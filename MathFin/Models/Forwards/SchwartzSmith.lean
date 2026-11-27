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
open scoped NNReal InnerProductSpace
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

/-! ### Sums of independent Gaussian variables -/

/-- **Sum of independent Gaussian variables**: with `X ~ N(m₁, v₁)`, `Y ~ N(m₂, v₂)`
independent, `X + Y ~ N(m₁ + m₂, v₁ + v₂)`. -/
private theorem hasLaw_add_of_indepFun {X Y : Ω → ℝ} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0}
    (hX : HasLaw X (gaussianReal m₁ v₁) μ) (hY : HasLaw Y (gaussianReal m₂ v₂) μ)
    (hind : IndepFun X Y μ) :
    HasLaw (fun ω ↦ X ω + Y ω) (gaussianReal (m₁ + m₂) (v₁ + v₂)) μ := by
  have hGX : HasGaussianLaw X μ := ⟨hX.aemeasurable, by rw [hX.map_eq]; infer_instance⟩
  have hGY : HasGaussianLaw Y μ := ⟨hY.aemeasurable, by rw [hY.map_eq]; infer_instance⟩
  have hG := iIndepFun.hasGaussianLaw_fun_add hGX hGY hind
  have hmemX : MemLp X 2 μ := hGX.memLp_two
  have hmemY : MemLp Y 2 μ := hGY.memLp_two
  have hmean : ∫ ω, (X ω + Y ω) ∂μ = m₁ + m₂ := by
    have hIX : Integrable X μ := hmemX.integrable one_le_two
    have hIY : Integrable Y μ := hmemY.integrable one_le_two
    rw [integral_add hIX hIY, hX.integral_eq.trans integral_id_gaussianReal,
      hY.integral_eq.trans integral_id_gaussianReal]
  have hvar : Var[fun ω ↦ X ω + Y ω; μ] = (v₁ + v₂ : ℝ) := by
    show Var[X + Y; μ] = _
    rw [IndepFun.variance_add hmemX hmemY hind, hX.variance_eq, variance_id_gaussianReal,
      hY.variance_eq, variance_id_gaussianReal]
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.isGaussian_map.eq_gaussianReal]
  have hid : (μ.map (fun ω ↦ X ω + Y ω))[id] = m₁ + m₂ := by
    rw [integral_map hG.aemeasurable aestronglyMeasurable_id]
    simpa using hmean
  have hvid : Var[id; μ.map (fun ω ↦ X ω + Y ω)] = (v₁ + v₂ : ℝ) := by
    rw [variance_map aemeasurable_id hG.aemeasurable]
    simpa using hvar
  rw [hid, hvid]
  simp

/-! ### The model -/

/-- **The short-term deviation** `χ_t` of the Schwartz–Smith model: the Ornstein–Uhlenbeck
integral `HullWhite.integratedRate` at zero forcing, with speed `κ`, volatility `σ_χ` and
initial value `χ₀`. -/
noncomputable def schwartzSmithChi (hB : IsPreBrownianReal B μ) (κ σ x₀ : ℝ) (hκ : 0 < κ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  HullWhite.integratedRate hB (fun _ ↦ 0) κ σ x₀ hκ t ω

/-- **The equilibrium level** `ξ_t` of the Schwartz–Smith model: the drifted Brownian motion
`ξ₀ + νt` with volatility `σ_ξ`, correlated with the `χ`-driver through `ρ`:
`ξ_t = ξ₀ + νt + ρσ_ξ B¹_t + √(1−ρ²) σ_ξ B²_t`, both Brownian values carried as Wiener
integrals of the whole-window indicator. For `ρ² > 1` the square root is junk; the
correlation constraint `ρ² ≤ 1` is a hypothesis of every theorem below. -/
noncomputable def schwartzSmithXi (hB₁ : IsPreBrownianReal B₁ μ) (hB₂ : IsPreBrownianReal B₂ μ)
    (ξ₀ ν ρ σ : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ξ₀ + ν * (t : ℝ)
    + ρ * σ * (wienerIntegralLp B₁ hB₁ t (stepIndicatorLp t (StepIndex.whole t))) ω
    + Real.sqrt (1 - ρ ^ 2) * σ
      * (wienerIntegralLp B₂ hB₂ t (stepIndicatorLp t (StepIndex.whole t))) ω

/-- **The log spot** of the Schwartz–Smith model: `ln S_t = χ_t + ξ_t`. -/
noncomputable def schwartzSmithLogSpot (hB₁ : IsPreBrownianReal B₁ μ)
    (hB₂ : IsPreBrownianReal B₂ μ) (κ σ₁ x₀ ξ₀ ν ρ σ₂ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) (ω : Ω) :
    ℝ :=
  schwartzSmithChi hB₁ κ σ₁ x₀ hκ t ω + schwartzSmithXi hB₁ hB₂ ξ₀ ν ρ σ₂ t ω

/-! ### The kernel integrals the variance formula needs -/

private lemma deterministic_zero_eq (κ x₀ : ℝ) (t : ℝ≥0) :
    HullWhite.deterministic (fun _ ↦ (0 : ℝ)) κ x₀ (t : ℝ) = x₀ * Real.exp (-(κ * (t : ℝ))) := by
  simp [HullWhite.deterministic, mul_comm]

private lemma integral_vasicekKernel_eq (κ : ℝ) (hκ : κ ≠ 0) (T : ℝ≥0) :
    ∫ s in Set.Ioc (0 : ℝ) ((T : ℝ)), vasicekKernel κ (T : ℝ) s ∂volume
      = (1 - Real.exp (-(κ * (T : ℝ)))) / κ := by
  rw [← intervalIntegral.integral_of_le T.coe_nonneg]
  have hd : ∀ u : ℝ, HasDerivAt (fun v ↦ Real.exp (-(κ * ((T : ℝ) - v))) / κ)
      (vasicekKernel κ (T : ℝ) u) u := by
    intro u
    have hh : HasDerivAt (fun v : ℝ ↦ (T : ℝ) - v) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (T : ℝ)
    have hmul : HasDerivAt (fun v : ℝ ↦ -((κ : ℝ) * ((T : ℝ) - v))) κ u := by
      simpa using hh.const_mul (-(κ : ℝ))
    have hexp := ((Real.hasDerivAt_exp _).comp u hmul).div_const κ
    rw [show ∀ x : ℝ, Real.exp x * κ / κ = Real.exp x from fun x ↦ by field_simp] at hexp
    rw [vasicekKernel]
    exact hexp
  have hinteg : IntervalIntegrable (vasicekKernel κ (T : ℝ)) volume 0 (T : ℝ) := by
    apply Continuous.intervalIntegrable
    unfold vasicekKernel
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x) hinteg]
  norm_num
  field_simp

/-- The quadratic form of the log-spot variance is nonnegative: the covariance matrix of
`(χ_t, ξ_t)` is positive semidefinite, which here rests on `2(1 − e^{−x})² ≤ x(1 − e^{−2x})`. -/
private lemma ssQuadratic_nonneg (a b : ℝ) {κ σ₁ σ₂ ρ : ℝ} {t : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t)
    (hρ : ρ ^ 2 ≤ 1) :
    0 ≤ a ^ 2 * vasicekSDEVariance σ₁ κ t
      + 2 * (a * b) * (ρ * σ₁ * σ₂ * (1 - Real.exp (-(κ * t))) / κ) + b ^ 2 * σ₂ ^ 2 * t := by
  by_cases hσ₂ : σ₂ = 0
  · subst hσ₂
    simp
    exact mul_nonneg (sq_nonneg a) (vasicekSDEVariance_nonneg σ₁ hκ ht)
  by_cases ht0 : t = 0
  · subst ht0
    simp
    exact mul_nonneg (sq_nonneg a) (vasicekSDEVariance_nonneg σ₁ hκ ht)
  have hx : 0 < κ * t := by positivity
  -- the core inequality `2(1 − e^{−x})² ≤ x(1 − e^{−2x})`
  have hcore : 2 * (1 - Real.exp (-(κ * t))) ^ 2
      ≤ (κ * t) * (1 - Real.exp (-(2 * (κ * t)))) := by
    have he2 : Real.exp (-(2 * (κ * t))) = Real.exp (-(κ * t)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he2]
    have hsle : 0 ≤ 1 - Real.exp (-(κ * t)) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
    have hgs : 2 ≤ (κ * t) * (1 + Real.exp (-(κ * t))) + 2 * Real.exp (-(κ * t)) := by
      have hg' : ∀ u : ℝ, HasDerivAt
          (fun v ↦ v * (1 + Real.exp (-v)) + 2 * Real.exp (-v))
          (1 * (1 + Real.exp (-u)) + u * (0 + (-Real.exp (-u))) + 2 * (-Real.exp (-u))) u := by
        intro u
        have hexp : HasDerivAt (fun v : ℝ ↦ Real.exp (-v)) (-Real.exp (-u)) u := by
          simpa using (hasDerivAt_id u).neg.exp
        have hadd : HasDerivAt (fun v : ℝ ↦ 1 + Real.exp (-v))
            (0 + (-Real.exp (-u))) u := (hasDerivAt_const u (1 : ℝ)).add hexp
        have h1 : HasDerivAt (fun v : ℝ ↦ v * (1 + Real.exp (-v)))
            (1 * (1 + Real.exp (-u)) + u * (0 + (-Real.exp (-u)))) u :=
          (hasDerivAt_id u).mul hadd
        have h2 : HasDerivAt (fun v : ℝ ↦ 2 * Real.exp (-v))
            (2 * (-Real.exp (-u))) u := hexp.const_mul 2
        have h := h1.add h2
        have hfun : ((fun v : ℝ ↦ v * (1 + Real.exp (-v))) + fun v : ℝ ↦ 2 * Real.exp (-v))
            = fun v : ℝ ↦ v * (1 + Real.exp (-v)) + 2 * Real.exp (-v) := rfl
        rw [hfun] at h
        exact h
      have hng : ∀ u : ℝ, 0 ≤ 1 - (1 + u) * Real.exp (-u) := by
        intro u
        have hle : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
        have hs' : 0 < Real.exp (-u) := Real.exp_pos _
        have heq : Real.exp u * Real.exp (-u) = 1 := by
          rw [← Real.exp_add]
          norm_num
        nlinarith [hle, hs', heq]
      have hinteg : IntervalIntegrable
          (fun u : ℝ ↦ 1 * (1 + Real.exp (-u)) + u * (0 + (-Real.exp (-u)))
            + 2 * (-Real.exp (-u))) volume 0 (κ * t) := by
        apply Continuous.intervalIntegrable
        fun_prop
      have hng2 : ∀ u : ℝ,
          0 ≤ 1 * (1 + Real.exp (-u)) + u * (0 + (-Real.exp (-u))) + 2 * (-Real.exp (-u)) := by
        intro u
        rw [show (1 * (1 + Real.exp (-u)) + u * (0 + (-Real.exp (-u)))
              + 2 * (-Real.exp (-u)))
            = 1 - (1 + u) * Real.exp (-u) from by ring]
        exact hng u
      have hint := intervalIntegral.integral_nonneg (μ := volume) hx.le (fun u _ ↦ hng2 u)
      have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ ↦ hg' u) hinteg
      have h0 : (0 : ℝ) * (1 + Real.exp (-(0 : ℝ))) + 2 * Real.exp (-(0 : ℝ)) = 2 := by
        norm_num
      rw [h0] at hsub
      nlinarith [hint, hsub]
    have hsplit : (κ * t) * (1 - Real.exp (-(κ * t)) ^ 2)
          - 2 * (1 - Real.exp (-(κ * t))) ^ 2
        = (1 - Real.exp (-(κ * t)))
          * ((κ * t) * (1 + Real.exp (-(κ * t))) - 2 * (1 - Real.exp (-(κ * t)))) := by
      ring
    have hp2 : 0 ≤ (1 - Real.exp (-(κ * t)))
        * ((κ * t) * (1 + Real.exp (-(κ * t))) - 2 * (1 - Real.exp (-(κ * t)))) :=
      mul_nonneg hsle (by linarith)
    calc 2 * (1 - Real.exp (-(κ * t))) ^ 2
        ≤ 2 * (1 - Real.exp (-(κ * t))) ^ 2
          + (1 - Real.exp (-(κ * t)))
            * ((κ * t) * (1 + Real.exp (-(κ * t)))
              - 2 * (1 - Real.exp (-(κ * t)))) := by linarith
      _ = (κ * t) * (1 - Real.exp (-(κ * t)) ^ 2) := by rw [← hsplit]; ring
  -- the bracket `κt·F − 2ρ²E²` is nonnegative
  have hbr : 0 ≤ (κ * t) * (1 - Real.exp (-(2 * (κ * t))))
      - ρ ^ 2 * (2 * (1 - Real.exp (-(κ * t))) ^ 2) := by
    have h1 : ρ ^ 2 * (1 - Real.exp (-(κ * t))) ^ 2
        ≤ (1 - Real.exp (-(κ * t))) ^ 2 := by
      nlinarith [sq_nonneg (1 - Real.exp (-(κ * t)))]
    nlinarith [hcore, h1, hx]
  -- the completed square: multiply the quadratic by `2 * κ ^ 2 * t` (positive here)
  have hκ2t : 0 < 2 * κ ^ 2 * t := by positivity
  have hsq : 0 ≤ (b * (σ₂ * (κ * t))
      + a * (ρ * σ₁ * (1 - Real.exp (-(κ * t))))) ^ 2 :=
    sq_nonneg _
  have hident : 2 * κ ^ 2 * t * (a ^ 2 * vasicekSDEVariance σ₁ κ t
      + 2 * (a * b) * (ρ * σ₁ * σ₂ * (1 - Real.exp (-(κ * t))) / κ) + b ^ 2 * σ₂ ^ 2 * t)
      = 2 * (b * (σ₂ * (κ * t)) + a * (ρ * σ₁ * (1 - Real.exp (-(κ * t))))) ^ 2
        + a ^ 2 * σ₁ ^ 2 * ((κ * t) * (1 - Real.exp (-(2 * (κ * t))))
          - ρ ^ 2 * (2 * (1 - Real.exp (-(κ * t))) ^ 2)) := by
    unfold vasicekSDEVariance
    field_simp
    ring
  refine le_of_mul_le_mul_right ?_ hκ2t
  rw [zero_mul, mul_comm (a ^ 2 * vasicekSDEVariance σ₁ κ t
      + 2 * (a * b) * (ρ * σ₁ * σ₂ * (1 - Real.exp (-(κ * t))) / κ)
      + b ^ 2 * σ₂ ^ 2 * t) (2 * κ ^ 2 * t), hident]
  nlinarith [hsq, hbr, mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg σ₁)) hbr,
    sq_nonneg a, sq_nonneg σ₁]

private lemma norm_vasicekKernelLp_sq (κ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) :
    ‖(vasicekKernelLp κ hκ.le t : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) ((t : ℝ)))))‖ ^ 2
      = vasicekSDEVariance 1 κ (t : ℝ) := by
  rw [lp_two_norm_sq, vasicekKernelLp,
    MemLp.integral_sq_toLp (vasicekKernel_memLp κ hκ.le t),
    vasicekKernel_integral_sq κ hκ.ne' t]
  unfold vasicekSDEVariance
  ring

private lemma inner_kernel_stepIndicator (κ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) :
    ⟪vasicekKernelLp κ hκ.le t, stepIndicatorLp t (StepIndex.whole t)⟫_ℝ
      = (1 - Real.exp (-(κ * (t : ℝ)))) / κ := by
  rw [real_inner_comm, inner_stepIndicatorLp_whole, vasicekKernelLp,
    MeasureTheory.integral_congr_ae (MemLp.coeFn_toLp (vasicekKernel_memLp κ hκ.le t))]
  exact integral_vasicekKernel_eq κ hκ.ne' t

/-- **Linear combinations of the two factors are Gaussian.** For every `a b`, the variable
`a·χ_t + b·ξ_t` is Gaussian with mean `a·χ₀e^{−κt} + b·(ξ₀ + νt)` and variance
`a²·v_χ + 2ab·cov + b²·v_ξ`, where `v_χ = vasicekSDEVariance σ_χ κ t`, `v_ξ = σ_ξ²t` and
`cov = ρσ_χσ_ξ(1−e^{−κt})/κ` — the independence of the two motions feeding the
`√(1−ρ²)`-leg and the Vasicek isometry feeding the rest. -/
private theorem hasLaw_linearCombination (hB₁ : IsPreBrownianReal B₁ μ)
    (hB₂ : IsPreBrownianReal B₂ μ) (h₁m : ∀ s, Measurable (B₁ s)) (h₂m : ∀ s, Measurable (B₂ s))
    (hind : IndepFun (fun ω s ↦ B₁ s ω) (fun ω s ↦ B₂ s ω) μ)
    {κ σ₁ σ₂ x₀ ξ₀ ν ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ^ 2 ≤ 1) (t : ℝ≥0) (a b : ℝ) :
    HasLaw (fun ω ↦ a * schwartzSmithChi hB₁ κ σ₁ x₀ hκ t ω
        + b * schwartzSmithXi hB₁ hB₂ ξ₀ ν ρ σ₂ t ω)
      (gaussianReal
        (a * (x₀ * Real.exp (-(κ * (t : ℝ)))) + b * (ξ₀ + ν * (t : ℝ)))
        ((a ^ 2 * vasicekSDEVariance σ₁ κ (t : ℝ)
            + 2 * (a * b) * (ρ * σ₁ * σ₂ * (1 - Real.exp (-(κ * (t : ℝ)))) / κ)
            + b ^ 2 * σ₂ ^ 2 * (t : ℝ)).toNNReal)) μ := by
  set k : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) ((t : ℝ)))) :=
    vasicekKernelLp κ hκ.le t with hkeq
  set w : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) ((t : ℝ)))) :=
    stepIndicatorLp t (StepIndex.whole t) with hweq
  set A : ℝ := a * σ₁ with hA
  set Bc : ℝ := b * ρ * σ₂ with hBc
  set C : ℝ := b * Real.sqrt (1 - ρ ^ 2) * σ₂ with hC
  set c₀ : ℝ := a * (x₀ * Real.exp (-(κ * (t : ℝ)))) + b * (ξ₀ + ν * (t : ℝ)) with hc₀
  have hk2 : ‖k‖ ^ 2 = vasicekSDEVariance 1 κ (t : ℝ) := by
    rw [hkeq]; exact norm_vasicekKernelLp_sq κ hκ t
  have hkw : ⟪k, w⟫_ℝ = (1 - Real.exp (-(κ * (t : ℝ)))) / κ := by
    rw [hkeq, hweq]; exact inner_kernel_stepIndicator κ hκ t
  have hw2 : ‖w‖ ^ 2 = (t : ℝ) := by rw [hweq]; exact norm_stepIndicatorLp_whole_sq t
  have hu : ‖A • k + Bc • w‖ ^ 2
      = A ^ 2 * ‖k‖ ^ 2 + 2 * (A * Bc) * ⟪k, w⟫_ℝ + Bc ^ 2 * ‖w‖ ^ 2 :=
    norm_smul_add_smul_sq_real A Bc k w
  have hintu : ∫ s in Set.Ioc (0 : ℝ) ((t : ℝ)), ((A • k + Bc • w) s) ^ 2 ∂volume
      = A ^ 2 * vasicekSDEVariance 1 κ (t : ℝ)
        + 2 * (A * Bc) * ((1 - Real.exp (-(κ * (t : ℝ)))) / κ) + Bc ^ 2 * (t : ℝ) := by
    rw [← lp_two_norm_sq, hu, hk2, hkw, hw2]
  have hIu := wienerIntegralLp_hasLaw_gaussian_of_integral_sq hB₁ t (A • k + Bc • w) hintu
  have hintv : ∫ s in Set.Ioc (0 : ℝ) ((t : ℝ)), ((C • w) s) ^ 2 ∂volume = C ^ 2 * (t : ℝ) := by
    rw [← lp_two_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hw2]
  have hIv := wienerIntegralLp_hasLaw_gaussian_of_integral_sq hB₂ t (C • w) hintv
  have hinds := indepFun_wienerIntegral_of_indepFun hB₁ hB₂ h₁m h₂m hind t (A • k + Bc • w) (C • w)
  have hsum := hasLaw_add_of_indepFun hIu hIv hinds
  have hshift := gaussianReal_const_add hsum c₀
  have hae : (fun ω ↦ a * schwartzSmithChi hB₁ κ σ₁ x₀ hκ t ω
      + b * schwartzSmithXi hB₁ hB₂ ξ₀ ν ρ σ₂ t ω)
      =ᵐ[μ] (fun ω ↦ c₀ + ((wienerIntegralLp B₁ hB₁ t (A • k + Bc • w)) ω
        + (wienerIntegralLp B₂ hB₂ t (C • w)) ω)) := by
    filter_upwards [wienerIntegralLp_smul_add_smul_ae hB₁ t A Bc k w,
      wienerIntegralLp_smul_ae hB₂ t C w] with ω h1 h2
    have hchi : schwartzSmithChi hB₁ κ σ₁ x₀ hκ t ω
        = x₀ * Real.exp (-(κ * (t : ℝ))) + σ₁ * (wienerIntegralLp B₁ hB₁ t k) ω := by
      rw [schwartzSmithChi, HullWhite.integratedRate, deterministic_zero_eq]
    rw [hchi, hkeq]
    simp only [schwartzSmithXi, hweq]
    rw [h1, h2]
    ring
  have hℓ : gaussianReal ((0 : ℝ) + 0 + c₀)
      (((A ^ 2 * vasicekSDEVariance 1 κ (t : ℝ)
          + 2 * (A * Bc) * ((1 - Real.exp (-(κ * (t : ℝ)))) / κ) + Bc ^ 2 * (t : ℝ)).toNNReal
        + (C ^ 2 * (t : ℝ)).toNNReal : ℝ≥0))
      = gaussianReal c₀
        ((a ^ 2 * vasicekSDEVariance σ₁ κ (t : ℝ)
          + 2 * (a * b) * (ρ * σ₁ * σ₂ * (1 - Real.exp (-(κ * (t : ℝ)))) / κ)
          + b ^ 2 * σ₂ ^ 2 * (t : ℝ)).toNNReal) := by
    refine congr (congrArg gaussianReal
      (show ((0 : ℝ) + 0 + c₀) = c₀ from by norm_num)) (NNReal.eq ?_)
    rw [NNReal.coe_add]
    rw [Real.coe_toNNReal
      (A ^ 2 * vasicekSDEVariance 1 κ (t : ℝ)
        + 2 * (A * Bc) * ((1 - Real.exp (-(κ * (t : ℝ)))) / κ) + Bc ^ 2 * (t : ℝ))
      (by
        have h := ssQuadratic_nonneg A Bc (σ₁ := 1) (σ₂ := 1) (ρ := 1) hκ t.coe_nonneg
          (by norm_num : (1 : ℝ) ^ 2 ≤ 1)
        simpa using h)]
    rw [Real.coe_toNNReal (C ^ 2 * (t : ℝ)) (mul_nonneg (sq_nonneg C) t.coe_nonneg)]
    rw [Real.coe_toNNReal
      (a ^ 2 * vasicekSDEVariance σ₁ κ (t : ℝ)
        + 2 * (a * b) * (ρ * σ₁ * σ₂ * (1 - Real.exp (-(κ * (t : ℝ)))) / κ)
        + b ^ 2 * σ₂ ^ 2 * (t : ℝ)) (ssQuadratic_nonneg a b hκ t.coe_nonneg hρ)]
    simp only [hA, hBc, hC, vasicekSDEVariance]
    rw [show (b * Real.sqrt (1 - ρ ^ 2) * σ₂) ^ 2
        = b ^ 2 * (1 - ρ ^ 2) * σ₂ ^ 2 from by
      rw [mul_pow, mul_pow, Real.sq_sqrt (sub_nonneg.mpr hρ : (0 : ℝ) ≤ 1 - ρ ^ 2)]]
    field_simp
    ring
  rw [← hℓ]
  exact hshift.congr hae

end MathFin
