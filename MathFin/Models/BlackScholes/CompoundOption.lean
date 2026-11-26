/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Probability.Gaussian.GaussianPairLinearLaw
public import MathFin.Probability.Gaussian.NormalQuantile
public import MathFin.Models.BlackScholes.Put
public import MathFin.Models.BlackScholes.PutGreeks
public import MathFin.Probability.Gaussian.BivariateNormalCDF

/-!
# Compound options on non-flat curves: the reduction behind Geske's formula

An option on an option (compound maturity `Tm`, underlying-option maturity `Td > Tm`) under
deterministic rate, dividend and total-variance curves. Write `Dr`, `Dq` for the discount and
dividend factors and `V` for the total variance. The reduction needs only the forward
quantities `DrF = Dr(Td)/Dr(Tm)`, `DqF = Dq(Td)/Dq(Tm)` and `VF = V(Td) - V(Tm) > 0`.
Source: after Haug, *The Complete Guide to Option Pricing Formulas*, 2nd ed. (2007), ch. 4,
"Options on Options".

## Main definitions

* `compoundCorrelation` — `ρ = √(V(Tm)/V(Td))`.
* `daughterPut` — the daughter put's value at `Tm` as a function of spot `S`: the Black-Scholes
  put with forward discount `DrF`, forward factor `S·DqF/DrF` and standard deviation `√VF`.

## Main results

* `compoundCovariance_eq` and `compoundCorrelation_eq` — for independent standard normals
  `Z, Z'`, the nested-horizon drivers `G_m = √V(Tm)·Z` and `G_d = G_m + √(V(Td)-V(Tm))·Z'` have
  `Var G_m = V(Tm)`, `Var G_d = V(Td)`, `cov(G_m, G_d) = V(Tm)`, so their correlation is `ρ`;
  `cov(Z, G_d/√V(Td)) = ρ` for the standardized variables; `0 < ρ < 1` for `V(Tm) > 0`, `ρ² = V(Tm)/V(Td)`.
  Haug prints the flat-parameter case `ρ = √(t₁/T₂)`, which is `compoundCorrelation_flat`; the
  curve version `ρ = √(V(Tm)/V(Td))` is its generalisation.
* `compound_joint` — the joint law of `(Z, G_d/√V(Td))` is bivariate normal: the probability of
  `{Z ≤ a, G_d/√V(Td) ≤ b}` is `bivariateNormalCDF a b ρ`.
* `daughterPut_eq_bsP` — `daughterPut` is the library's `bsP` at spot `S·DqF`, rate `-log DrF`,
  volatility `√VF` and unit time; `daughterPut_eq_integral` — it is the discounted expectation of
  the put payoff over a lognormal forward step.
* `daughterPut_lt_strike` — the daughter put value is below `Kd·DrF` for every `S > 0`;
  `daughterPut_strictAntiOn` — it is strictly decreasing in the spot on `(0, ∞)` for `VF > 0`;
  `daughterPut_integrable` — it is integrable along any measurable positive spot.
* `compound_put_payoff_eq`, `compound_call_payoff_eq_zero` — for `Km ≥ Kd·DrF` the call-on-put
  payoff is identically `0` and the put-on-put payoff is `Km - daughterPut` pointwise.
* `compound_put_value` — for `Km ≥ Kd·DrF` the time-0 put-on-put value is `Km·Dr(Tm)` minus the
  daughter put's time-0 price, with the tower property `price₀ = Dr(Tm)·𝔼[daughterPut(S_Tm)]`
  as the only hypothesis (integrability is proved); `compound_call_value_eq_zero` — the
  call-on-put has value zero in that case.

## Not derived

Geske's closed form (the integral of the daughter value over the critical-spot region, giving
bivariate-normal CDFs), the existence and uniqueness of the critical spot for `Km < Kd·DrF`, and
the tower property itself (a hypothesis of `compound_put_value`).

## References

* [Haug, *The Complete Guide to Option Pricing Formulas*][Haug2007], 2nd ed. (2007), ch. 4,
  "Options on Options".

## Tags

compound option, option on option, Geske, bivariate normal, time-dependent correlation,
Black-Scholes, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- Time-dependent correlation `ρ = √(V(Tm)/V(Td))` between the standardized `Tm`- and
`Td`-horizon Gaussian drivers. -/
noncomputable def compoundCorrelation (Vm Vd : ℝ) : ℝ := √(Vm / Vd)

/-- `d₁` of the daughter put at time `Tm`, in forward quantities. -/
noncomputable def daughterD1 (S K DrF DqF VF : ℝ) : ℝ :=
  (Real.log (S * DqF / (K * DrF)) + VF / 2) / √VF

/-- The daughter put's value at `Tm` as a function of spot `S`:
`Kd·DrF·Φ(-d₂) - S·DqF·Φ(-d₁)`. -/
noncomputable def daughterPut (S K DrF DqF VF : ℝ) : ℝ :=
  K * DrF * Phi (-(daughterD1 S K DrF DqF VF - √VF)) - S * DqF * Phi (-daughterD1 S K DrF DqF VF)

section CorrelationMoments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
private lemma var_one {Z : Ω → ℝ} (h : HasLaw Z (gaussianReal 0 1) P) : Var[Z; P] = 1 := by
  rw [h.variance_eq, variance_id_gaussianReal, NNReal.coe_one]

/-- **moments of the nested drivers.** For independent standard normals `Z, Z'` and
`0 ≤ Vm ≤ Vd`, with `G_m = √Vm·Z` and `G_d = √Vm·Z + √(Vd-Vm)·Z'`:
`Var G_m = Vm`, `Var G_d = Vd`, `cov(G_m, G_d) = Vm`. -/
theorem compoundCovariance_eq {Z Z' : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P)
    (hZ' : HasLaw Z' (gaussianReal 0 1) P) (hind : IndepFun Z Z' P) {Vm Vd : ℝ}
    (hm : 0 ≤ Vm) (hd : Vm ≤ Vd) :
    Var[fun ω ↦ √Vm * Z ω; P] = Vm ∧
    Var[fun ω ↦ √Vm * Z ω + √(Vd - Vm) * Z' ω; P] = Vd ∧
    cov[fun ω ↦ √Vm * Z ω, fun ω ↦ √Vm * Z ω + √(Vd - Vm) * Z' ω; P] = Vm := by
  have h2 := hZ.hasGaussianLaw.memLp_two
  have h2' := hZ'.hasGaussianLaw.memLp_two
  have hc : cov[Z, Z'; P] = 0 := hind.covariance_eq_zero h2 h2'
  have s1 := Real.sq_sqrt hm
  have s2 := Real.sq_sqrt (sub_nonneg.2 hd)
  refine ⟨?_, ?_, ?_⟩
  · rw [variance_const_mul, var_one hZ]; nlinarith
  · rw [variance_linear_of_unit h2 h2' (var_one hZ) (var_one hZ') hc]; nlinarith
  · rw [covariance_const_mul_left]
    change √Vm * cov[Z, (fun ω ↦ √Vm * Z ω) + fun ω ↦ √(Vd - Vm) * Z' ω; P] = Vm
    rw [covariance_add_right h2 (h2.const_mul _) (h2'.const_mul _),
      covariance_const_mul_right, covariance_const_mul_right, covariance_self h2.aemeasurable,
      var_one hZ, hc]
    nlinarith

/-- **the correlation of the standardized variables is `ρ = √(Vm/Vd)`.** With `Vd > 0`,
`cov(Z, G_d/√Vd) = ρ` and `Var(G_d/√Vd) = 1`. -/
theorem compoundCorrelation_eq {Z Z' : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P)
    (hZ' : HasLaw Z' (gaussianReal 0 1) P) (hind : IndepFun Z Z' P) {Vm Vd : ℝ}
    (hm : 0 ≤ Vm) (hd : Vm < Vd) :
    Var[fun ω ↦ (√Vm / √Vd) * Z ω + (√(Vd - Vm) / √Vd) * Z' ω; P] = 1 ∧
    cov[Z, fun ω ↦ (√Vm / √Vd) * Z ω + (√(Vd - Vm) / √Vd) * Z' ω; P]
      = compoundCorrelation Vm Vd := by
  have h2 := hZ.hasGaussianLaw.memLp_two
  have h2' := hZ'.hasGaussianLaw.memLp_two
  have hc : cov[Z, Z'; P] = 0 := hind.covariance_eq_zero h2 h2'
  have hVd : 0 < Vd := lt_of_le_of_lt hm hd
  have s1 := Real.sq_sqrt hm
  have s2 := Real.sq_sqrt (sub_nonneg.2 hd.le)
  have s3 := Real.sq_sqrt hVd.le
  have hs3 : 0 < √Vd := Real.sqrt_pos.2 hVd
  refine ⟨?_, ?_⟩
  · rw [variance_linear_of_unit h2 h2' (var_one hZ) (var_one hZ') hc, div_pow, div_pow, s1, s2, s3]
    field_simp; ring
  · have := covariance_linear_of_unit h2 h2' (var_one hZ) (var_one hZ') hc 1 0 (√Vm / √Vd)
      (√(Vd - Vm) / √Vd)
    simp only [one_mul, zero_mul, add_zero, mul_zero] at this
    rw [this, compoundCorrelation, Real.sqrt_div hm]

omit [IsProbabilityMeasure P] in
/-- **shape of `ρ`.** `0 < ρ < 1` for `0 < Vm < Vd`. -/
theorem compoundCorrelation_mem_Ioo {Vm Vd : ℝ} (hm : 0 < Vm) (hd : Vm < Vd) :
    0 < compoundCorrelation Vm Vd ∧ compoundCorrelation Vm Vd < 1 := by
  have hVd : 0 < Vd := hm.trans hd
  unfold compoundCorrelation
  refine ⟨Real.sqrt_pos.2 (div_pos hm hVd), ?_⟩
  rw [Real.sqrt_lt' one_pos, one_pow]
  exact (div_lt_one hVd).2 hd

omit [IsProbabilityMeasure P] in
/-- **`ρ² = V(Tm)/V(Td)`.** -/
theorem compoundCorrelation_sq {Vm Vd : ℝ} (hm : 0 ≤ Vm) (hd : 0 < Vd) :
    compoundCorrelation Vm Vd ^ 2 = Vm / Vd :=
  Real.sq_sqrt (div_nonneg hm hd.le)

omit [IsProbabilityMeasure P] in
/-- **flat volatility.** `V(t) = σ²t` gives `ρ = √(Tm/Td)`, the flat-parameter case Haug prints. -/
theorem compoundCorrelation_flat {σ Tm Td : ℝ} (hσ : σ ≠ 0) :
    compoundCorrelation (σ ^ 2 * Tm) (σ ^ 2 * Td) = √(Tm / Td) := by
  unfold compoundCorrelation
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hσ)]

/-- **Joint law of the standardized drivers.** For independent standard normals `Z, Z'` and
`0 ≤ Vm < Vd`, `P{Z ≤ a, (√Vm/√Vd)·Z + (√(Vd-Vm)/√Vd)·Z' ≤ b} = N₂(a, b; ρ)` with
`ρ = compoundCorrelation Vm Vd`. -/
theorem compound_joint {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {Z Z' : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P)
    (hZ' : HasLaw Z' (gaussianReal 0 1) P) (hind : IndepFun Z Z' P) {Vm Vd : ℝ}
    (hm : 0 ≤ Vm) (hd : Vm < Vd) (a b : ℝ) :
    P.real {ω | Z ω ≤ a ∧ (√Vm / √Vd) * Z ω + (√(Vd - Vm) / √Vd) * Z' ω ≤ b}
      = bivariateNormalCDF a b (compoundCorrelation Vm Vd) := by
  have hj : HasGaussianLaw (fun ω ↦ (Z ω, Z' ω)) P :=
    hind.hasGaussianLaw hZ.hasGaussianLaw hZ'.hasGaussianLaw
  have hc : cov[Z, Z'; P] = 0 :=
    hind.covariance_eq_zero hZ.hasGaussianLaw.memLp_two hZ'.hasGaussianLaw.memLp_two
  obtain ⟨hvar, hcov⟩ := compoundCorrelation_eq hZ hZ' hind hm hd
  set G := fun ω ↦ (√Vm / √Vd) * Z ω + (√(Vd - Vm) / √Vd) * Z' ω with hG
  have hGlaw : HasLaw G (gaussianReal 0 1) P := by
    have h := hasLaw_linear_gaussianPair hj hZ hZ' hc (√Vm / √Vd) (√(Vd - Vm) / √Vd)
    have hv := variance_linear_of_unit hZ.hasGaussianLaw.memLp_two hZ'.hasGaussianLaw.memLp_two
      (by rw [hZ.variance_eq, variance_id_gaussianReal, NNReal.coe_one])
      (by rw [hZ'.variance_eq, variance_id_gaussianReal, NNReal.coe_one]) hc
      (√Vm / √Vd) (√(Vd - Vm) / √Vd)
    rw [← hv, hvar, Real.toNNReal_one] at h
    exact h
  have hpair : HasGaussianLaw (fun ω ↦ (Z ω, G ω)) P := by
    simpa only [ContinuousLinearMap.prod_apply, add_apply,
      smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul] using
      hj.map_fun ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((√Vm / √Vd) • ContinuousLinearMap.fst ℝ ℝ ℝ
          + (√(Vd - Vm) / √Vd) • ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hlaw := hasLaw_bivariateNormalLaw_of_gaussianPair hpair hZ hGlaw hcov
  rw [bivariateNormalCDF_eq_law, ← hlaw.map_eq, Measure.real, Measure.real,
    Measure.map_apply_of_aemeasurable hlaw.aemeasurable (measurableSet_Iic.prod measurableSet_Iic)]
  rfl

end CorrelationMoments

/-- Daughter underlying at `Td` given the spot `S` at `Tm`: forward `S·DqF/DrF` times a
lognormal step with variance `VF`. -/
noncomputable def daughterTerminal (S DrF DqF VF z : ℝ) : ℝ :=
  S * DqF / DrF * Real.exp (-VF / 2 + √VF * z)

private lemma daughterD1_eq {S K DrF DqF VF : ℝ} (hSq : 0 < S * DqF) (hK : 0 < K)
    (hDr : 0 < DrF) :
    bsd1 (S * DqF) K (-Real.log DrF) (√VF) 1 = daughterD1 S K DrF DqF VF := by
  unfold bsd1 daughterD1
  rw [Real.log_div hSq.ne' (mul_pos hK hDr).ne', Real.log_mul hK.ne' hDr.ne',
    Real.log_div hSq.ne' hK.ne']
  by_cases hV : 0 ≤ VF
  · rw [Real.sq_sqrt hV]; simp only [Real.sqrt_one, mul_one]; ring_nf
  · simp [Real.sqrt_eq_zero_of_nonpos (not_le.1 hV).le]

/-- **The daughter put is the library's Black-Scholes put.** `daughterPut` equals `bsP` at spot
`S·DqF`, rate `-log DrF`, volatility `√VF` and unit time. -/
theorem daughterPut_eq_bsP {S K DrF DqF VF : ℝ} (hS : 0 < S) (hK : 0 < K) (hDr : 0 < DrF)
    (hDq : 0 < DqF) :
    daughterPut S K DrF DqF VF = bsP K (-Real.log DrF) (√VF) (S * DqF) 1 := by
  unfold daughterPut bsP bsd2
  rw [← daughterD1_eq (mul_pos hS hDq) hK hDr, Real.sqrt_one, mul_one, mul_one, neg_neg,
    Real.exp_log hDr]

/-- **The daughter put value is a Black-Scholes expectation.** For `S, K, DrF, DqF, VF > 0` and
`Z ~ N(0,1)`, `DrF·𝔼[(K - S_Td)⁺] = daughterPut`, with `S_Td` the lognormal forward step
`daughterTerminal`. Via `bs_put_formula` with spot `S·DqF`, rate `-log DrF`, volatility `√VF`
and unit time. -/
theorem daughterPut_eq_integral {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P)
    {S K DrF DqF VF : ℝ} (hS : 0 < S) (hK : 0 < K) (hDr : 0 < DrF) (hDq : 0 < DqF)
    (hV : 0 < VF) :
    ∫ ω, DrF * max (K - daughterTerminal S DrF DqF VF (Z ω)) 0 ∂P
      = daughterPut S K DrF DqF VF := by
  have hSq : 0 < S * DqF := mul_pos hS hDq
  have hσ : 0 < √VF := Real.sqrt_pos.2 hV
  have h := bs_put_formula (S_0 := S * DqF) (K := K) (r := -Real.log DrF) (σ := √VF) (T := 1)
    (Z := Z) (Q := P) ⟨hSq, hK, hσ, one_pos, hZ⟩
  have e1 : Real.exp (-(-Real.log DrF) * 1) = DrF := by
    rw [neg_neg, mul_one, Real.exp_log hDr]
  have e2 : ∀ z, bsTerminal (S * DqF) (-Real.log DrF) (√VF) 1 z
      = daughterTerminal S DrF DqF VF z := by
    intro z
    unfold bsTerminal daughterTerminal
    rw [Real.sq_sqrt hV.le, Real.sqrt_one]
    have : Real.exp ((-Real.log DrF - VF / 2) * 1 + √VF * 1 * z)
        = DrF⁻¹ * Real.exp (-VF / 2 + √VF * z) := by
      rw [← Real.exp_log (inv_pos.2 hDr), Real.log_inv, ← Real.exp_add]
      ring_nf
    rw [this]; field_simp
  simp only [e1, e2] at h
  rw [h, bsd2, daughterD1_eq hSq hK hDr, Real.sqrt_one, mul_one, daughterPut]

/-- **No-root bound.** The daughter put is strictly below `Kd·DrF` at every spot `S > 0`:
`Kd·DrF·Φ(-d₂) < Kd·DrF` (as `Φ < 1`) and `S·DqF·Φ(-d₁) > 0`. -/
theorem daughterPut_lt_strike {S K DrF DqF VF : ℝ} (hS : 0 < S) (hK : 0 < K) (hDr : 0 < DrF)
    (hDq : 0 < DqF) : daughterPut S K DrF DqF VF < K * DrF := by
  unfold daughterPut
  have h1 := (Phi_mem_Ioo (-(daughterD1 S K DrF DqF VF - √VF))).2
  have h2 := Phi_pos (-daughterD1 S K DrF DqF VF)
  have hKD : 0 < K * DrF := mul_pos hK hDr
  have : 0 < S * DqF * Phi (-daughterD1 S K DrF DqF VF) := mul_pos (mul_pos hS hDq) h2
  nlinarith [mul_lt_mul_of_pos_left h1 hKD]

/-- **Strict monotonicity in spot.** For `VF > 0` the daughter put value is strictly decreasing
in the spot on `(0, ∞)`; its derivative is the put delta `(Φ(d₁) - 1)·DqF < 0`. -/
theorem daughterPut_strictAntiOn {K DrF DqF VF : ℝ} (hK : 0 < K) (hDr : 0 < DrF)
    (hDq : 0 < DqF) (hV : 0 < VF) :
    StrictAntiOn (fun S ↦ daughterPut S K DrF DqF VF) (Set.Ioi 0) := by
  have hσ : 0 < √VF := Real.sqrt_pos.2 hV
  have hd : ∀ S ∈ Set.Ioi (0:ℝ), HasDerivAt (fun s ↦ daughterPut s K DrF DqF VF)
      ((Phi (bsd1 (S * DqF) K (-Real.log DrF) (√VF) 1) - 1) * DqF) S := by
    intro S hS
    have h1 := hasDerivAt_bsP_S (r := -Real.log DrF) hK hσ (mul_pos hS hDq) one_pos
    have h2 : HasDerivAt (fun s : ℝ ↦ s * DqF) DqF S := by
      simpa using (hasDerivAt_id S).mul_const DqF
    refine (HasDerivAt.comp S h1 h2).congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hS] with s hs
    exact daughterPut_eq_bsP hs hK hDr hDq
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun S hS ↦ (hd S hS).continuousAt.continuousWithinAt
  · intro S hS
    rw [interior_Ioi] at hS
    rw [(hd S hS).deriv]
    exact mul_neg_of_neg_of_pos (sub_neg.2 (Phi_mem_Ioo _).2) hDq

/-- **Integrability.** For a measurable positive spot `Sm` and `VF > 0`, `daughterPut(Sm)` is
integrable: it is measurable and lies in `[0, Kd·DrF)`. -/
theorem daughterPut_integrable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {Sm : Ω → ℝ} {K DrF DqF VF : ℝ}
    (hSm : ∀ ω, 0 < Sm ω) (hmeas : Measurable Sm) (hK : 0 < K) (hDr : 0 < DrF) (hDq : 0 < DqF)
    (hV : 0 < VF) : Integrable (fun ω ↦ daughterPut (Sm ω) K DrF DqF VF) P := by
  have hPhi : Measurable Phi := continuous_Phi.measurable
  have hm : Measurable (fun ω ↦ daughterPut (Sm ω) K DrF DqF VF) := by
    unfold daughterPut daughterD1; fun_prop
  refine Integrable.mono' (integrable_const (K * DrF)) hm.aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hZ : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have h0 : 0 ≤ daughterPut (Sm ω) K DrF DqF VF := by
    rw [← daughterPut_eq_integral hZ (hSm ω) hK hDr hDq hV]
    exact integral_nonneg fun _ ↦ mul_nonneg hDr.le (le_max_right _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact (daughterPut_lt_strike (VF := VF) (hSm ω) hK hDr hDq).le

/-- **Compound call payoff vanishes.** For mother strike `Km ≥ Kd·DrF` the call-on-put payoff
`(daughterPut(S) - Km)⁺` is `0` at every spot `S > 0`. -/
theorem compound_call_payoff_eq_zero {S Km K DrF DqF VF : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hDr : 0 < DrF) (hDq : 0 < DqF) (hKm : K * DrF ≤ Km) :
    max (daughterPut S K DrF DqF VF - Km) 0 = 0 :=
  max_eq_right (by linarith [daughterPut_lt_strike (VF := VF) hS hK hDr hDq])

/-- **Compound put payoff is linear.** For `Km ≥ Kd·DrF` the put-on-put payoff
`(Km - daughterPut(S))⁺` equals `Km - daughterPut(S)` at every spot `S > 0`. -/
theorem compound_put_payoff_eq {S Km K DrF DqF VF : ℝ} (hS : 0 < S) (hK : 0 < K)
    (hDr : 0 < DrF) (hDq : 0 < DqF) (hKm : K * DrF ≤ Km) :
    max (Km - daughterPut S K DrF DqF VF) 0 = Km - daughterPut S K DrF DqF VF :=
  max_eq_left (by linarith [daughterPut_lt_strike (VF := VF) hS hK hDr hDq])

/-- **Time-0 value of the put-on-put when no critical spot exists.** Let `Sm` be the (measurable,
positive) spot at `Tm`, `DrTm` the discount factor to `Tm` (a free real here, tied to no curve), and `price0` the daughter put's time-0 price. Assuming
the tower property `price0 = DrTm·𝔼[daughterPut(Sm)]` (hypothesis `htower`), for `Km ≥ Kd·DrF`
and `VF > 0`: `DrTm·𝔼[(Km - daughterPut(Sm))⁺] = Km·DrTm - price0`. Integrability of
`daughterPut(Sm)` is proved (`daughterPut_integrable`). -/
theorem compound_put_value {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {Sm : Ω → ℝ} {Km K DrF DqF VF DrTm price0 : ℝ}
    (hSm : ∀ ω, 0 < Sm ω) (hmeas : Measurable Sm) (hK : 0 < K) (hDr : 0 < DrF)
    (hDq : 0 < DqF) (hV : 0 < VF) (hKm : K * DrF ≤ Km)
    (htower : price0 = DrTm * ∫ ω, daughterPut (Sm ω) K DrF DqF VF ∂P) :
    DrTm * ∫ ω, max (Km - daughterPut (Sm ω) K DrF DqF VF) 0 ∂P = Km * DrTm - price0 := by
  have : (fun ω ↦ max (Km - daughterPut (Sm ω) K DrF DqF VF) 0)
      = fun ω ↦ Km - daughterPut (Sm ω) K DrF DqF VF :=
    funext fun ω ↦ compound_put_payoff_eq (hSm ω) hK hDr hDq hKm
  rw [this, integral_sub (integrable_const _)
    (daughterPut_integrable hSm hmeas hK hDr hDq hV), htower]
  simp; ring

/-- **The call-on-put has value zero when no critical spot exists.** -/
theorem compound_call_value_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Sm : Ω → ℝ} {Km K DrF DqF VF DrTm : ℝ} (hSm : ∀ ω, 0 < Sm ω) (hK : 0 < K)
    (hDr : 0 < DrF) (hDq : 0 < DqF) (hKm : K * DrF ≤ Km) :
    DrTm * ∫ ω, max (daughterPut (Sm ω) K DrF DqF VF - Km) 0 ∂P = 0 := by
  simp [compound_call_payoff_eq_zero (hSm _) hK hDr hDq hKm]

end MathFin
