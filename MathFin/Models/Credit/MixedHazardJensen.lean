/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Credit.Cox
public import Mathlib.Analysis.Convex.Integral

/-!
# Jensen's inequality for the mixed survival

Bagaria ch. 16, Calculation 16.10: under a random intensity the survival curve (16.7),
`Q(0, T) = E[exp(−∫₀ᵀ λₛ ds)]`, is a convex function of the integrated intensity, so
`E[e⁻ˣ] > e⁻ᴱ[ˣ]` and "a random intensity survives better than its own average" — a desk
bootstrapping a deterministic curve from quotes is recovering something below the mean
intensity, by an amount that is a pure convexity.

Here the random intensity is a hazard rate `h` with nonnegative, jointly measurable, integrable
sections, the mixed survival is the Cox mixing integral of `Models/Credit/Cox.lean`, and the
survival of the mean-intensity hazard is `hazardSurvival (fun s ↦ ∫ ω, h s ω dμ₁) T`
(`Models/Credit/HazardCurve.lean`):

* `cox_mixingSurvival_ge_meanIntensitySurvival` — the mixed survival integral is at least
  `ENNReal.ofReal (hazardSurvival …)`, Jensen's inequality (`ConvexOn.map_integral_le` of
  `Real.exp`) plus Fubini moving the mean of the integrated intensity inside the time integral.
* `cox_mixingSurvival_gt_or_intensityConst` — the strict dichotomy of Calculation 16.10: either
  the integrated intensity equals its mean almost surely, or the mixed survival integral is
  strictly greater (`StrictConvexOn.ae_eq_const_or_map_average_lt` of `Real.exp`).
* `cox_mixedSurvival_ge_meanIntensitySurvival` — through `cox_mixed_survival`, the survival
  probability of a default time tied to the clock's crossing of the integrated intensity is at
  least the survival curve of the mean-intensity hazard.

Scope: the inequality at a single horizon `T`. A deterministic intensity (every path's integrated
intensity equal to its mean) reaches the equality case, which is the degenerate branch of the
dichotomy; Bagaria's strict reading is the other branch, and a lower bound on the strictness gap
is not derived.

## Main definitions

The module adds no definition; its three results are inequalities for the existing Cox mixing
objects.

## Main results

* `cox_mixingSurvival_ge_meanIntensitySurvival`: for a nonnegative jointly measurable hazard `h`
  whose integrated intensity has an integrable mean, the mixed survival integral
  `∫⁻ ω, e^(−∫₀ᵀ h s ω) dμ₁` is at least `hazardSurvival` of the mean-intensity hazard at
  `T`.
* `cox_mixingSurvival_gt_or_intensityConst`: under the same hypotheses, either the integrated
  intensity equals its own mean almost surely, or the mixed survival integral is strictly
  greater than that bound.
* `cox_mixedSurvival_ge_meanIntensitySurvival`: the same lower bound for the survival
  probability of a Cox default time on the product of the path space with the unit-exponential
  clock.

## References

* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 16, eq. 16.7 and
  Calc. 16.10.
* [D. Lando, *Credit Risk Modeling*][Lando2004], ch. 5.

## Tags

mixed survival, stochastic intensity, Jensen's inequality, Cox process, credit spread
convexity, default probability, MSC 91G40, MSC 60G55, JEL G12
-/

@[expose] public section

namespace MathFin.Cox

open MeasureTheory ProbabilityTheory Real MathFin
open scoped NNReal ENNReal

/-! ### The Jensen step for the mixing integral

Two private lemmas for a general nonnegative integrable `Λ`, stated in the mixing variables of
`Cox.mixing_survival`: the exponential of a negative mean against the mean of the exponentials.
-/

private theorem integrable_exp_neg {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {μ₁ : Measure Ω₁}
    [IsProbabilityMeasure μ₁] {Λ : Ω₁ → ℝ} (hmeas : Measurable Λ) (hnn : ∀ ω, 0 ≤ Λ ω) :
    Integrable (fun ω ↦ rexp (-Λ ω)) μ₁ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (Real.measurable_exp.comp hmeas.neg |>.aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact (Real.exp_le_exp.2 (neg_nonpos.2 (hnn ω))).trans (by rw [Real.exp_zero])

private theorem mixingJensen_ge {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {μ₁ : Measure Ω₁}
    [IsProbabilityMeasure μ₁] {Λ : Ω₁ → ℝ} (hmeas : Measurable Λ)
    (hnn : ∀ ω, 0 ≤ Λ ω) (hint : Integrable Λ μ₁) :
    ENNReal.ofReal (rexp (-(∫ ω, Λ ω ∂μ₁))) ≤ ∫⁻ ω, ENNReal.ofReal (rexp (-Λ ω)) ∂μ₁ := by
  have hgi : Integrable (fun ω ↦ rexp (-Λ ω)) μ₁ := integrable_exp_neg hmeas hnn
  have hj : rexp (-∫ ω, Λ ω ∂μ₁) ≤ ∫ ω, rexp (-Λ ω) ∂μ₁ := by
    rw [← integral_neg]
    have hconv : ConvexOn ℝ (Set.univ : Set ℝ) rexp := convexOn_exp
    exact ConvexOn.map_integral_le hconv Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun ω ↦ Set.mem_univ _) hint.neg hgi
  have hconv : ENNReal.ofReal (∫ ω, rexp (-Λ ω) ∂μ₁)
      = ∫⁻ ω, ENNReal.ofReal (rexp (-Λ ω)) ∂μ₁ :=
    ofReal_integral_eq_lintegral_ofReal hgi
      (Filter.Eventually.of_forall fun ω ↦ Real.exp_nonneg _)
  exact (ENNReal.ofReal_le_ofReal hj).trans hconv.le

/-! ### The mean of the integrated intensity, moved inside the time integral

The integrated intensity of a path `ω` is `∫ s in (0)..T, h s ω`; the Fubini kernel below
identifies its mean with the cumulative hazard of the mean-intensity hazard.
-/

private theorem cumLambda_nonneg {Ω₁ : Type*} {_m₁ : MeasurableSpace Ω₁} {h : ℝ → Ω₁ → ℝ}
    (hnn : ∀ s ω, 0 ≤ h s ω) {T : ℝ} (hT : 0 ≤ T) (ω : Ω₁) :
    0 ≤ ∫ s in (0)..T, h s ω := by
  rw [intervalIntegral.integral_of_le hT]
  exact setIntegral_nonneg measurableSet_Ioc fun s _ ↦ hnn s ω

private theorem cumLambda_measurable {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁}
    {h : ℝ → Ω₁ → ℝ} (hmeas : Measurable fun p : Ω₁ × ℝ ↦ h p.2 p.1) {T : ℝ} (hT : 0 ≤ T) :
    Measurable fun ω : Ω₁ ↦ ∫ s in (0)..T, h s ω := by
  have hsm : StronglyMeasurable fun ω : Ω₁ ↦
      ∫ s, h s ω ∂(volume.restrict (Set.Ioc 0 T)) :=
    StronglyMeasurable.integral_prod_right' hmeas.stronglyMeasurable
  have hfunc : (fun ω : Ω₁ ↦ ∫ s, h s ω ∂(volume.restrict (Set.Ioc 0 T)))
      = fun ω : Ω₁ ↦ ∫ s in (0)..T, h s ω :=
    funext fun ω ↦ (intervalIntegral.integral_of_le hT).symm
  rw [← hfunc]
  exact hsm.measurable

private theorem meanCumHazard_swap {Ω₁ : Type*} {_m₁ : MeasurableSpace Ω₁} {μ₁ : Measure Ω₁}
    [IsProbabilityMeasure μ₁] {h : ℝ → Ω₁ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hmeas : Measurable fun p : Ω₁ × ℝ ↦ h p.2 p.1)
    (hnn : ∀ s ω, 0 ≤ h s ω)
    (hωint : ∀ᵐ ω ∂μ₁, IntervalIntegrable (fun s ↦ h s ω) volume 0 T)
    (hΛint : Integrable (fun ω ↦ ∫ s in (0)..T, h s ω) μ₁) :
    ∫ ω : Ω₁, (∫ s in (0)..T, h s ω) ∂μ₁
      = ∫ s in (0)..T, ∫ ω : Ω₁, h s ω ∂μ₁ := by
  have hintω : ∀ᵐ ω ∂μ₁, Integrable (fun s ↦ h s ω) (volume.restrict (Set.Ioc 0 T)) := by
    filter_upwards [hωint] with ω hω
    simp only [IntervalIntegrable, IntegrableOn] at hω
    exact hω.1
  have hintprod : Integrable (fun p : Ω₁ × ℝ ↦ h p.2 p.1)
      (μ₁.prod (volume.restrict (Set.Ioc 0 T))) := by
    have hmeas' : AEStronglyMeasurable (fun p : Ω₁ × ℝ ↦ h p.2 p.1)
        (μ₁.prod (volume.restrict (Set.Ioc 0 T))) := hmeas.aestronglyMeasurable
    have h2 : ∀ᵐ ω ∂μ₁, ∫⁻ s, ENNReal.ofReal (h s ω) ∂(volume.restrict (Set.Ioc 0 T))
        = ENNReal.ofReal (∫ s in (0)..T, h s ω) := by
      filter_upwards [hintω] with ω hintω'
      rw [intervalIntegral.integral_of_le hT]
      exact (ofReal_integral_eq_lintegral_ofReal hintω'
        (Filter.Eventually.of_forall fun s ↦ hnn s ω)).symm
    have hfenn : AEMeasurable (fun p : Ω₁ × ℝ ↦ ENNReal.ofReal (h p.2 p.1))
        (μ₁.prod (volume.restrict (Set.Ioc 0 T))) :=
      (ENNReal.measurable_ofReal.comp hmeas).aemeasurable
    have hstep : ∫⁻ p : Ω₁ × ℝ, ENNReal.ofReal (h p.2 p.1)
        ∂(μ₁.prod (volume.restrict (Set.Ioc 0 T)))
        = ∫⁻ ω : Ω₁, ∫⁻ s, ENNReal.ofReal (h s ω)
            ∂(volume.restrict (Set.Ioc 0 T)) ∂μ₁ := lintegral_prod _ hfenn
    have hstep2 : ∫⁻ ω : Ω₁, ∫⁻ s, ENNReal.ofReal (h s ω)
        ∂(volume.restrict (Set.Ioc 0 T)) ∂μ₁
        = ENNReal.ofReal (∫ ω : Ω₁, (∫ s in (0)..T, h s ω) ∂μ₁) := by
      rw [lintegral_congr_ae h2]
      exact (ofReal_integral_eq_lintegral_ofReal hΛint
        (Filter.Eventually.of_forall fun ω ↦ cumLambda_nonneg (_m₁ := _m₁) hnn hT ω)).symm
    have hfin : ∫⁻ p : Ω₁ × ℝ, ENNReal.ofReal (h p.2 p.1)
        ∂(μ₁.prod (volume.restrict (Set.Ioc 0 T))) < ⊤ := by
      rw [hstep, hstep2]
      exact ENNReal.ofReal_lt_top
    have hnn2 : ∀ᵐ p ∂(μ₁.prod (volume.restrict (Set.Ioc 0 T))),
        (0 : ℝ) ≤ h p.2 p.1 := Filter.Eventually.of_forall fun p ↦ hnn p.2 p.1
    exact ⟨hmeas', (hasFiniteIntegral_iff_ofReal hnn2).2 hfin⟩
  have hmean := MeasureTheory.integral_integral_swap (f := fun (ω : Ω₁) (s : ℝ) ↦ h s ω) hintprod
  simp only [intervalIntegral.integral_of_le hT] at hmean ⊢
  rw [← hmean]

/-! ### The mixed survival against the survival of the mean-intensity hazard -/

/-- **Jensen's inequality for the mixed survival** — Bagaria ch. 16, eq. 16.7 and Calc. 16.10:
for a random hazard rate `h` with nonnegative, jointly measurable sections, integrable sections
and integrable integrated intensity, the mixed survival integral `∫⁻ ω, e^(−∫₀ᵀ h s ω) dμ₁` is
at least the survival curve of the mean-intensity hazard, `hazardSurvival (fun s ↦ ∫ ω, h s ω)
T`: `e⁻ˣ` is convex, so `E[e⁻ˣ] ≥ e⁻ᴱ[ˣ]`, and the mean of the integrated intensity is the
cumulative hazard of the mean-intensity hazard (Fubini). A deterministic intensity gives
equality, so the bound is sharp. -/
theorem cox_mixingSurvival_ge_meanIntensitySurvival
    {Ω₁ : Type*} {_m₁ : MeasurableSpace Ω₁} {μ₁ : Measure Ω₁} [IsProbabilityMeasure μ₁]
    {h : ℝ → Ω₁ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hmeas : Measurable fun p : Ω₁ × ℝ ↦ h p.2 p.1)
    (hnn : ∀ s ω, 0 ≤ h s ω)
    (hωint : ∀ᵐ ω ∂μ₁, IntervalIntegrable (fun s ↦ h s ω) volume 0 T)
    (hΛint : Integrable (fun ω ↦ ∫ s in (0)..T, h s ω) μ₁) :
    ENNReal.ofReal (hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T)
      ≤ ∫⁻ ω : Ω₁, ENNReal.ofReal (rexp (-(∫ s in (0)..T, h s ω))) ∂μ₁ := by
  have hΛmeas := cumLambda_measurable (m₁ := _m₁) hmeas hT
  have hΛnn : ∀ ω : Ω₁, 0 ≤ ∫ s in (0)..T, h s ω := fun ω ↦ cumLambda_nonneg (_m₁ := _m₁) hnn hT ω
  have hmean := meanCumHazard_swap hT hmeas hnn hωint hΛint
  have hident : ENNReal.ofReal (hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T)
      = ENNReal.ofReal (rexp (-(∫ ω : Ω₁, (∫ s in (0)..T, h s ω) ∂μ₁))) := by
    have hrfl : hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T
        = rexp (-(∫ s in (0)..T, ∫ ω : Ω₁, h s ω ∂μ₁)) := rfl
    rw [hrfl, ← hmean]
  rw [hident]
  exact mixingJensen_ge hΛmeas hΛnn hΛint

/-- **The strict dichotomy of Calculation 16.10** — under the hypotheses of
`cox_mixingSurvival_ge_meanIntensitySurvival`, either the integrated intensity equals its own
mean almost surely (the deterministic case), or the mixed survival integral is strictly greater
than the survival curve of the mean-intensity hazard: a random intensity survives strictly
better than its own average. -/
theorem cox_mixingSurvival_gt_or_intensityConst
    {Ω₁ : Type*} {_m₁ : MeasurableSpace Ω₁} {μ₁ : Measure Ω₁} [IsProbabilityMeasure μ₁]
    {h : ℝ → Ω₁ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hmeas : Measurable fun p : Ω₁ × ℝ ↦ h p.2 p.1)
    (hnn : ∀ s ω, 0 ≤ h s ω)
    (hωint : ∀ᵐ ω ∂μ₁, IntervalIntegrable (fun s ↦ h s ω) volume 0 T)
    (hΛint : Integrable (fun ω ↦ ∫ s in (0)..T, h s ω) μ₁) :
    (∀ᵐ ω ∂μ₁, (∫ s in (0)..T, h s ω) = ∫ s in (0)..T, ∫ ω' : Ω₁, h s ω' ∂μ₁)
    ∨ ENNReal.ofReal (hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T)
        < ∫⁻ ω : Ω₁, ENNReal.ofReal (rexp (-(∫ s in (0)..T, h s ω))) ∂μ₁ := by
  have hΛmeas := cumLambda_measurable (m₁ := _m₁) hmeas hT
  have hΛnn : ∀ ω : Ω₁, 0 ≤ ∫ s in (0)..T, h s ω :=
    fun ω ↦ cumLambda_nonneg (_m₁ := _m₁) hnn hT ω
  have hmean := meanCumHazard_swap hT hmeas hnn hωint hΛint
  have hgi : Integrable (fun ω ↦ rexp (-(∫ s in (0)..T, h s ω))) μ₁ :=
    integrable_exp_neg hΛmeas hΛnn
  have hsc : StrictConvexOn ℝ (Set.univ : Set ℝ) rexp := strictConvexOn_exp
  have havgmean : (⨍ (x : Ω₁), (-fun ω : Ω₁ ↦ ∫ s in (0)..T, h s ω) x ∂μ₁)
      = -(∫ s in (0)..T, ∫ ω' : Ω₁, h s ω' ∂μ₁) := by
    rw [average_neg (f := fun ω : Ω₁ ↦ ∫ s in (0)..T, h s ω),
      average_eq_integral, ← hmean]
  rcases StrictConvexOn.ae_eq_const_or_map_average_lt hsc
      Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun ω ↦ Set.mem_univ _)
      hΛint.neg hgi with hconst | hstrict
  · left
    filter_upwards [hconst] with ω hω
    simp only [Pi.neg_apply, Function.const_apply] at hω
    have h3 : -(∫ s in (0)..T, h s ω) = -(∫ s in (0)..T, ∫ ω' : Ω₁, h s ω' ∂μ₁) :=
      hω.trans havgmean
    linarith
  · right
    have havg2' : (⨍ (x : Ω₁), rexp ((-fun ω : Ω₁ ↦ ∫ s in (0)..T, h s ω) x) ∂μ₁)
        = ∫ ω' : Ω₁, rexp (-(∫ s in (0)..T, h s ω')) ∂μ₁ :=
      average_eq_integral (f := fun x : Ω₁ ↦ rexp ((-fun ω : Ω₁ ↦ ∫ s in (0)..T, h s ω) x))
        (μ := μ₁)
    have hident : ENNReal.ofReal (hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T)
        = ENNReal.ofReal (rexp (⨍ (x : Ω₁), (-fun ω : Ω₁ ↦ ∫ s in (0)..T, h s ω) x ∂μ₁)) := by
      have hrfl : hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T
          = rexp (-(∫ s in (0)..T, ∫ ω : Ω₁, h s ω ∂μ₁)) := rfl
      rw [hrfl, ← havgmean]
    have hconv : ENNReal.ofReal (∫ ω' : Ω₁, rexp (-(∫ s in (0)..T, h s ω')) ∂μ₁)
        = ∫⁻ ω' : Ω₁, ENNReal.ofReal (rexp (-(∫ s in (0)..T, h s ω'))) ∂μ₁ :=
      ofReal_integral_eq_lintegral_ofReal hgi
        (Filter.Eventually.of_forall fun ω ↦ Real.exp_nonneg _)
    rw [hident, ← hconv, ← havg2']
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_nonneg _)).2 hstrict

/-- **The survival probability of a Cox default time against the mean-intensity hazard** —
through `cox_mixed_survival`, a default time on the product of the path space with the
unit-exponential clock whose survival event is the clock beating the integrated intensity has
survival probability at least `hazardSurvival` of the mean-intensity hazard. -/
theorem cox_mixedSurvival_ge_meanIntensitySurvival
    {Ω₁ : Type*} {_m₁ : MeasurableSpace Ω₁} {μ₁ : Measure Ω₁} [IsProbabilityMeasure μ₁]
    {h : ℝ → Ω₁ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hmeas : Measurable fun p : Ω₁ × ℝ ↦ h p.2 p.1)
    (hnn : ∀ s ω, 0 ≤ h s ω)
    (hωint : ∀ᵐ ω ∂μ₁, IntervalIntegrable (fun s ↦ h s ω) volume 0 T)
    (hΛint : Integrable (fun ω ↦ ∫ s in (0)..T, h s ω) μ₁)
    {τ : Ω₁ × ℝ → ℝ}
    (hτ : ∀ p : Ω₁ × ℝ, T < τ p ↔ (∫ s in (0)..T, h s p.1) < p.2) :
    (μ₁.prod (expMeasure 1)) {p : Ω₁ × ℝ | T < τ p}
      ≥ ENNReal.ofReal (hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T) := by
  have hΛmeasAll : ∀ t : ℝ, Measurable fun ω : Ω₁ ↦ ∫ s in (0)..(max t 0), h s ω :=
    fun t ↦ cumLambda_measurable (m₁ := _m₁) hmeas (le_max_right t 0)
  have hΛnnAll : ∀ (t : ℝ) (ω : Ω₁), 0 ≤ ∫ s in (0)..(max t 0), h s ω :=
    fun t ω ↦ cumLambda_nonneg (_m₁ := _m₁) hnn (le_max_right t 0) ω
  rw [cox_mixed_survival (Λ := fun t ω ↦ ∫ s in (0)..(max t 0), h s ω)
    hΛmeasAll hΛnnAll (t := T) (fun p ↦ by rw [max_eq_left hT]; exact hτ p)]
  rw [max_eq_left hT]
  exact cox_mixingSurvival_ge_meanIntensitySurvival hT hmeas hnn hωint hΛint

end MathFin.Cox
