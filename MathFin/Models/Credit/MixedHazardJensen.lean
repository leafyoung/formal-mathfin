/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Credit.Cox
public import MathFin.Probability.Analysis.MixingJensen

/-!
# Jensen's inequality for the mixed survival

Bagaria ch. 16, Calculation 16.10: under a random intensity the survival curve (16.7),
`Q(0, T) = E[exp(−∫₀ᵀ λₛ ds)]`, is a convex function of the integrated intensity, so
`E[e⁻ˣ] > e⁻ᴱ[ˣ]` and "a random intensity survives better than its own average" — a desk
bootstrapping a deterministic curve from quotes is recovering something below the mean
intensity, by an amount that is a pure convexity.

Here the random intensity is a hazard rate `h` with nonnegative, jointly measurable sections
whose paths are interval-integrable on `[0, T]` almost surely and whose integrated intensity has
an integrable mean; the mixed survival is the Cox mixing integral of `Models/Credit/Cox.lean`,
and the survival of the mean-intensity hazard is
`hazardSurvival (fun s ↦ ∫ ω, h s ω dμ₁) T` (`Models/Credit/HazardCurve.lean`). The measure
theory is the exponential-Jensen pair and the running-integral exchange of
`Probability/Analysis/MixingJensen.lean`:

* `cox_mixingSurvival_ge_meanIntensitySurvival` — the mixed survival integral is at least
  `ENNReal.ofReal (hazardSurvival …)` (`exp_jensen_of_nonneg` plus Fubini moving the mean of
  the integrated intensity inside the time integral, `runningIntegral_mean_eq`).
* `cox_mixingSurvival_gt_or_intensityConst` — the strict dichotomy of Calculation 16.10: either
  the integrated intensity equals its mean almost surely, or the mixed survival integral is
  strictly greater (`exp_jensen_strict_of_nonneg`).
* `cox_mixedSurvival_ge_meanIntensitySurvival` — through `cox_mixed_survival`, the survival
  probability of a default time tied to the clock's crossing of the integrated intensity is at
  least the survival curve of the mean-intensity hazard.

Scope: the inequality at a single horizon `T`. A deterministic intensity (every path's integrated
intensity equal to its mean) reaches the equality case, which is the degenerate branch of the
dichotomy; Bagaria's strict reading is the other branch, and a lower bound on the strictness gap
is not derived. Per-time integrability of `h` follows almost surely from the hypotheses, so the
mean hazard's junk on a null set of times does not reach the time integral.

## Main definitions

The module adds no definition; its three results are inequalities for the existing Cox mixing
objects.

## Main results

* `cox_mixingSurvival_ge_meanIntensitySurvival`: for a nonnegative jointly measurable hazard `h`
  whose integrated intensity has an integrable mean, the mixed survival integral
  `∫⁻ ω, e^(−∫₀ᵀ h s ω) dμ₁` is at least `hazardSurvival` of the mean-intensity hazard at `T`.
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

/-- **Jensen's inequality for the mixed survival** — Bagaria ch. 16, eq. 16.7 and Calc. 16.10:
for a random hazard rate `h` with nonnegative, jointly measurable sections whose paths are
interval-integrable on `[0, T]` almost surely and whose integrated intensity has an integrable
mean, the mixed survival integral `∫⁻ ω, e^(−∫₀ᵀ h s ω) dμ₁` is at least the survival curve of
the mean-intensity hazard, `hazardSurvival (fun s ↦ ∫ ω, h s ω) T`. A deterministic intensity
gives equality, so the bound is sharp. -/
theorem cox_mixingSurvival_ge_meanIntensitySurvival
    {Ω₁ : Type*} {_m₁ : MeasurableSpace Ω₁} {μ₁ : Measure Ω₁} [IsProbabilityMeasure μ₁]
    {h : ℝ → Ω₁ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hmeas : Measurable fun p : Ω₁ × ℝ ↦ h p.2 p.1)
    (hnn : ∀ s ω, 0 ≤ h s ω)
    (hωint : ∀ᵐ ω ∂μ₁, IntervalIntegrable (fun s ↦ h s ω) volume 0 T)
    (hΛint : Integrable (fun ω ↦ ∫ s in (0)..T, h s ω) μ₁) :
    ENNReal.ofReal (hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T)
      ≤ ∫⁻ ω : Ω₁, ENNReal.ofReal (rexp (-(∫ s in (0)..T, h s ω))) ∂μ₁ := by
  have hΛmeas := runningIntegral_measurable (m := _m₁) hmeas hT
  have hΛnn : ∀ ω : Ω₁, 0 ≤ ∫ s in (0)..T, h s ω :=
    fun ω ↦ runningIntegral_nonneg (_m := _m₁) hnn hT ω
  have hmean := runningIntegral_mean_eq hT hmeas hnn hωint hΛint
  have hident : ENNReal.ofReal (hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T)
      = ENNReal.ofReal (rexp (-(∫ ω : Ω₁, (∫ s in (0)..T, h s ω) ∂μ₁))) := by
    have hrfl : hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T
        = rexp (-(∫ s in (0)..T, ∫ ω : Ω₁, h s ω ∂μ₁)) := rfl
    rw [hrfl, ← hmean]
  rw [hident]
  exact exp_jensen_of_nonneg hΛmeas hΛnn hΛint

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
  have hΛmeas := runningIntegral_measurable (m := _m₁) hmeas hT
  have hΛnn : ∀ ω : Ω₁, 0 ≤ ∫ s in (0)..T, h s ω :=
    fun ω ↦ runningIntegral_nonneg (_m := _m₁) hnn hT ω
  have hmean := runningIntegral_mean_eq hT hmeas hnn hωint hΛint
  have hgi : Integrable (fun ω ↦ rexp (-(∫ s in (0)..T, h s ω))) μ₁ :=
    integrable_exp_neg_of_nonneg hΛmeas hΛnn
  have hident : ENNReal.ofReal (hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T)
      = ENNReal.ofReal (rexp (-(∫ ω : Ω₁, (∫ s in (0)..T, h s ω) ∂μ₁))) := by
    have hrfl : hazardSurvival (fun s ↦ ∫ ω : Ω₁, h s ω ∂μ₁) T
        = rexp (-(∫ s in (0)..T, ∫ ω : Ω₁, h s ω ∂μ₁)) := rfl
    rw [hrfl, ← hmean]
  rcases exp_jensen_strict_of_nonneg hΛmeas hΛnn hΛint with hconst | hstrict
  · left
    filter_upwards [hconst] with ω hω
    rw [hω, ← hmean]
  · right
    rw [hident]
    exact hstrict

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
    fun t ↦ runningIntegral_measurable (m := _m₁) hmeas (le_max_right t 0)
  have hΛnnAll : ∀ (t : ℝ) (ω : Ω₁), 0 ≤ ∫ s in (0)..(max t 0), h s ω :=
    fun t ω ↦ runningIntegral_nonneg (_m := _m₁) hnn (le_max_right t 0) ω
  rw [cox_mixed_survival (Λ := fun t ω ↦ ∫ s in (0)..(max t 0), h s ω)
    hΛmeasAll hΛnnAll (t := T) (fun p ↦ by rw [max_eq_left hT]; exact hτ p)]
  rw [max_eq_left hT]
  exact cox_mixingSurvival_ge_meanIntensitySurvival hT hmeas hnn hωint hΛint

end MathFin.Cox
