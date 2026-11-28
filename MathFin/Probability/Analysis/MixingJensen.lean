/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Init
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Jensen's inequality for an exponential, and the running integral of a random family

Two measure-theoretic facts used by convexity arguments on expectations of exponentials, in
`ENNReal` form so that survival integrals need no integrability of the exponentiated side.

* **Jensen for the exponential.** For a probability measure, a measurable `Λ ≥ 0` with
  integrable mean, the exponential of the negative mean is at most the mean of the
  exponentials: `ENNReal.ofReal (rexp (-∫ ω, Λ ω ∂μ)) ≤ ∫⁻ ω, ENNReal.ofReal (rexp (-Λ ω)) ∂μ`
  (`exp_jensen_of_nonneg`, Jensen's inequality `ConvexOn.map_integral_le` of `Real.exp`
  plus the conversion of a real integral of a nonnegative function into an `ENNReal`
  lintegral). Since `exp` is strictly convex, the dichotomy
  `exp_jensen_strict_of_nonneg` gives equality exactly when `Λ` is a.s. its own mean.

* **The running integral.** For a jointly measurable family `h : ℝ → α → ℝ` of nonnegative
  functions, the pathwise integral `ω ↦ ∫ s in (0)..T, h s ω` is nonnegative
  (`runningIntegral_nonneg`), measurable (`runningIntegral_measurable`), and — under a
  probability measure on the paths and interval-integrable paths — its mean is the running
  integral of the means (`runningIntegral_mean_eq`, Fubini–Tonelli on the product with the
  restricted Lebesgue measure).

## Main definitions

The module adds no definition; its six results are inequalities and identifications.

## Main results

* `integrable_exp_neg_of_nonneg`: the exponential of the negative of a nonnegative random
  variable is integrable (bounded by 1).
* `exp_jensen_of_nonneg`, `exp_jensen_strict_of_nonneg`, `exp_jensen_eq_of_ae_const`: the
  Jensen inequality, its strict dichotomy, and its equality case for an a.s. constant
  intensity, for `exp ∘ (−·)`, in `ENNReal` form.
* `runningIntegral_nonneg`, `runningIntegral_measurable`, `runningIntegral_mean_eq`: the
  pathwise running integral of a jointly measurable nonnegative family is nonnegative,
  measurable, and its mean is the running integral of the means.

## References

* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 16, eq. 16.7 and
  Calc. 16.10.

## Tags

Jensen's inequality, exponential mixing, running integral, Fubini, convexity, expectation,
MSC 60E15, MSC 28A25
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ### Jensen for the exponential, in `ENNReal` form -/

/-- The exponential of the negative of a nonnegative random variable is integrable under a
probability measure: `rexp (-Λ)` is measurable and bounded by `1`. -/
theorem integrable_exp_neg_of_nonneg {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Λ : Ω → ℝ} (hmeas : Measurable Λ) (hnn : ∀ ω, 0 ≤ Λ ω) :
    Integrable (fun ω ↦ rexp (-Λ ω)) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (Real.measurable_exp.comp hmeas.neg |>.aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact (Real.exp_le_exp.2 (neg_nonpos.2 (hnn ω))).trans (by rw [Real.exp_zero])

/-- **Jensen's inequality for the exponential, in `ENNReal` form**: for a probability measure
and a measurable `Λ ≥ 0` with integrable mean, the exponential of the negative mean is at
most the mean of the exponentials. -/
theorem exp_jensen_of_nonneg {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Λ : Ω → ℝ} (hmeas : Measurable Λ)
    (hnn : ∀ ω, 0 ≤ Λ ω) (hint : Integrable Λ μ) :
    ENNReal.ofReal (rexp (-(∫ ω, Λ ω ∂μ))) ≤ ∫⁻ ω, ENNReal.ofReal (rexp (-Λ ω)) ∂μ := by
  have hgi : Integrable (fun ω ↦ rexp (-Λ ω)) μ := integrable_exp_neg_of_nonneg hmeas hnn
  have hj : rexp (-∫ ω, Λ ω ∂μ) ≤ ∫ ω, rexp (-Λ ω) ∂μ := by
    rw [← integral_neg]
    have hconv : ConvexOn ℝ (Set.univ : Set ℝ) rexp := convexOn_exp
    exact ConvexOn.map_integral_le hconv Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun ω ↦ Set.mem_univ _) hint.neg hgi
  have hconv : ENNReal.ofReal (∫ ω, rexp (-Λ ω) ∂μ)
      = ∫⁻ ω, ENNReal.ofReal (rexp (-Λ ω)) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hgi
      (Filter.Eventually.of_forall fun ω ↦ Real.exp_nonneg _)
  exact (ENNReal.ofReal_le_ofReal hj).trans hconv.le

/-- **The strict dichotomy behind `exp_jensen_of_nonneg`**: under the same hypotheses,
either `Λ` is a.s. its own mean, or the Jensen inequality of `exp_jensen_of_nonneg` is
strict. -/
theorem exp_jensen_strict_of_nonneg {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Λ : Ω → ℝ} (hmeas : Measurable Λ)
    (hnn : ∀ ω, 0 ≤ Λ ω) (hint : Integrable Λ μ) :
    (∀ᵐ ω ∂μ, Λ ω = ∫ ω', Λ ω' ∂μ)
    ∨ ENNReal.ofReal (rexp (-(∫ ω, Λ ω ∂μ)))
        < ∫⁻ ω, ENNReal.ofReal (rexp (-Λ ω)) ∂μ := by
  have hgi : Integrable (fun ω ↦ rexp (-Λ ω)) μ := integrable_exp_neg_of_nonneg hmeas hnn
  have hsc : StrictConvexOn ℝ (Set.univ : Set ℝ) rexp := strictConvexOn_exp
  rcases StrictConvexOn.ae_eq_const_or_map_average_lt hsc
      Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun ω ↦ Set.mem_univ _)
      hint.neg hgi with hconst | hstrict
  · left
    have havg : (⨍ (x : Ω), (-Λ) x ∂μ) = -(∫ ω' : Ω, Λ ω' ∂μ) := by
      rw [average_neg (f := Λ), average_eq_integral]
    filter_upwards [hconst] with ω hω
    simp only [Pi.neg_apply, Function.const_apply] at hω
    have h3 : -(Λ ω) = -(∫ ω' : Ω, Λ ω' ∂μ) := hω.trans havg
    linarith
  · right
    have havg2 : (⨍ (x : Ω), rexp ((-Λ) x) ∂μ)
        = ∫ ω' : Ω, rexp (-Λ ω') ∂μ :=
      average_eq_integral (f := fun x : Ω ↦ rexp ((-Λ) x)) (μ := μ)
    have hident : ENNReal.ofReal (rexp (-(∫ ω, Λ ω ∂μ)))
        = ENNReal.ofReal (rexp (⨍ (x : Ω), (-Λ) x ∂μ)) := by
      have havg' : ⨍ (x : Ω), (-fun ω : Ω ↦ Λ ω) x ∂μ = -(∫ ω' : Ω, Λ ω' ∂μ) := by
        rw [average_neg (f := Λ), average_eq_integral]
      rw [havg']
    have hconv : ENNReal.ofReal (∫ ω' : Ω, rexp (-Λ ω') ∂μ)
        = ∫⁻ ω' : Ω, ENNReal.ofReal (rexp (-Λ ω')) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hgi
        (Filter.Eventually.of_forall fun ω ↦ Real.exp_nonneg _)
    rw [hident, ← hconv, ← havg2]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_nonneg _)).2 hstrict

/-- **Equality in `exp_jensen_of_nonneg` for an a.s. constant intensity**: if `Λ` equals its
own mean almost surely, the two sides of `exp_jensen_of_nonneg` are equal — the degenerate
branch of `exp_jensen_strict_of_nonneg`. -/
theorem exp_jensen_eq_of_ae_const {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Λ : Ω → ℝ}
    (hconst : ∀ᵐ ω ∂μ, Λ ω = ∫ ω' : Ω, Λ ω' ∂μ) :
    ENNReal.ofReal (rexp (-(∫ ω, Λ ω ∂μ))) = ∫⁻ ω, ENNReal.ofReal (rexp (-Λ ω)) ∂μ := by
  have hae : ∫⁻ ω, ENNReal.ofReal (rexp (-Λ ω)) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (rexp (-(∫ ω' : Ω, Λ ω' ∂μ))) ∂μ :=
    lintegral_congr_ae (hconst.mono fun ω hω ↦ by dsimp only; rw [hω])
  rw [hae, lintegral_const, IsProbabilityMeasure.measure_univ, mul_one]

/-! ### The running integral of a jointly measurable nonnegative family -/

/-- **The pathwise running integral is nonnegative**: for a jointly measurable family
`h : ℝ → Ω → ℝ` with `0 ≤ h s ω`, the integral over `(0)..T` is nonnegative for every `T ≥ 0`
and every path. -/
theorem runningIntegral_nonneg {Ω : Type*} {_m : MeasurableSpace Ω} {h : ℝ → Ω → ℝ}
    (hnn : ∀ s ω, 0 ≤ h s ω) {T : ℝ} (hT : 0 ≤ T) (ω : Ω) :
    0 ≤ ∫ s in (0)..T, h s ω := by
  rw [intervalIntegral.integral_of_le hT]
  exact setIntegral_nonneg measurableSet_Ioc fun s _ ↦ hnn s ω

/-- **The pathwise running integral is measurable**: for a jointly measurable family
`h : ℝ → Ω → ℝ`, the map `ω ↦ ∫ s in (0)..T, h s ω` is measurable for `T ≥ 0`. -/
theorem runningIntegral_measurable {Ω : Type*} {m : MeasurableSpace Ω}
    {h : ℝ → Ω → ℝ} (hmeas : Measurable fun p : Ω × ℝ ↦ h p.2 p.1) {T : ℝ} (hT : 0 ≤ T) :
    Measurable fun ω : Ω ↦ ∫ s in (0)..T, h s ω := by
  have hsm : StronglyMeasurable fun ω : Ω ↦
      ∫ s, h s ω ∂(volume.restrict (Set.Ioc 0 T)) :=
    StronglyMeasurable.integral_prod_right' hmeas.stronglyMeasurable
  have hfunc : (fun ω : Ω ↦ ∫ s, h s ω ∂(volume.restrict (Set.Ioc 0 T)))
      = fun ω : Ω ↦ ∫ s in (0)..T, h s ω :=
    funext fun ω ↦ (intervalIntegral.integral_of_le hT).symm
  rw [← hfunc]
  exact hsm.measurable

/-- **The mean of the running integral is the running integral of the means** (Fubini–Tonelli):
for a probability measure `μ`, a jointly measurable nonnegative family `h` with
interval-integrable paths and an integrable running integral at `T`,
`∫ ω, (∫ s in (0)..T, h s ω) dμ = ∫ s in (0)..T, (∫ ω, h s ω dμ) ds`. -/
theorem runningIntegral_mean_eq {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {h : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hmeas : Measurable fun p : Ω × ℝ ↦ h p.2 p.1)
    (hnn : ∀ s ω, 0 ≤ h s ω)
    (hωint : ∀ᵐ ω ∂μ, IntervalIntegrable (fun s ↦ h s ω) volume 0 T)
    (hΛint : Integrable (fun ω ↦ ∫ s in (0)..T, h s ω) μ) :
    ∫ ω : Ω, (∫ s in (0)..T, h s ω) ∂μ
      = ∫ s in (0)..T, (∫ ω : Ω, h s ω ∂μ) := by
  have hintω : ∀ᵐ ω ∂μ, Integrable (fun s ↦ h s ω) (volume.restrict (Set.Ioc 0 T)) := by
    filter_upwards [hωint] with ω hω
    simp only [IntervalIntegrable, IntegrableOn] at hω
    exact hω.1
  have hmeas' : AEStronglyMeasurable (fun p : Ω × ℝ ↦ h p.2 p.1)
      (μ.prod (volume.restrict (Set.Ioc 0 T))) := hmeas.aestronglyMeasurable
  have h2 : ∀ᵐ ω ∂μ, ∫⁻ s, ENNReal.ofReal (h s ω) ∂(volume.restrict (Set.Ioc 0 T))
      = ENNReal.ofReal (∫ s in (0)..T, h s ω) := by
    filter_upwards [hintω] with ω hintω'
    rw [intervalIntegral.integral_of_le hT]
    exact (ofReal_integral_eq_lintegral_ofReal hintω'
      (Filter.Eventually.of_forall fun s ↦ hnn s ω)).symm
  have hfenn : AEMeasurable (fun p : Ω × ℝ ↦ ENNReal.ofReal (h p.2 p.1))
      (μ.prod (volume.restrict (Set.Ioc 0 T))) :=
    (ENNReal.measurable_ofReal.comp hmeas).aemeasurable
  have hstep : ∫⁻ p : Ω × ℝ, ENNReal.ofReal (h p.2 p.1)
      ∂(μ.prod (volume.restrict (Set.Ioc 0 T)))
      = ∫⁻ ω : Ω, ∫⁻ s, ENNReal.ofReal (h s ω)
          ∂(volume.restrict (Set.Ioc 0 T)) ∂μ := lintegral_prod _ hfenn
  have hstep2 : ∫⁻ ω : Ω, ∫⁻ s, ENNReal.ofReal (h s ω)
      ∂(volume.restrict (Set.Ioc 0 T)) ∂μ
      = ENNReal.ofReal (∫ ω : Ω, (∫ s in (0)..T, h s ω) ∂μ) := by
    rw [lintegral_congr_ae h2]
    exact (ofReal_integral_eq_lintegral_ofReal hΛint
      (Filter.Eventually.of_forall fun ω ↦ runningIntegral_nonneg (_m := m) hnn hT ω)).symm
  have hfin : ∫⁻ p : Ω × ℝ, ENNReal.ofReal (h p.2 p.1)
      ∂(μ.prod (volume.restrict (Set.Ioc 0 T))) < ⊤ := by
    rw [hstep, hstep2]
    exact ENNReal.ofReal_lt_top
  have hnn2 : ∀ᵐ p ∂(μ.prod (volume.restrict (Set.Ioc 0 T))),
      (0 : ℝ) ≤ h p.2 p.1 := Filter.Eventually.of_forall fun p ↦ hnn p.2 p.1
  have hintprod : Integrable (fun p : Ω × ℝ ↦ h p.2 p.1)
      (μ.prod (volume.restrict (Set.Ioc 0 T))) :=
    ⟨hmeas', (hasFiniteIntegral_iff_ofReal hnn2).2 hfin⟩
  have hmean := MeasureTheory.integral_integral_swap (f := fun (ω : Ω) (s : ℝ) ↦ h s ω) hintprod
  simp only [intervalIntegral.integral_of_le hT] at hmean ⊢
  rw [← hmean]

end MathFin
