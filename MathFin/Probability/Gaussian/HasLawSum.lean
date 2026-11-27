/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Init
public import MathFin.Probability.Gaussian.GaussianMoments
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Sums of independent Gaussian random variables

The Gaussian laws are closed under addition of independent random variables: if
`X ~ N(m₁, v₁)` and `Y ~ N(m₂, v₂)` are independent then `X + Y ~ N(m₁ + m₂, v₁ + v₂)`
(`hasLaw_add_of_indepFun`). This is the closure behind every short-rate model's total
variance accumulation.

## Main results

* `hasLaw_add_of_indepFun` — the sum of independent Gaussian random variables is Gaussian
  with the means and variances added.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.2.1

## Tags

Gaussian law, independent sum, moment generating function, MSC 60E05, MSC 60G15
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Sum of independent Gaussian variables**: with `X ~ N(m₁, v₁)`, `Y ~ N(m₂, v₂)`
independent, `X + Y ~ N(m₁ + m₂, v₁ + v₂)` — the closure of the Gaussian laws under
independent convolution. -/
theorem hasLaw_add_of_indepFun {X Y : Ω → ℝ} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0}
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

end MathFin
