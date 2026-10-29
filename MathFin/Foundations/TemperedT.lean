/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.StudentT

/-!
# The exponentially tempered Student-t law

The **tempered Student-t law** with `ν > 0` degrees of freedom and tempering parameter
`lam > 0` is the law on `ℝ` with density proportional to `e^{-|x|/lam} · k_ν(x)`, the
Student-t kernel damped by a symmetric exponential. It is the Route-A redesign of the
FMGD case study: exact t innovations have *no* finite exponential moments
(`studentT_expMoment_eq_top` below), so any average of exponentials of t increments has
infinite mean and moment matching is ill-posed; exponential tempering restores a
well-posedness strip.

## Main results

* `studentT_expMoment_eq_top`: **the ill-posedness theorem** — for every `ν > 0` and
  every `θ ≠ 0`, `E[e^{θX}] = ∞` under the exact Student-t law. The moment the
  Turnbull–Wakeman matcher needs does not exist.
* `temperedTMeasure ν lam`: the tempered law, a probability measure for `ν, lam > 0`
  (`isProbabilityMeasure_temperedTMeasure`).
* `temperedT_expMoment_eq_top`: outside the strip, `1/lam < |θ|`, the tempered law again
  has `E[e^{θX}] = ∞` — the strip edge is sharp.
* `integrable_exp_mul_temperedTPDFReal` and `temperedT_expMoment_pos`: on the closed
  strip `|θ| ≤ 1/lam` the exponential moment is finite and strictly positive. (The
  boundary belongs to the finite side: at `|θ| = 1/lam` the surviving decay is the
  polynomial t tail, integrable for every `ν > 0`.)
* `temperedExpMoment ν lam θ`: the exponential moment as a definition, with the
  evaluation lemma `integral_exp_comp_eq_temperedExpMoment` for `HasLaw` copies of the
  law.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Topology

variable {ν lam : ℝ}

/-! ### The tempering weight and the kernel -/

/-- The exponential tempering factor `e^{-|x|/lam}`, symmetric and at most one. -/
noncomputable def temperedTWeight (lam x : ℝ) : ℝ := Real.exp (-(|x|) / lam)

lemma temperedTWeight_pos (lam x : ℝ) : 0 < temperedTWeight lam x := Real.exp_pos _

lemma temperedTWeight_le_one (hlam : 0 < lam) (x : ℝ) : temperedTWeight lam x ≤ 1 := by
  refine Real.exp_le_one_iff.2 ?_
  rw [neg_div]
  exact neg_nonpos.2 (div_nonneg (abs_nonneg x) hlam.le)

lemma temperedTWeight_neg (lam x : ℝ) : temperedTWeight lam (-x) = temperedTWeight lam x := by
  simp only [temperedTWeight, abs_neg]

/-- The tempered kernel `k_ν(x) · e^{-|x|/lam}`: the t kernel damped by the symmetric
exponential. -/
noncomputable def temperedTKernel (ν lam x : ℝ) : ℝ :=
  studentTKernel ν x * temperedTWeight lam x

lemma temperedTKernel_pos (hν : 0 < ν) (lam : ℝ) (x : ℝ) : 0 < temperedTKernel ν lam x :=
  mul_pos (studentTKernel_pos hν x) (temperedTWeight_pos lam x)

lemma studentTKernel_neg (ν x : ℝ) : studentTKernel ν (-x) = studentTKernel ν x := by
  simp only [studentTKernel, neg_sq]

lemma temperedTKernel_neg (ν lam x : ℝ) : temperedTKernel ν lam (-x) = temperedTKernel ν lam x := by
  simp only [temperedTKernel, temperedTWeight_neg, studentTKernel, neg_sq]

/-- The tempering weight is continuous in `x` for every value of the parameter. -/
lemma continuous_temperedTWeight (lam : ℝ) : Continuous (temperedTWeight lam) :=
  Real.continuous_exp.comp (continuous_abs.neg.div_const lam)

lemma continuous_temperedTKernel (hν : 0 < ν) (lam : ℝ) : Continuous (temperedTKernel ν lam) :=
  (continuous_studentTKernel hν).mul (continuous_temperedTWeight lam)

/-- The tempered kernel is integrable: it is dominated by the t kernel, whose tails it
only damps further. -/
lemma integrable_temperedTKernel (hν : 0 < ν) (hlam : 0 < lam) : Integrable (temperedTKernel ν lam) := by
  have h : ∀ x : ℝ, ‖temperedTKernel ν lam x‖ ≤ studentTKernel ν x := by
    intro x
    rw [norm_of_nonneg (temperedTKernel_pos hν lam x).le, temperedTKernel]
    exact (mul_le_mul_of_nonneg_left (temperedTWeight_le_one hlam x)
      (studentTKernel_pos hν x).le).trans_eq (mul_one _)
  exact (integrable_studentTKernel hν).mono'
    (continuous_temperedTKernel hν lam).aestronglyMeasurable (ae_of_all (μ := volume) h)

/-- The normalizing constant `Z_{ν,lam} = ∫ k_ν(x) e^{-|x|/lam} dx`. -/
noncomputable def temperedTNormConst (ν lam : ℝ) : ℝ := ∫ x, temperedTKernel ν lam x

lemma temperedTNormConst_pos (hν : 0 < ν) (hlam : 0 < lam) : 0 < temperedTNormConst ν lam :=
  (integral_pos_iff_support_of_nonneg (fun x ↦ (temperedTKernel_pos hν lam x).le)
    (integrable_temperedTKernel hν hlam)).2 <| by
    rw [Function.support_eq_univ fun x ↦ (temperedTKernel_pos hν lam x).ne']
    simp

lemma temperedTNormConst_le (hν : 0 < ν) (hlam : 0 < lam) :
    temperedTNormConst ν lam ≤ studentTNormConst ν := by
  have key := setIntegral_mono_ae (μ := volume) (s := Set.univ)
    (integrable_temperedTKernel hν hlam).integrableOn
    (integrable_studentTKernel hν).integrableOn
    (ae_of_all (μ := volume) fun x : ℝ ↦
      (mul_le_mul_of_nonneg_left (temperedTWeight_le_one hlam x)
        (studentTKernel_pos hν x).le).trans_eq (mul_one _))
  simpa only [setIntegral_univ, temperedTNormConst, studentTNormConst] using key

/-! ### The density and the law -/

/-- The tempered Student-t density `g_{ν,lam}(x) = k_ν(x) e^{-|x|/lam} / Z_{ν,lam}`. -/
noncomputable def temperedTPDFReal (ν lam x : ℝ) : ℝ :=
  temperedTKernel ν lam x / temperedTNormConst ν lam

/-- The tempered Student-t density as an `ℝ≥0∞`-valued function. -/
noncomputable def temperedTPDF (ν lam x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (temperedTPDFReal ν lam x)

lemma temperedTPDFReal_pos (hν : 0 < ν) (hlam : 0 < lam) (x : ℝ) :
    0 < temperedTPDFReal ν lam x :=
  div_pos (temperedTKernel_pos hν lam x) (temperedTNormConst_pos hν hlam)

lemma temperedTPDFReal_neg (ν lam x : ℝ) :
    temperedTPDFReal ν lam (-x) = temperedTPDFReal ν lam x := by
  simp only [temperedTPDFReal, temperedTKernel_neg]

lemma integrable_temperedTPDFReal (hν : 0 < ν) (hlam : 0 < lam) :
    Integrable (temperedTPDFReal ν lam) :=
  (integrable_temperedTKernel hν hlam).div_const _

lemma integral_temperedTPDFReal (hν : 0 < ν) (hlam : 0 < lam) :
    ∫ x, temperedTPDFReal ν lam x = 1 := by
  simp only [temperedTPDFReal, integral_div]
  exact div_self (temperedTNormConst_pos hν hlam).ne'

lemma lintegral_temperedTPDF (hν : 0 < ν) (hlam : 0 < lam) : ∫⁻ x, temperedTPDF ν lam x = 1 := by
  simp only [temperedTPDF]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_temperedTPDFReal hν hlam)
    (ae_of_all _ fun x ↦ (temperedTPDFReal_pos hν hlam x).le),
    integral_temperedTPDFReal hν hlam, ENNReal.ofReal_one]

/-- The **tempered Student-t law** with `ν` degrees of freedom and tempering `lam`. -/
noncomputable def temperedTMeasure (ν lam : ℝ) : Measure ℝ :=
  volume.withDensity (temperedTPDF ν lam)

lemma isProbabilityMeasure_temperedTMeasure (hν : 0 < ν) (hlam : 0 < lam) :
    IsProbabilityMeasure (temperedTMeasure ν lam) :=
  ⟨by rw [temperedTMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_temperedTPDF hν hlam]⟩

@[fun_prop]
lemma measurable_temperedTWeight (lam : ℝ) : Measurable (temperedTWeight lam) :=
  (continuous_temperedTWeight lam).measurable

@[fun_prop]
lemma measurable_temperedTKernel (ν lam : ℝ) : Measurable (temperedTKernel ν lam) := by
  have hk : Measurable (studentTKernel ν) := by
    unfold studentTKernel; fun_prop
  exact hk.mul (measurable_temperedTWeight lam)

@[fun_prop]
lemma measurable_temperedTPDFReal (ν lam : ℝ) : Measurable (temperedTPDFReal ν lam) :=
  (measurable_temperedTKernel ν lam).div measurable_const

@[fun_prop]
lemma measurable_temperedTPDF (ν lam : ℝ) : Measurable (temperedTPDF ν lam) :=
  (measurable_temperedTPDFReal ν lam).ennreal_ofReal

/-! ### Eventual dominance: the exponential beats the polynomial kernel -/

/-- **Eventual dominance.** For every `θ > 0` the exponential `e^{θ·|x|}` eventually
dominates the Student-t kernel's polynomial decay: `e^{θ·|x|} · k_ν(x) ≥ 1` for all
large enough `x`. The analytic input is that a power times a decaying exponential
tends to zero (`Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`). -/
lemma eventually_one_le_exp_mul_studentTKernel (hν : 0 < ν) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ x in atTop, (1 : ℝ) ≤ Real.exp (θ * |x|) * studentTKernel ν x := by
  set p : ℝ := (ν + 1) / 2 with hpdef
  set C : ℝ := (2 / ν) ^ p with hCdef
  have hp : (0 : ℝ) ≤ p := by linarith
  have hsq : ∀ᶠ x : ℝ in atTop, 1 + x ^ 2 / ν ≤ (2 / ν) * x ^ 2 := by
    filter_upwards [eventually_gt_atTop (√ν)] with x hx
    have h1 : √ν ≤ x := le_of_lt hx
    have h2 : (0 : ℝ) ≤ x := (Real.sqrt_nonneg ν).trans h1
    have h3 : (√ν) ^ 2 ≤ x ^ 2 := by
      calc (√ν) ^ 2 = √ν * √ν := pow_two _
        _ ≤ x * x := mul_le_mul h1 h1 (Real.sqrt_nonneg ν) h2
        _ = x ^ 2 := (pow_two x).symm
    rw [Real.sq_sqrt hν.le] at h3
    have hge : (1 : ℝ) ≤ x ^ 2 / ν := (one_le_div hν).2 h3
    have hsplit : (2 / ν) * x ^ 2 = x ^ 2 / ν + x ^ 2 / ν := by field_simp; ring
    rw [hsplit]
    linarith
  have hbound : ∀ᶠ x : ℝ in atTop,
      (1 + x ^ 2 / ν) ^ p ≤ C * (x ^ 2) ^ p := by
    filter_upwards [hsq] with x hx
    have hx0 : (0 : ℝ) ≤ 1 + x ^ 2 / ν := by positivity
    calc (1 + x ^ 2 / ν) ^ p ≤ ((2 / ν) * x ^ 2) ^ p := Real.rpow_le_rpow hx0 hx hp
      _ = (2 / ν) ^ p * (x ^ 2) ^ p := Real.mul_rpow (by positivity) (by positivity)
  have hmain := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * p) θ hθ
  have hT : Tendsto (fun x : ℝ => (1 + x ^ 2 / ν) ^ p * Real.exp (-(θ * x))) atTop (𝓝 0) := by
    refine squeeze_zero'
      (g := fun x => C * (x ^ (2 * p) * Real.exp (-(θ * x))))
      (Filter.Eventually.of_forall fun x => by positivity) ?_ ?_
    · filter_upwards [hbound, eventually_gt_atTop 0] with x hxle hx0
      have heq : (x ^ 2) ^ p = x ^ (2 * p) := by
        rw [show 2 * p = p + p from by ring, Real.rpow_add hx0, pow_two x]
        exact Real.mul_rpow hx0.le hx0.le
      rw [heq] at hxle
      rw [← mul_assoc]
      exact mul_le_mul hxle le_rfl (Real.exp_pos _).le (by positivity)
    · simpa using hmain.const_mul C
  filter_upwards [hT.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 0] with x hx hx0
  have hpos : (0 : ℝ) ≤ 1 + x ^ 2 / ν := by positivity
  rw [abs_of_nonneg hx0, studentTKernel, show -(ν + 1) / 2 = -p from by ring,
    Real.rpow_neg hpos]
  have hE : Real.exp (θ * x) = (Real.exp (-(θ * x)))⁻¹ := by
    rw [← Real.exp_neg, neg_neg]
  have hrew : Real.exp (θ * x) * ((1 + x ^ 2 / ν) ^ p)⁻¹
      = (Real.exp (-(θ * x)) * (1 + x ^ 2 / ν) ^ p)⁻¹ := by
    rw [hE, mul_inv]
  rw [hrew]
  have hle : Real.exp (-(θ * x)) * (1 + x ^ 2 / ν) ^ p ≤ (1 : ℝ) := by
    rw [mul_comm]
    exact le_of_lt hx
  exact one_le_inv_iff₀.2 ⟨by positivity, hle⟩

/-- If a nonnegative integrand exceeds a positive constant on a right half-line, its
lower integral against Lebesgue volume is infinite. -/
lemma lintegral_eq_top_of_ge_on_Ici {f : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ 0) (B : ℝ)
    (hf : ∀ x ∈ Set.Ici B, c ≤ f x) : ∫⁻ x, f x ∂volume = ⊤ := by
  have h1 : (∫⁻ x, Set.indicator (Set.Ici B) (fun _ => c) x ∂volume) ≤ (∫⁻ x, f x ∂volume) := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Set.Ici B
    · simpa [Set.indicator_of_mem, hx] using hf x hx
    · simp [Set.indicator_of_notMem, hx]
  have h2 : (∫⁻ x, Set.indicator (Set.Ici B) (fun _ => c) x ∂volume) = ⊤ := by
    rw [lintegral_indicator measurableSet_Ici, lintegral_const,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ici,
      ENNReal.mul_top hc]
  rw [h2] at h1
  exact le_antisymm le_top h1

/-- If a nonnegative integrand exceeds a positive constant on a left half-line, its
lower integral against Lebesgue volume is infinite. -/
lemma lintegral_eq_top_of_ge_on_Iic {f : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ 0) (B : ℝ)
    (hf : ∀ x ∈ Set.Iic B, c ≤ f x) : ∫⁻ x, f x ∂volume = ⊤ := by
  have h1 : (∫⁻ x, Set.indicator (Set.Iic B) (fun _ => c) x ∂volume) ≤ (∫⁻ x, f x ∂volume) := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Set.Iic B
    · simpa [Set.indicator_of_mem, hx] using hf x hx
    · simp [Set.indicator_of_notMem, hx]
  have h2 : (∫⁻ x, Set.indicator (Set.Iic B) (fun _ => c) x ∂volume) = ⊤ := by
    rw [lintegral_indicator measurableSet_Iic, lintegral_const,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Iic,
      ENNReal.mul_top hc]
  rw [h2] at h1
  exact le_antisymm le_top h1

/-- **Result 1 — ill-posedness of the naive extension.** Under the exact Student-t law
with any `ν > 0`, every nontrivial exponential moment is infinite: `E[e^{θX}] = ∞` for
every `θ ≠ 0`. The moment the Turnbull–Wakeman matcher needs does not exist at any
degrees of freedom, so the naive practice extension is not a well-posed pricing model.
Proof: the exponential `e^{θ·|x|}` eventually dominates the kernel's polynomial decay,
so the integrand exceeds a positive constant on a half-line of infinite volume. -/
theorem studentT_expMoment_eq_top (hν : 0 < ν) {θ : ℝ} (hθ : θ ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (θ * x)) ∂studentTMeasure ν = ⊤ := by
  have hC := studentTNormConst_pos hν
  have hkey : ∀ u : ℝ, (1 : ℝ) ≤ Real.exp (θ * u) * studentTKernel ν u →
      ENNReal.ofReal ((studentTNormConst ν)⁻¹)
        ≤ ENNReal.ofReal (Real.exp (θ * u) * studentTPDFReal ν u) := by
    intro u hu
    refine ENNReal.ofReal_le_ofReal ?_
    rw [studentTPDFReal]
    have hid : Real.exp (θ * u) * (studentTKernel ν u / studentTNormConst ν)
        * studentTNormConst ν = Real.exp (θ * u) * studentTKernel ν u := by
      field_simp
    have hstep : (1 : ℝ) / studentTNormConst ν
        ≤ Real.exp (θ * u) * (studentTKernel ν u / studentTNormConst ν) := by
      rw [div_le_iff₀ hC, hid]
      exact hu
    rwa [inv_eq_one_div]
  have hgrw : ∀ x : ℝ, (studentTPDF ν * fun y => ENNReal.ofReal (Real.exp (θ * y))) x
      = ENNReal.ofReal (Real.exp (θ * x) * studentTPDFReal ν x) := by
    intro x
    rw [Pi.mul_apply, studentTPDF, mul_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [studentTMeasure,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_studentTPDF ν)
      (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))),
    lintegral_congr hgrw]
  rcases lt_or_gt_of_ne hθ with hθn | hθp
  · obtain ⟨B, hB⟩ := eventually_atTop.mp
      (eventually_one_le_exp_mul_studentTKernel hν (neg_pos.2 hθn))
    have hM0 : (0 : ℝ) ≤ max B 0 := le_max_right B 0
    have hcne : ENNReal.ofReal ((studentTNormConst ν)⁻¹) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.2 hC
    refine lintegral_eq_top_of_ge_on_Iic hcne (-(max B 0)) ?_
    intro x hx
    have hxle : x ≤ -(max B 0) := hx
    have hx0 : x ≤ 0 := hxle.trans (neg_nonpos.2 hM0)
    have h1 : (1 : ℝ) ≤ Real.exp (θ * x) * studentTKernel ν x := by
      have hBx := hB (-x) ((le_max_left B 0).trans (by linarith))
      rw [abs_neg, abs_of_nonpos hx0, studentTKernel_neg,
        show (-θ) * (-x) = θ * x from by ring] at hBx
      exact hBx
    exact hkey x h1
  · obtain ⟨B, hB⟩ := eventually_atTop.mp
      (eventually_one_le_exp_mul_studentTKernel hν hθp)
    have hM0 : (0 : ℝ) ≤ max B 0 := le_max_right B 0
    have hcne : ENNReal.ofReal ((studentTNormConst ν)⁻¹) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact inv_pos.2 hC
    refine lintegral_eq_top_of_ge_on_Ici hcne (max B 0) ?_
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hM0.trans hx
    have h1 : (1 : ℝ) ≤ Real.exp (θ * x) * studentTKernel ν x := by
      have hBx := hB x ((le_max_left B 0).trans hx)
      rwa [abs_of_nonneg hx0] at hBx
    exact hkey x h1
/-! ### The well-posedness strip -/

/-- Pointwise strip bound: for `|θ| ≤ 1/λ` the tempering dominates the exponential
everywhere, `e^{θx} e^{-|x|/λ} ≤ 1`. -/
lemma exp_mul_temperedTWeight_le_one (_hlam : 0 < lam) {θ : ℝ} (h : |θ| ≤ 1 / lam)
    (x : ℝ) : Real.exp (θ * x) * temperedTWeight lam x ≤ 1 := by
  have hrew : Real.exp (θ * x) * temperedTWeight lam x
      = Real.exp (θ * x + -(1 / lam) * |x|) := by
    rw [temperedTWeight, div_eq_inv_mul, ← one_div, ← Real.exp_add]
    ring_nf
  rw [hrew, Real.exp_le_one_iff]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have h1 : θ * x ≤ (1 / lam) * x := mul_le_mul_of_nonneg_right (abs_le.mp h).2 hx
    linarith
  · rw [abs_of_nonpos hx]
    have h1 : θ * x ≤ (-1 / lam) * x := by
      have hmul : x * θ ≤ x * -(1 / lam) := mul_le_mul_of_nonpos_left (abs_le.mp h).left hx
      have e1 : x * θ = θ * x := mul_comm x θ
      have e2 : x * -(1 / lam) = (-1 / lam) * x := by ring
      linarith
    have h2 : (-1 / lam) * x = (1 / lam) * (-x) := by ring
    linarith

/-- **Divergence bookend — the strip edge is sharp.** Strictly outside the strip,
`1/λ < |θ|`, the tempered law again has `E[e^{θX}] = ∞`: the surviving decay
`e^{-(|θ| - 1/λ)|x|}` loses to the polynomial kernel. -/
theorem temperedT_expMoment_eq_top (hν : 0 < ν) (hlam : 0 < lam) {θ : ℝ}
    (h : 1 / lam < |θ|) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (θ * x)) ∂temperedTMeasure ν lam = ⊤ := by
  have hZ := temperedTNormConst_pos hν hlam
  have hgrw : ∀ x : ℝ, (temperedTPDF ν lam * fun y => ENNReal.ofReal (Real.exp (θ * y))) x
      = ENNReal.ofReal (Real.exp (θ * x) * temperedTPDFReal ν lam x) := by
    intro x
    rw [Pi.mul_apply, temperedTPDF, mul_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [temperedTMeasure,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_temperedTPDF ν lam)
      (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))),
    lintegral_congr hgrw]
  have hcne : ENNReal.ofReal ((temperedTNormConst ν lam)⁻¹) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 hZ
  have hθne : θ ≠ 0 := by
    intro h0
    rw [h0] at h
    simp only [abs_zero] at h
    exact absurd h (not_lt.2 (le_of_lt (one_div_pos.2 hlam)))
  rcases lt_or_gt_of_ne hθne with hθn | hθp
  · -- `θ < -1/λ`, left tail
    have habs : |θ| = -θ := abs_of_neg hθn
    have hδ : 0 < -θ - 1 / lam := by rw [← habs]; linarith
    obtain ⟨B, hB⟩ := eventually_atTop.mp
      (eventually_one_le_exp_mul_studentTKernel hν hδ)
    have hM0 : (0 : ℝ) ≤ max B 0 := le_max_right B 0
    refine lintegral_eq_top_of_ge_on_Iic hcne (-(max B 0)) ?_
    intro x hx
    have hxle : x ≤ -(max B 0) := hx
    have hx0 : x ≤ 0 := hxle.trans (neg_nonpos.2 hM0)
    have h1 : (1 : ℝ) ≤ Real.exp ((-θ - 1 / lam) * |x|) * studentTKernel ν x := by
      have hBx := hB (-x) ((le_max_left B 0).trans (by linarith))
      rw [abs_neg, abs_of_nonpos hx0, studentTKernel_neg,
        show (-θ - 1 / lam) * (-x) = (-θ - 1 / lam) * |x| from by
          rw [abs_of_nonpos hx0]] at hBx
      exact hBx
    refine ENNReal.ofReal_le_ofReal ?_
    rw [temperedTPDFReal]
    have hw : temperedTWeight lam x = Real.exp ((1 / lam) * x) := by
      rw [temperedTWeight, abs_of_nonpos hx0]
      have hbr : (-(-x)) / lam = (1 / lam) * x := by field_simp
      rw [hbr]
    have hz : Real.exp (θ * x) * temperedTKernel ν lam x
        = Real.exp ((-θ - 1 / lam) * |x|) * studentTKernel ν x := by
      rw [temperedTKernel, hw, mul_left_comm, ← Real.exp_add, abs_of_nonpos hx0, mul_comm]
      ring_nf
    have hid : Real.exp (θ * x) * (temperedTKernel ν lam x / temperedTNormConst ν lam)
        * temperedTNormConst ν lam
        = Real.exp ((-θ - 1 / lam) * |x|) * studentTKernel ν x := by
      rw [mul_div_assoc' _ _ _, hz, div_mul_cancel₀ _ hZ.ne']
    have hstep : (1 : ℝ) / temperedTNormConst ν lam
        ≤ Real.exp (θ * x) * (temperedTKernel ν lam x / temperedTNormConst ν lam) := by
      rw [div_le_iff₀ hZ, hid]
      exact h1
    rwa [inv_eq_one_div]
  · -- `1/λ < θ`, right tail
    have habs : |θ| = θ := abs_of_pos hθp
    have hδ : 0 < θ - 1 / lam := by rw [← habs]; linarith
    obtain ⟨B, hB⟩ := eventually_atTop.mp
      (eventually_one_le_exp_mul_studentTKernel hν hδ)
    have hM0 : (0 : ℝ) ≤ max B 0 := le_max_right B 0
    refine lintegral_eq_top_of_ge_on_Ici hcne (max B 0) ?_
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hM0.trans hx
    have h1 : (1 : ℝ) ≤ Real.exp ((θ - 1 / lam) * x) * studentTKernel ν x := by
      have hBx := hB x ((le_max_left B 0).trans hx)
      rwa [abs_of_nonneg hx0] at hBx
    refine ENNReal.ofReal_le_ofReal ?_
    rw [temperedTPDFReal]
    have hw : temperedTWeight lam x = Real.exp (-(1 / lam) * x) := by
      rw [temperedTWeight, abs_of_nonneg hx0]
      have hbr : (-x) / lam = -(1 / lam) * x := by field_simp
      rw [hbr]
    have hz : Real.exp (θ * x) * temperedTKernel ν lam x
        = Real.exp ((θ - 1 / lam) * x) * studentTKernel ν x := by
      rw [temperedTKernel, hw, mul_left_comm, ← Real.exp_add, sub_mul]
      ring_nf
    have hid : Real.exp (θ * x) * (temperedTKernel ν lam x / temperedTNormConst ν lam)
        * temperedTNormConst ν lam
        = Real.exp ((θ - 1 / lam) * x) * studentTKernel ν x := by
      rw [mul_div_assoc' _ _ _, hz, div_mul_cancel₀ _ hZ.ne']
    have hstep : (1 : ℝ) / temperedTNormConst ν lam
        ≤ Real.exp (θ * x) * (temperedTKernel ν lam x / temperedTNormConst ν lam) := by
      rw [div_le_iff₀ hZ, hid]
      exact h1
    rwa [inv_eq_one_div]

/-- **Finiteness bookend.** On the closed strip `|θ| ≤ 1/λ` the exponential moment
integrates: the integrand is dominated by the t kernel itself. The boundary belongs to
the finite side — at `|θ| = 1/λ` the surviving decay is the polynomial t tail,
integrable at every `ν > 0`. -/
lemma integrable_exp_mul_temperedTPDFReal (hν : 0 < ν) (hlam : 0 < lam) {θ : ℝ}
    (h : |θ| ≤ 1 / lam) :
    Integrable fun x => Real.exp (θ * x) * temperedTPDFReal ν lam x := by
  have hZ := temperedTNormConst_pos hν hlam
  have hbound : ∀ x : ℝ, ‖Real.exp (θ * x) * temperedTPDFReal ν lam x‖ ≤
      (temperedTNormConst ν lam)⁻¹ * studentTKernel ν x := by
    intro x
    have hnn : (0 : ℝ) ≤ Real.exp (θ * x) * temperedTPDFReal ν lam x :=
      mul_nonneg (Real.exp_pos _).le (temperedTPDFReal_pos hν hlam x).le
    have h1 : Real.exp (θ * x) * temperedTKernel ν lam x ≤ studentTKernel ν x := by
      rw [temperedTKernel, mul_left_comm]
      exact (mul_le_mul_of_nonneg_left (exp_mul_temperedTWeight_le_one hlam h x)
        (studentTKernel_pos hν x).le).trans_eq (mul_one _)
    have h2 : Real.exp (θ * x) * (temperedTKernel ν lam x / temperedTNormConst ν lam)
        ≤ studentTKernel ν x / temperedTNormConst ν lam := by
      rw [mul_div_assoc' _ _ _, div_le_div_iff₀ hZ hZ]
      exact mul_le_mul_of_nonneg_right h1 hZ.le
    rw [norm_of_nonneg hnn, temperedTPDFReal]
    calc Real.exp (θ * x) * (temperedTKernel ν lam x / temperedTNormConst ν lam)
        ≤ studentTKernel ν x / temperedTNormConst ν lam := h2
      _ = (temperedTNormConst ν lam)⁻¹ * studentTKernel ν x := by
          rw [div_eq_inv_mul, mul_comm]
  exact ((integrable_studentTKernel hν).const_mul _).mono'
    (by fun_prop) (ae_of_all (μ := volume) hbound)

/-- On the strip the exponential moment is strictly positive — the integrand is
positive everywhere. -/
lemma temperedT_expMoment_pos (hν : 0 < ν) (hlam : 0 < lam) {θ : ℝ} (h : |θ| ≤ 1 / lam) :
    0 < ∫ x, Real.exp (θ * x) * temperedTPDFReal ν lam x :=
  (integral_pos_iff_support_of_nonneg
    (fun x => mul_nonneg (Real.exp_pos _).le (temperedTPDFReal_pos hν hlam x).le)
    (integrable_exp_mul_temperedTPDFReal hν hlam h)).2 <| by
    rw [Function.support_eq_univ fun x =>
      (mul_pos (Real.exp_pos _) (temperedTPDFReal_pos hν hlam x)).ne']
    simp

/-! ### The exponential moment as a definition -/

/-- The tempered-t exponential moment `m(θ) = E[e^{θX}]`, in density form. Finite and
positive on the closed strip `|θ| ≤ 1/λ` (`integrable_exp_mul_temperedTPDFReal`,
`temperedExpMoment_pos`), infinite strictly outside it
(`temperedT_expMoment_eq_top`). -/
noncomputable def temperedExpMoment (ν lam θ : ℝ) : ℝ :=
  ∫ x, Real.exp (θ * x) * temperedTPDFReal ν lam x

lemma temperedExpMoment_pos (hν : 0 < ν) (hlam : 0 < lam) {θ : ℝ} (h : |θ| ≤ 1 / lam) :
    0 < temperedExpMoment ν lam θ := temperedT_expMoment_pos hν hlam h

/-- The exponential moment against the law equals the density form. -/
lemma integral_exp_temperedTMeasure_eq (hν : 0 < ν) (hlam : 0 < lam) (θ : ℝ) :
    (∫ x, Real.exp (θ * x) ∂temperedTMeasure ν lam) = temperedExpMoment ν lam θ := by
  have hgrw : ∀ x : ℝ, (temperedTPDF ν lam * fun y => ENNReal.ofReal (Real.exp (θ * y))) x
      = ENNReal.ofReal (temperedTPDFReal ν lam x * Real.exp (θ * x)) := by
    intro x
    rw [Pi.mul_apply, temperedTPDF, ← ENNReal.ofReal_mul (temperedTPDFReal_pos hν hlam x).le]
  rw [temperedTMeasure,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le)
      (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul volume (measurable_temperedTPDF ν lam)
      (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))),
    lintegral_congr hgrw, temperedExpMoment,
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x =>
        mul_nonneg (Real.exp_pos (θ * x)).le (temperedTPDFReal_pos hν hlam x).le)
      (by fun_prop)]
  congr 1
  exact lintegral_congr fun x => by rw [mul_comm]

/-- Evaluation of the exponential moment for any `HasLaw` copy of the tempered law. -/
lemma integral_exp_comp_eq_temperedExpMoment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hν : 0 < ν) (hlam : 0 < lam)
    (hX : HasLaw X (temperedTMeasure ν lam) P) (θ : ℝ) :
    (∫ ω, Real.exp (θ * X ω) ∂P) = temperedExpMoment ν lam θ := by
  rw [← integral_exp_temperedTMeasure_eq hν hlam θ, ← hX.map_eq,
    integral_map hX.aemeasurable (by fun_prop)]

end MathFin
