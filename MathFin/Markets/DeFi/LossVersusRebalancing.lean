/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedProcess
public import MathFin.Probability.Brownian.Ito.ItoProductRule
public import MathFin.Markets.DeFi.UniswapMechanics

/-!
# Loss-versus-rebalancing for a pool with a smooth value function

For a liquidity pool whose mark-to-market value is a function `V(P)` of a price `P` trading as a
geometric Brownian motion, the pool loses against a continuously rebalanced hedge at a rate
driven by the volatility and by the curvature of `V`: Lemma 2 and eq. (8) of Milionis, Moallemi,
Roughgarden and Zhang (2022). The price is built from its logarithm, `P_t = exp X_t`, with `X`
the library's `localItoProcess` (log-drift `b`, log-volatility `σ`): Itô's formula is applied to
`V ∘ exp`, which is twice differentiable on all of `ℝ` exactly when `V` is twice differentiable
on `(0, ∞)`. That is what a constant-product pool's value `V(P) = 2L√P` is, and why the
constant-product pool instantiates the general theorem directly — no derivative of `V` at `0` is
ever taken.

With `R_t` the value process of the paper's rebalancing strategy (`rebalancingValue`: start at
the pool value `V(P₀) = V (Real.exp x₀)`, then hold `x*(P_t) = V'(P_t)` units of the risky asset,
self-financing), the module proves, almost surely at every `t ∈ [0, T]` at once,

`V(P_t) = R_t + ½ ∫₀ᵗ σ_s² P_s² V''(P_s) ds`,

the Itô-correction term of the paper's eq. (31) against eq. (5). Equivalently
`R_t − V(P_t) = −½ ∫₀ᵗ σ_s² P_s² V''(P_s) ds`: the loss-versus-rebalancing process, which is
nonnegative whenever `V'' ≤ 0` on `(0, ∞)` — Lemma 1 Part 3, `V'' = x*′ ≤ 0`. The instantaneous
rate is `ℓ(σ, P) = −(σ²P²/2)·x*′(P)`. The text layer of the arXiv page renders eq. (8) without
the minus sign; the printed equation carries it, and the formula holds only as
`ℓ = −(σ²P²/2)·x*′(P)`: with Lemma 1.3 (`x*′(P) ≤ 0`) the rate is nonnegative, and eq. (19)
confirms the sign for the constant-product pool (`ℓ = (Lσ²/4)·√P ≥ 0`). That is the sign proved
here.

For the constant-product pool (`V(P) = 2L√P`, Example 3, eq. (19)), the specialization reads
`R_t − V(P_t) = (σ²/4)·L·∫₀ᵗ √P_s ds = (σ²/8)·∫₀ᵗ V(P_s) ds`: the paper's loss of `σ²/8` of
pool value per unit time, as an identity of processes (a drift of a process difference, not a
number).

## Relation to impermanent loss

The library's `impermanentLoss` (`Markets/DeFi/UniswapMechanics.lean`) compares the pool
against holding the initial reserves — the paper's "loss-versus-holding", whose nonnegativity
(Proposition 1 of §8) is the library's `impermanentLoss_nonpos` — while `R_t` rebalances
continuously and is self-financing. `losses_nonneg` proves both benchmarks nonnegative along
the same GBM price. No identity between the two losses is proved here, and the source proves
none: its §8 shows the benchmarks behave differently, loss-versus-holding not being cumulative
over subintervals while the loss proved here is a nonnegative time integral.

## Main definitions

* `rebalancingValue`: the value process `R_t` of the rebalancing strategy, in the library's
  log-price construction.

## Main results

* `poolValue_eq_rebalancingValue_add_correction`: the decomposition of the pool value into the
  rebalancing value plus the Itô correction `½∫σ²P²V''`.
* `rebalancingValue_sub_poolValue_eq_lvr`: the same identity as the difference, the
  loss-versus-rebalancing process as a time integral of the instantaneous rate
  `−½σ²P²V''(P)`.
* `lvr_nonneg`: the loss is nonnegative for a concave value function.
* `losses_nonneg`: for the constant-product pool, the loss against the rebalancing strategy
  and the static `impermanentLoss` at the realized price factor are both nonnegative — the two
  benchmarks of the paper's §8, with no identity between them.
* `lvr_constantProduct`: the constant-product pool loses `(σ²/4)·L·∫₀ᵗ √P_s ds`.
* `lvr_constantProduct_eq_sigma_sq_over_eight`: the same loss as
  `(σ²/8)·∫₀ᵗ V(P_s) ds`.

## References

* [J. Milionis, C. C. Moallemi, T. Roughgarden and A. L. Zhang, *Automated market making and
  loss-versus-rebalancing*][MilionisMoallemiRoughgardenZhang2022], §2–5 (Lemma 1, Lemma 2,
  eq. (8)), Example 3 (eq. (19)), §8

## Tags

loss-versus-rebalancing, LVR, automated market maker, constant product, liquidity provider,
impermanent loss, Itô correction, MSC 91G80, JEL G23
-/

@[expose] public section

namespace MathFin

namespace DeFi

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralProcessContinuousModification
open ItoIntegralLocalised ItoFormulaAdapted
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {σ b : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {b : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) (x₀ : ℝ)
  {V V' V'' : ℝ → ℝ}

/-- The hedge holding `x*(P) = V'(P)` read on the log price, `x ↦ Real.exp x · V'(Real.exp x)`,
is continuous on all of `ℝ`. Public because the value process of the rebalancing strategy needs
it in its own definition. -/
theorem continuous_rebalancingHolding (hv' : ∀ p > 0, HasDerivAt V' (V'' p) p) :
    Continuous fun x ↦ Real.exp x * V' (Real.exp x) :=
  Differentiable.continuous fun x ↦
    ((Real.hasDerivAt_exp x).mul (HasDerivAt.comp x (hv' (Real.exp x) (Real.exp_pos x))
      (Real.hasDerivAt_exp x))).differentiableAt

/-! ### The rebalancing strategy and the LVR identity -/

/-- The value process `R_t` of the rebalancing strategy (eq. (5) of the source): start at the
pool value `V (Real.exp x₀) = V(P₀)` and hold `x*(P_t) = V'(P_t)` units of the risky asset,
self-financing. In the library's construction the price is `P_t = Real.exp X_t` with the log
price `X = localItoProcess x₀ b σ`, so `dP = P(b + ½σ²)ds + PσdB` and the self-financing value
is the initial value, plus the cash leg's drift integral `∫ x*(P)·P·(b + ½σ²) ds`, plus the
risky leg's Itô integral of the integrand `x*(P)·P·σ` against `B`. What the module proves about
it: the pool value exceeds it by exactly `½ ∫₀ᵗ σ²P²V''(P) ds`
(`poolValue_eq_rebalancingValue_add_correction`). -/
noncomputable def rebalancingValue (V V' : ℝ → ℝ)
    (hpred : IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
            * V' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)))
          * σ s ω)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  V (Real.exp x₀)
    + ∫ (s : ℝ≥0) in Ioc 0 t,
        (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
            * V' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)))
          * (b s ω + 1 / 2 * σ s ω ^ 2) ∂timeMeasure
    + predItoIntegral (μ := μ) T hBmeas hpred t ω

/-- **The loss-versus-rebalancing decomposition** (the source's eq. (31) against eq. (5)): the
pool value exceeds the rebalancing value by exactly half the volatility-weighted curvature
integral. Almost surely, for every `t ∈ [0, T]` at once,

`V(P_t) = R_t + ½ ∫₀ᵗ σ_s² P_s² V''(P_s) ds`,

where `P_t = Real.exp (localItoProcess …)` is the price and `R_t` the rebalancing value. The
hypotheses on `V` are the Itô formula's, carried by `V ∘ exp` and so restricted to `(0, ∞)`,
where the price lives; nothing at `P = 0` is assumed. -/
theorem poolValue_eq_rebalancingValue_add_correction
    (hv : ∀ p > 0, HasDerivAt V (V' p) p) (hv' : ∀ p > 0, HasDerivAt V' (V'' p) p)
    (hv''_cont : ContinuousOn V'' (Ioi 0)) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      V (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω))
        = rebalancingValue T hBmeas hadap hcont x₀ V V'
            (itoIntegrand_isStronglyPredictable hB T hBmeas hBcont hadap hcont hb_adap hb_cont
              x₀ (f_x := fun _ x ↦ Real.exp x * V' (Real.exp x))
              ((continuous_rebalancingHolding hv').comp continuous_snd)) t ω
          + 1 / 2 * ∫ (s : ℝ≥0) in Ioc 0 t,
              σ s ω ^ 2
                * Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) ^ 2
                * V'' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω))
              ∂timeMeasure := by
  have hlpv : ∀ x : ℝ, HasDerivAt (fun x ↦ V (Real.exp x))
      (Real.exp x * V' (Real.exp x)) x := fun x ↦
    (HasDerivAt.comp x (hv (Real.exp x) (Real.exp_pos x)) (Real.hasDerivAt_exp x)).congr_deriv
      (mul_comm _ _)
  have hlphmul : ∀ x : ℝ, HasDerivAt (fun x ↦ Real.exp x * V' (Real.exp x))
      (Real.exp x ^ 2 * V'' (Real.exp x) + Real.exp x * V' (Real.exp x)) x := fun x ↦ by
    have h := (Real.hasDerivAt_exp x).mul (HasDerivAt.comp x
      (hv' (Real.exp x) (Real.exp_pos x)) (Real.hasDerivAt_exp x))
    rw [Pi.mul_def, Function.comp_apply] at h
    have h2 : HasDerivAt (fun x ↦ Real.exp x * V' (Real.exp x))
        (Real.exp x ^ 2 * V'' (Real.exp x) + Real.exp x * V' (Real.exp x)) x :=
      h.congr_deriv (by ring)
    exact h2
  have hcontsq : Continuous fun x ↦ Real.exp x ^ 2 * V'' (Real.exp x)
      + Real.exp x * V' (Real.exp x) := by
    have hV''comp : Continuous fun x ↦ V'' (Real.exp x) :=
      hv''_cont.comp_continuous Real.continuous_exp fun x ↦ mem_Ioi.2 (Real.exp_pos x)
    have hV'c : ContinuousOn V' (Ioi 0) :=
      DifferentiableOn.continuousOn fun p hp ↦
        (hv' p hp).differentiableAt.differentiableWithinAt
    have h2 : Continuous fun x ↦ V' (Real.exp x) :=
      hV'c.comp_continuous Real.continuous_exp fun x ↦ mem_Ioi.2 (Real.exp_pos x)
    exact ((Real.continuous_exp.pow 2).mul hV''comp).add (Real.continuous_exp.mul h2)
  have hito := ito_formula_adapted_unbounded_C2_process hB T hBmeas hBcont hadap hcont hb_adap
    hb_cont x₀
    (f := fun x ↦ V (Real.exp x)) (f' := fun x ↦ Real.exp x * V' (Real.exp x))
    (f'' := fun x ↦ Real.exp x ^ 2 * V'' (Real.exp x) + Real.exp x * V' (Real.exp x))
    hlpv hlphmul hcontsq
  have hX := ae_continuousOn_localItoProcess hB T hBmeas hBcont hadap hcont hb_cont x₀
  filter_upwards [hito, hX] with ω hω hXc t ht
  have hXct : ContinuousOn (fun s : ℝ≥0 ↦ localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b
      s ω) (Icc 0 t) := hXc.mono fun s hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
  have hcontHedge : ContinuousOn (fun s : ℝ≥0 ↦
      (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
          * V' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)))
        * (b s ω + 1 / 2 * σ s ω ^ 2)) (Icc 0 t) :=
    ((continuous_rebalancingHolding hv').comp_continuousOn hXct).mul
      (((hb_cont ω).continuousOn.add
        (((hcont ω).continuousOn.pow 2).const_mul (1 / 2))).mono fun s hs ↦ hs)
  have hσ2 : ContinuousOn (fun s : ℝ≥0 ↦ σ s ω ^ 2) (Icc 0 t) :=
    (hcont ω).continuousOn.pow 2
  have hexp2 : ContinuousOn (fun s : ℝ≥0 ↦
      Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) ^ 2) (Icc 0 t) :=
    (Real.continuous_exp.pow 2).comp_continuousOn hXct
  have hV2 : ContinuousOn (fun s : ℝ≥0 ↦
      V'' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω))) (Icc 0 t) :=
    (hv''_cont.comp_continuous Real.continuous_exp
      fun x ↦ mem_Ioi.2 (Real.exp_pos x)).comp_continuousOn hXct
  have hcontCorr : ContinuousOn (fun s : ℝ≥0 ↦ σ s ω ^ 2
      * Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) ^ 2
      * V'' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω))) (Icc 0 t) :=
    (hσ2.mul hexp2).mul hV2
  have hintHedge := integrableOn_Ioc_of_continuousOn hcontHedge
  have hintCorr := integrableOn_Ioc_of_continuousOn hcontCorr
  have hintCorrHalf : IntegrableOn (fun s : ℝ≥0 ↦
      1 / 2 * (σ s ω ^ 2 * Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) ^ 2
        * V'' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)))) (Ioc 0 t)
      timeMeasure := hintCorr.const_mul (1 / 2)
  have hstep := hω t ht
  beta_reduce at hstep
  have hpred : predItoIntegral (μ := μ) T hBmeas
        (itoIntegrand_isStronglyPredictable hB T hBmeas hBcont hadap hcont hb_adap hb_cont x₀
          (f_x := fun _ x ↦ Real.exp x * V' (Real.exp x))
          ((continuous_rebalancingHolding hv').comp continuous_snd)) t ω
      = predItoIntegral (μ := μ) T hBmeas
        (itoIntegrand_isStronglyPredictable hB T hBmeas hBcont hadap hcont hb_adap hb_cont x₀
          (f_x := fun _ x ↦ Real.exp x * V' (Real.exp x))
          ((Differentiable.continuous fun x ↦
              (hlphmul x).differentiableAt).comp continuous_snd)) t ω :=
    congrArg (fun h ↦ predItoIntegral (μ := μ) T hBmeas h t ω) (proof_irrel _ _)
  have hcongr : ∀ s ∈ Ioc 0 t,
      Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
          * V' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)) * b s ω
        + 1 / 2 * ((Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) ^ 2
              * V'' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω))
            + Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
              * V' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)))
            * σ s ω ^ 2)
      = (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)
          * V' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)))
        * (b s ω + 1 / 2 * σ s ω ^ 2)
        + 1 / 2 * (σ s ω ^ 2
          * Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) ^ 2
          * V'' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω))) := by
    intro s _
    ring
  rw [rebalancingValue, hpred, hstep,
    setIntegral_congr_fun measurableSet_Ioc hcongr,
    integral_add hintHedge hintCorrHalf, integral_const_mul]
  ring


/-- **The loss-versus-rebalancing process** (the source's eq. (6) with Lemma 2's eq. (7)): the
rebalancing value exceeds the pool value by exactly the time integral of the instantaneous rate
`−½·σ²P²V''(P)`, the paper's `ℓ(σ, P) = −(σ²P²/2)·x*′(P)` under Lemma 1 Part 3 (`x*′ = V''`).
Almost surely, at every `t ∈ [0, T]` at once. -/
theorem rebalancingValue_sub_poolValue_eq_lvr
    (hv : ∀ p > 0, HasDerivAt V (V' p) p) (hv' : ∀ p > 0, HasDerivAt V' (V'' p) p)
    (hv''_cont : ContinuousOn V'' (Ioi 0)) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      rebalancingValue T hBmeas hadap hcont x₀ V V'
          (itoIntegrand_isStronglyPredictable hB T hBmeas hBcont hadap hcont hb_adap hb_cont
            x₀ (f_x := fun _ x ↦ Real.exp x * V' (Real.exp x))
            ((continuous_rebalancingHolding hv').comp continuous_snd)) t ω
        - V (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω))
        = -(1 / 2 * ∫ (s : ℝ≥0) in Ioc 0 t,
            σ s ω ^ 2 * Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) ^ 2
              * V'' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω))
            ∂timeMeasure) := by
  have h := poolValue_eq_rebalancingValue_add_correction hB T hBmeas hBcont hadap hcont hb_adap
    hb_cont x₀ hv hv' hv''_cont
  filter_upwards [h] with ω h t ht
  rw [h t ht]
  ring

/-- **The loss is nonnegative** (Lemma 2's "ℓ(σ, P) is always positive", on the concavity of
Lemma 1 Part 3): whenever `V'' ≤ 0` on `(0, ∞)`, the pool never runs ahead of the rebalancing
strategy. Almost surely, at every `t ∈ [0, T]` at once. -/
theorem lvr_nonneg (hv : ∀ p > 0, HasDerivAt V (V' p) p) (hv' : ∀ p > 0, HasDerivAt V' (V'' p) p)
    (hv''_cont : ContinuousOn V'' (Ioi 0)) (hv''_nonpos : ∀ p > 0, V'' p ≤ 0) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      0 ≤ rebalancingValue T hBmeas hadap hcont x₀ V V'
          (itoIntegrand_isStronglyPredictable hB T hBmeas hBcont hadap hcont hb_adap hb_cont
            x₀ (f_x := fun _ x ↦ Real.exp x * V' (Real.exp x))
            ((continuous_rebalancingHolding hv').comp continuous_snd)) t ω
        - V (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω)) := by
  have h := rebalancingValue_sub_poolValue_eq_lvr hB T hBmeas hBcont hadap hcont hb_adap hb_cont
    x₀ hv hv' hv''_cont
  filter_upwards [h] with ω h t ht
  rw [h t ht]
  have hle : ∫ (s : ℝ≥0) in Ioc 0 t,
      σ s ω ^ 2 * Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) ^ 2
        * V'' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω))
      ∂timeMeasure ≤ 0 := by
    have hpos : (0 : ℝ) ≤ ∫ (s : ℝ≥0) in Ioc 0 t,
        -(σ s ω ^ 2
            * Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω) ^ 2
          * V'' (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω)))
        ∂timeMeasure :=
      setIntegral_nonneg measurableSet_Ioc (fun s (_ : s ∈ Ioc 0 t) ↦ neg_nonneg.mpr
        (mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (sq_nonneg (σ s ω))
            (sq_nonneg (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω))))
          (hv''_nonpos (Real.exp (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω))
            (Real.exp_pos _))))
    rw [integral_neg] at hpos
    exact neg_nonneg.mp hpos
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hle)

/-! ### The constant-product pool -/

/-- The constant-product pool value as a function of the price `P` (Example 3, eq. (19) of the
source): `cpPoolValue L P = 2L√P`, where `L` is the pool's liquidity. Twice differentiable on
`(0, ∞)`; the derivative facts are `hasDerivAt_cpPoolValue`, `hasDerivAt_cpPoolHedge` and
`continuousOn_cpPoolCurvature`. -/
noncomputable def cpPoolValue (L : ℝ) : ℝ → ℝ := fun p ↦ 2 * L * Real.sqrt p

/-- The hedge holding of the constant-product pool: `x*(P) = V'(P) = L/√P` — the pool's own
reserve of X at price `P` (the source's Lemma 1 Part 2 at this pool). -/
noncomputable def cpPoolHedge (L : ℝ) : ℝ → ℝ := fun p ↦ L / Real.sqrt p

/-- The curvature of the constant-product pool value: `V''(P) = −L/(2·P·√P)`, which is
`x*′(P) ≤ 0` — the marginal liquidity of Lemma 1 Part 3 at this pool. -/
noncomputable def cpPoolCurvature (L : ℝ) : ℝ → ℝ := fun p ↦ -(L / (2 * (p * Real.sqrt p)))

theorem hasDerivAt_cpPoolValue (L p : ℝ) (hp : 0 < p) :
    HasDerivAt (cpPoolValue L) (cpPoolHedge L p) p := by
  have h0 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt p)) p := Real.hasDerivAt_sqrt hp.ne'
  have h1 : HasDerivAt (fun q : ℝ ↦ (2 * L) * Real.sqrt q)
      ((2 * L) * (1 / (2 * Real.sqrt p))) p := HasDerivAt.const_mul (2 * L) h0
  rw [show ((2 * L) * (1 / (2 * Real.sqrt p)) : ℝ) = cpPoolHedge L p by
    unfold cpPoolHedge
    field_simp] at h1
  exact h1

theorem hasDerivAt_cpPoolHedge (L p : ℝ) (hp : 0 < p) :
    HasDerivAt (cpPoolHedge L) (cpPoolCurvature L p) p := by
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
  have h0 : HasDerivAt (fun q : ℝ ↦ (L : ℝ) / Real.sqrt q)
      ((0 * Real.sqrt p - L * (1 / (2 * Real.sqrt p))) / Real.sqrt p ^ 2) p :=
    HasDerivAt.div (hasDerivAt_const (c := L) p) (Real.hasDerivAt_sqrt hp.ne')
      ((Real.sqrt_ne_zero').mpr hp)
  rw [hs] at h0
  rw [show ((0 * Real.sqrt p - L * (1 / (2 * Real.sqrt p))) / p : ℝ)
      = cpPoolCurvature L p by
    unfold cpPoolCurvature
    field_simp
    ring] at h0
  exact h0

/-- The constant-product curvature is nonpositive for a nonnegative liquidity `c`: the pool
value function is concave on `(0, ∞)` (the source's Lemma 1 Part 3). -/
private theorem cpPoolCurvature_nonpos {c : ℝ} (hc : 0 ≤ c) (p : ℝ) (hp : 0 < p) :
    cpPoolCurvature c p ≤ 0 := by
  unfold cpPoolCurvature
  exact neg_nonpos.mpr (div_nonneg hc (by positivity))

theorem continuousOn_cpPoolCurvature (L : ℝ) :
    ContinuousOn (cpPoolCurvature L) (Ioi 0) := by
  have hden : ContinuousOn (fun p : ℝ ↦ p * Real.sqrt p) (Ioi 0) :=
    (continuous_id.mul Real.continuous_sqrt).continuousOn
  have hinvmul : ContinuousOn (fun p : ℝ ↦ -(L / 2) * (p * Real.sqrt p)⁻¹) (Ioi 0) :=
    (ContinuousOn.inv₀ hden fun p hp ↦
      mul_ne_zero (ne_of_gt hp) ((Real.sqrt_ne_zero').mpr hp)).const_mul (-(L / 2))
  refine hinvmul.congr fun p (hp : p ∈ Ioi 0) ↦ ?_
  unfold cpPoolCurvature
  field_simp

/-- **Both loss benchmarks are nonnegative** (the source's Lemma 2 with Proposition 1 of §8):
for the constant-product pool `V(P) = 2L√P` along the GBM price, the loss against the
continuously rebalanced strategy and the static loss against holding the initial reserves
(`impermanentLoss` at the realized price factor, the paper's "loss-versus-holding") are both
nonnegative, almost surely at every `t ∈ [0, T]` at once. The benchmarks differ, and no
identity between the two losses is proved here. -/
theorem losses_nonneg {σ m c : ℝ} (hc : 0 ≤ c) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      0 ≤ rebalancingValue (σ := fun _ _ ↦ σ) (b := fun _ _ ↦ m - σ ^ 2 / 2) T hBmeas
          (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀ (cpPoolValue c)
          (cpPoolHedge c)
          (itoIntegrand_isStronglyPredictable (σ := fun _ _ ↦ σ)
            (b := fun _ _ ↦ m - σ ^ 2 / 2) hB T hBmeas hBcont
            (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
            (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
            (f_x := fun _ x ↦ Real.exp x * cpPoolHedge c (Real.exp x))
            ((continuous_rebalancingHolding (hasDerivAt_cpPoolHedge c)).comp continuous_snd))
          t ω
        - cpPoolValue c (Real.exp (localItoProcess (μ := μ) (σ := fun _ _ ↦ σ) T hBmeas
            (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
            (fun _ _ ↦ m - σ ^ 2 / 2) t ω))
        ∧ impermanentLoss (Real.exp (localItoProcess (μ := μ) (σ := fun _ _ ↦ σ) T hBmeas
            (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
            (fun _ _ ↦ m - σ ^ 2 / 2) t ω - x₀)) ≤ 0 := by
  have hdyn := lvr_nonneg hB T hBmeas hBcont (fun _ ↦ stronglyMeasurable_const)
    (fun _ ↦ continuous_const) (fun _ ↦ stronglyMeasurable_const)
    (fun _ ↦ continuous_const) x₀ (hasDerivAt_cpPoolValue c) (hasDerivAt_cpPoolHedge c)
    (continuousOn_cpPoolCurvature c) (cpPoolCurvature_nonpos hc)
    (σ := fun _ _ ↦ σ) (b := fun _ _ ↦ m - σ ^ 2 / 2)
  filter_upwards [hdyn] with ω hω t ht
  exact ⟨hω t ht, impermanentLoss_nonpos (Real.exp_nonneg _)⟩

/-- The pointwise curvature identity the constant-product specialization rests on:
`σ²·P²·V''(P) = −(σ²L/2)·√P` at `P = Real.exp x > 0`. -/
private theorem cpCurvature_pointwise {σ L x : ℝ} (hx : 0 < Real.exp x) :
    σ ^ 2 * Real.exp x ^ 2 * cpPoolCurvature L (Real.exp x)
      = -(σ ^ 2 * L / 2 * Real.sqrt (Real.exp x)) := by
  unfold cpPoolCurvature
  set S : ℝ := Real.sqrt (Real.exp x) with hS
  have hsq : S ^ 2 = Real.exp x := Real.sq_sqrt hx.le
  have hne : S ≠ 0 := by
    intro hs0
    exact hx.ne' (by rw [← hsq, hs0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  rw [← hsq]
  field_simp [hne]

/-- **The constant-product pool loses `σ²/8` of its value per unit time** (Lemma 2 at Example 3,
eq. (19) of the source): for the pool value `V(P) = 2L√P` and a price `P_t = Real.exp X_t` built
from the log price `X` with log-drift `m − σ²/2` and log-volatility `σ`, the rebalancing value
exceeds the pool value by `(σ²/4)·L·∫₀ᵗ √P_s ds`. Almost surely, at every `t ∈ [0, T]` at once.
The loss rate `(σ²/4)·L·√P_s = (σ²/8)·V(P_s)` is the paper's instantaneous LVR. -/
theorem lvr_constantProduct {σ m L : ℝ} :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      rebalancingValue (σ := fun _ _ ↦ σ) (b := fun _ _ ↦ m - σ ^ 2 / 2) T hBmeas
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀ (cpPoolValue L)
        (cpPoolHedge L)
        (itoIntegrand_isStronglyPredictable (σ := fun _ _ ↦ σ) (b := fun _ _ ↦ m - σ ^ 2 / 2)
          hB T hBmeas hBcont (fun _ ↦ stronglyMeasurable_const)
          (fun _ ↦ continuous_const) (fun _ ↦ stronglyMeasurable_const)
          (fun _ ↦ continuous_const) x₀ (f_x := fun _ x ↦ Real.exp x * cpPoolHedge L (Real.exp x))
          ((continuous_rebalancingHolding (hasDerivAt_cpPoolHedge L)).comp continuous_snd))
        t ω
        - cpPoolValue L (Real.exp (localItoProcess (μ := μ) (σ := fun _ _ ↦ σ) T hBmeas
            (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
            (fun _ _ ↦ m - σ ^ 2 / 2) t ω))
        = σ ^ 2 / 4 * L * ∫ (s : ℝ≥0) in Ioc 0 t,
            Real.sqrt (Real.exp (localItoProcess (μ := μ) (σ := fun _ _ ↦ σ) T hBmeas
              (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
              (fun _ _ ↦ m - σ ^ 2 / 2) s ω)) ∂timeMeasure := by
  have hmain := poolValue_eq_rebalancingValue_add_correction hB T hBmeas hBcont
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
    (fun p hp ↦ hasDerivAt_cpPoolValue L p hp) (hasDerivAt_cpPoolHedge L)
    (continuousOn_cpPoolCurvature L) (σ := fun _ _ ↦ σ) (b := fun _ _ ↦ m - σ ^ 2 / 2)
  filter_upwards [hmain] with ω h t ht
  have hx (s : ℝ≥0) : 0 < Real.exp (localItoProcess (μ := μ) (σ := fun _ _ ↦ σ) T hBmeas
      (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
      (fun _ _ ↦ m - σ ^ 2 / 2) s ω) := Real.exp_pos _
  have hcongr : ∀ u ∈ Ioc 0 t, σ ^ 2
      * Real.exp (localItoProcess (μ := μ) (σ := fun _ _ ↦ σ) T hBmeas
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
        (fun _ _ ↦ m - σ ^ 2 / 2) u ω) ^ 2
      * cpPoolCurvature L (Real.exp (localItoProcess (μ := μ) (σ := fun _ _ ↦ σ) T hBmeas
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
        (fun _ _ ↦ m - σ ^ 2 / 2) u ω))
      = -(σ ^ 2 * L / 2 * Real.sqrt (Real.exp (localItoProcess (μ := μ) T hBmeas
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
        (fun _ _ ↦ m - σ ^ 2 / 2) u ω))) := fun u _ ↦ cpCurvature_pointwise (hx u)
  rw [h t ht, setIntegral_congr_fun measurableSet_Ioc hcongr, integral_neg, integral_const_mul]
  ring

/-- **The same loss as `σ²/8` of the pool value** (eq. (19)'s normalized form): for the
constant-product pool, `R_t − V(P_t) = (σ²/8)·∫₀ᵗ V(P_s) ds` — the loss grows at `σ²/8` of the
mark-to-market pool value per unit time. Almost surely, at every `t ∈ [0, T]` at once. -/
theorem lvr_constantProduct_eq_sigma_sq_over_eight {σ m L : ℝ} :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      rebalancingValue (σ := fun _ _ ↦ σ) (b := fun _ _ ↦ m - σ ^ 2 / 2) T hBmeas
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀ (cpPoolValue L)
        (cpPoolHedge L)
        (itoIntegrand_isStronglyPredictable (σ := fun _ _ ↦ σ) (b := fun _ _ ↦ m - σ ^ 2 / 2)
          hB T hBmeas hBcont (fun _ ↦ stronglyMeasurable_const)
          (fun _ ↦ continuous_const) (fun _ ↦ stronglyMeasurable_const)
          (fun _ ↦ continuous_const) x₀ (f_x := fun _ x ↦ Real.exp x * cpPoolHedge L (Real.exp x))
          ((continuous_rebalancingHolding (hasDerivAt_cpPoolHedge L)).comp continuous_snd))
        t ω
        - cpPoolValue L (Real.exp (localItoProcess (μ := μ) (σ := fun _ _ ↦ σ) T hBmeas
            (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
            (fun _ _ ↦ m - σ ^ 2 / 2) t ω))
        = σ ^ 2 / 8 * ∫ (s : ℝ≥0) in Ioc 0 t,
            cpPoolValue L (Real.exp (localItoProcess (μ := μ) (σ := fun _ _ ↦ σ) T hBmeas
              (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) x₀
              (fun _ _ ↦ m - σ ^ 2 / 2) s ω)) ∂timeMeasure := by
  filter_upwards [lvr_constantProduct hB T hBmeas hBcont x₀] with ω h t ht
  rw [h t ht]
  simp only [cpPoolValue, integral_const_mul]
  ring

end DeFi

end MathFin
