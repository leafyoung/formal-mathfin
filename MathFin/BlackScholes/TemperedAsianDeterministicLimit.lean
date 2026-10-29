/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.NormalTail
public import MathFin.Foundations.NormalQuantile
public import MathFin.BlackScholes.GarmanNormalForm
public import MathFin.BlackScholes.TemperedAsianMoments

/-!
# The deterministic limit of the Turnbull–Wakeman ansatz (B2.5)

The QuantLib #2954 consistency limit, proven on our own engine's math
(`TemperedAsianMoments.lean`'s `twEffVol` / `twLognormalAnsatzPrice`, priced
through `bsVGarman`): as the variance of the matched lognormal degenerates to
zero — `E[A²] ↓ E[A]²` from the admissible side — the TW price converges to the
discounted deterministic payoff `DF · (E[A] − K)⁺`, and the greek convention at
the kink is the `N(d₁) = 1/2` midpoint. Limit algebra only; no new probability.

## The two degenerate regimes (keep them apart)

* **Exact substitution `σ = 0`** (`bsVGarman_zero_vol`,
  `twLognormalAnsatzPrice_eq_of_eq_moments`): Lean's division-by-zero convention
  collapses `d₁ = d₂ = 0`, so `Φ(d₁) = Φ(d₂) = 1/2` at *every* moneyness and the
  ansatz evaluates to the midpoint `(DF·E[A] − K·DF)/2`. This is the kink
  convention applied unconditionally — it equals the intrinsic value only at the
  kink `DF·E[A] = K·DF` itself. It mirrors QuantLib's `BlackCalculator`
  convention `N(d₁) = 1/2` at the ATM kink (`bsVGarman` is used unchanged; the
  convention is disclosed here, not altered).
* **Right limit `σ ↓ 0`** (`tendsto_bsVGarman_zero_vol`,
  `tendsto_twLognormalAnsatzPrice`): the genuine limit is the discounted
  deterministic payoff `max (A − K·DF) 0` at *every* moneyness — ITM the price
  tends to the discounted forward intrinsic, OTM to zero, and at the kink the
  midpoint limit `(A − K·DF)/2 = 0` agrees with the intrinsic. This is the value
  the post-#2954 QuantLib engine returns in the zero-variance state, and the
  lemma family here is the formal consistency obligation: the degenerate-state
  output is the unique continuous extension of the engine's main branch.

`twEffVol_zero_of_eq_moments` is the bridge: `E[A²] = E[A]²` forces the matched
effective volatility to `0` (no condition on `T`; at `E[A] = 0` the junk-value
conventions `log 0 = 0`, `0 / 0 = 0` give the same answer).

## The greek convention at the kink

`tendsto_Phi_gbsd1_at_the_money`: at `E[A] = K`, `d₁ → 0` and `Φ(d₁) → 1/2` as
`σ ↓ 0` — the consistent delta convention `DF · (∂E[A]/∂S) · 1/2` in the TW
chain rule (the matched-`σ` delta is `DF · Φ(d₁) · ∂E[A]/∂S`). QuantLib's
`BlackCalculator` hard-codes exactly this `0.5` at the ATM kink.

## Scope (disclosed)

The law-level degeneration — `λ ↓ 0` in the tempered family collapses the law to
a point mass, so `E[A²] → E[A]²` through `integral_temperedAsianSq_eq` — is NOT
formalized here: it needs uniform integrability of `e^{θX_λ}` in `λ`, which is
new probability/analysis and outside B2.5's "limit algebra only" scope. The
limit theorems below take the moment degeneration `EA2 ↓ EA²` as their
hypothesis-side limit, which composes with any future law-level convergence.

## Main results

* `bsVGarman_zero_vol`: `bsVGarman A K DF 0 T = (A − K·DF)/2` (exact `σ = 0`
  substitution; the kink convention, disclosed above).
* `twEffVol_zero_of_eq_moments`: `E[A²] = E[A]² → twEffVol = 0`.
* `twLognormalAnsatzPrice_eq_of_eq_moments`: at matched degenerate moments the
  ansatz price is the midpoint `(DF·EA − K·DF)/2`.
* `tendsto_bsVGarman_zero_vol`: `σ ↓ 0⁺` drives the Garman-normal price to
  `max (A − K·DF) 0`.
* `tendsto_twEffVol`: `EA2 ↓ (EA²)⁺` drives the matched effective volatility
  to `0⁺`.
* `tendsto_twLognormalAnsatzPrice`: `EA2 ↓ (EA²)⁺` drives the TW price to
  `DF · max (EA − K) 0` — the #2954 consistency limit.
* `tendsto_Phi_gbsd1_at_the_money`: the ATM kink convention `Φ(d₁) → 1/2`.
-/

@[expose] public section

namespace MathFin

open Real Filter Topology

/-! ### Private helpers: divergence and degenerate-algebra primitives -/

/-- `σ ↦ σ·√T` tends to `0` on the right of `0`, for every value of `T`
(continuity at `0`; no sign condition needed). -/
private lemma tendsto_sqrtT_nhdsGT_zero (T : ℝ) :
    Tendsto (fun σ : ℝ => σ * Real.sqrt T) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : ContinuousAt (fun σ : ℝ => σ * Real.sqrt T) 0 :=
    (continuous_id.mul continuous_const).continuousAt
  simpa using hc.continuousWithinAt.tendsto

/-- The σ-quadratic share of `d₁`: `(σ²T/2)/(σ√T) = σ√T/2` off `σ = 0`
(with `T ≥ 0`). -/
private lemma sq_div_sqrt_eq_half (σ T : ℝ) (hd : σ * Real.sqrt T ≠ 0)
    (hT : 0 ≤ T) : σ ^ 2 * T / 2 / (σ * Real.sqrt T) = σ * Real.sqrt T / 2 := by
  have hcal : σ * Real.sqrt T / 2 * (σ * Real.sqrt T) = σ ^ 2 * T / 2 := by
    rw [show σ * Real.sqrt T / 2 * (σ * Real.sqrt T)
          = σ * σ * (Real.sqrt T * Real.sqrt T) / 2 from by ring,
      Real.mul_self_sqrt hT]
    ring
  rw [div_eq_iff hd, hcal]

/-- A positive constant divided by `σ·b` diverges to `+∞` as `σ ↓ 0⁺`. -/
private lemma tendsto_div_mul_nhdsGT_zero_atTop {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun σ : ℝ => a / (σ * b)) (𝓝[>] (0:ℝ)) atTop := by
  have hfun : (fun σ : ℝ => (a / b) * σ⁻¹) =ᶠ[𝓝[>] 0] fun σ : ℝ => a / (σ * b) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have : σ ≠ 0 := ne_of_gt hσ
    field_simp
  exact Tendsto.congr' hfun
    (tendsto_const_nhds.pos_mul_atTop (div_pos ha hb) tendsto_inv_nhdsGT_zero)

/-- A negative constant divided by `σ·b` diverges to `−∞` as `σ ↓ 0⁺`. -/
private lemma tendsto_div_mul_nhdsGT_zero_atBot {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    Tendsto (fun σ : ℝ => a / (σ * b)) (𝓝[>] (0:ℝ)) atBot := by
  have hfun : (fun σ : ℝ => -((-a) / (σ * b))) =ᶠ[𝓝[>] 0] fun σ : ℝ => a / (σ * b) := by
    filter_upwards [self_mem_nhdsWithin] with σ _hσ
    rw [neg_div, neg_neg]
  exact Tendsto.congr' hfun
    (tendsto_neg_atTop_atBot.comp (tendsto_div_mul_nhdsGT_zero_atTop (neg_pos.2 ha) hb))

/-! ### The exact `σ = 0` substitution: the kink midpoint -/

/-- **The exact `σ = 0` substitution in the Garman normal form is the kink
midpoint.** At zero volatility, Lean's division-by-zero convention collapses
`d₁ = d₂ = 0`, so `Φ(d₁) = Φ(d₂) = Φ(0) = 1/2` and `bsVGarman A K DF 0 T =
(A − K·DF)/2` — at *every* moneyness, with no side conditions on the
parameters. This is QuantLib's `BlackCalculator` ATM convention `N(d₁) = 1/2`
applied unconditionally: it agrees with the discounted intrinsic
`max (A − K·DF) 0` only at the kink `A = K·DF` itself; off the kink the
intrinsic is attained as the right limit `σ ↓ 0` (`tendsto_bsVGarman_zero_vol`),
not by the exact substitution. `bsVGarman` is consumed unchanged — the
convention is disclosed here, not altered. -/
theorem bsVGarman_zero_vol (A K DF T : ℝ) :
    bsVGarman A K DF 0 T = (A - K * DF) / 2 := by
  have h1 : gbsd1 A K DF 0 T = 0 := by
    simp [gbsd1, div_zero]
  have h2 : gbsd2 A K DF 0 T = 0 := by
    simp [gbsd2, h1]
  unfold bsVGarman
  rw [h1, h2, Phi_zero]
  ring

/-- **Degenerate moments force zero effective volatility.** If `EA2 = EA²` then
`twEffVol EA EA2 T = 0`, for every value of `T` (the `T` cancels: the argument
is `√(log 1 / T) = √0`). At `EA = 0` the junk-value conventions `0 / 0 = 0`,
`log 0 = 0` give the same answer, so no side condition is needed. On the
admissible TW domain (`EA > 0`, `EA2 ≥ EA²`) this is the variance-free
statement: a degenerate second moment makes the moment-matched volatility
vanish. -/
theorem twEffVol_zero_of_eq_moments (EA EA2 T : ℝ) (heq : EA2 = EA ^ 2) :
    twEffVol EA EA2 T = 0 := by
  have hlog : Real.log (EA ^ 2 / EA ^ 2) = 0 := by
    rw [Real.log_eq_zero]
    rcases eq_or_ne EA 0 with hEA | hEA
    · exact Or.inl (by simp [hEA])
    · exact Or.inr (Or.inl (div_self (pow_ne_zero 2 hEA)))
  unfold twEffVol
  rw [heq, hlog, zero_div, Real.sqrt_zero]

/-- **The degenerate-moment price is the midpoint, not the intrinsic.** At
`EA2 = EA²` the matched volatility is `0` (`twEffVol_zero_of_eq_moments`) and
the TW ansatz price evaluates — through `bsVGarman`'s own zero-vol behavior
(`bsVGarman_zero_vol`) — to `(DF·EA − K·DF)/2`: `Φ(d₁) = Φ(d₂) = 1/2` at all
moneyness, with no side conditions. **Disclosed convention**: this is the
kink/midpoint value; it equals the discounted deterministic payoff
`DF · max (EA − K) 0` only at the kink `EA = K`. Off the kink, the
deterministic payoff is the right limit as `EA2 ↓ EA²`
(`tendsto_twLognormalAnsatzPrice`) — the consistency requirement QuantLib PR
#2954 imposed on the C++ engine's zero-variance branch. -/
theorem twLognormalAnsatzPrice_eq_of_eq_moments (EA EA2 K DF T : ℝ)
    (heq : EA2 = EA ^ 2) :
    twLognormalAnsatzPrice EA EA2 K DF T = (DF * EA - K * DF) / 2 := by
  unfold twLognormalAnsatzPrice
  rw [twEffVol_zero_of_eq_moments EA EA2 T heq, bsVGarman_zero_vol]

/-! ### The right limit `σ ↓ 0`: the deterministic payoff -/

/-- At the kink `A = K·DF` (log-moneyness `0`), `d₁ = σ√T/2 → 0` as `σ ↓ 0⁺`. -/
private lemma tendsto_gbsd1_at_the_money (K DF T : ℝ) (hK : 0 < K) (hDF : 0 < DF)
    (hT : 0 < T) :
    Tendsto (fun σ => gbsd1 (K * DF) K DF σ T) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hlog : Real.log (K * DF / (K * DF)) = 0 := by
    rw [div_self (mul_ne_zero hK.ne' hDF.ne'), Real.log_one]
  have hev : (fun σ : ℝ => σ * Real.sqrt T / 2) =ᶠ[𝓝[>] 0]
      fun σ => gbsd1 (K * DF) K DF σ T := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hd : σ * Real.sqrt T ≠ 0 := (mul_pos hσ (Real.sqrt_pos.2 hT)).ne'
    change σ * Real.sqrt T / 2
        = (Real.log (K * DF / (K * DF)) + σ ^ 2 * T / 2) / (σ * Real.sqrt T)
    rw [hlog, zero_add, sq_div_sqrt_eq_half σ T hd hT.le]
  have hsT : Tendsto (fun σ : ℝ => σ * Real.sqrt T / 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (tendsto_sqrtT_nhdsGT_zero T).div_const 2
  exact Tendsto.congr' hev hsT

/-- At the kink `A = K·DF`, `d₂ = −σ√T/2 → 0` as `σ ↓ 0⁺`. -/
private lemma tendsto_gbsd2_at_the_money (K DF T : ℝ) (hK : 0 < K) (hDF : 0 < DF)
    (hT : 0 < T) :
    Tendsto (fun σ => gbsd2 (K * DF) K DF σ T) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hlog : Real.log (K * DF / (K * DF)) = 0 := by
    rw [div_self (mul_ne_zero hK.ne' hDF.ne'), Real.log_one]
  have hev : (fun σ : ℝ => -(σ * Real.sqrt T / 2)) =ᶠ[𝓝[>] 0]
      fun σ => gbsd2 (K * DF) K DF σ T := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hd : σ * Real.sqrt T ≠ 0 := (mul_pos hσ (Real.sqrt_pos.2 hT)).ne'
    change -(σ * Real.sqrt T / 2)
        = (Real.log (K * DF / (K * DF)) + σ ^ 2 * T / 2) / (σ * Real.sqrt T)
        - σ * Real.sqrt T
    rw [hlog, zero_add, sq_div_sqrt_eq_half σ T hd hT.le]
    ring
  have hsT : Tendsto (fun σ : ℝ => σ * Real.sqrt T / 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (tendsto_sqrtT_nhdsGT_zero T).div_const 2
  exact Tendsto.congr' hev (by simpa using hsT.neg)

/-- **The `σ ↓ 0⁺` limit of the Garman normal form is the discounted intrinsic
`max (A − K·DF) 0`.** This is the QuantLib #2954 consistency limit on the
closed form itself: ITM (`K·DF < A`) the log-moneyness term dominates `d₁`, `d₂`
and both diverge to `+∞`, so the price tends to `A − K·DF`; OTM (`A < K·DF`)
both dive to `−∞` and the price tends to `0`; at the kink (`A = K·DF`)
`d₁ = σ√T/2 → 0` and `d₂ = −σ√T/2 → 0`, so the price tends to the midpoint
`(A − K·DF)/2 = 0`, which *is* the intrinsic there. Every branch lands on
`max (A − K·DF) 0` — the degenerate-state output that makes the price the
continuous extension of its own main branch. Contrast `bsVGarman_zero_vol`:
the exact substitution gives the midpoint at all moneyness; only the limit
recovers the intrinsic everywhere. -/
theorem tendsto_bsVGarman_zero_vol (A K DF T : ℝ) (hA : 0 < A) (hK : 0 < K)
    (hDF : 0 < DF) (hT : 0 < T) :
    Tendsto (fun σ => bsVGarman A K DF σ T) (𝓝[>] (0:ℝ)) (𝓝 (max (A - K * DF) 0)) := by
  have hKD : 0 < K * DF := mul_pos hK hDF
  rcases lt_trichotomy A (K * DF) with hlt | heq | hgt
  · -- OTM (`A < K·DF`): `d₁`, `d₂` → −∞, price → 0
    have hclog : Real.log (A / (K * DF)) < 0 :=
      Real.log_neg (div_pos hA hKD) ((div_lt_one hKD).2 hlt)
    have hsT0 : Tendsto (fun σ : ℝ => σ * Real.sqrt T) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_sqrtT_nhdsGT_zero T
    have hev : (fun σ : ℝ => Real.log (A / (K * DF)) / (σ * Real.sqrt T)
        + σ * Real.sqrt T / 2) =ᶠ[𝓝[>] 0] fun σ => gbsd1 A K DF σ T := by
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hd : σ * Real.sqrt T ≠ 0 := (mul_pos hσ (Real.sqrt_pos.2 hT)).ne'
      change Real.log (A / (K * DF)) / (σ * Real.sqrt T) + σ * Real.sqrt T / 2
          = (Real.log (A / (K * DF)) + σ ^ 2 * T / 2) / (σ * Real.sqrt T)
      rw [← sq_div_sqrt_eq_half σ T hd hT.le]
      field_simp
    have hsum : Tendsto (fun σ : ℝ => Real.log (A / (K * DF)) / (σ * Real.sqrt T)
        + σ * Real.sqrt T / 2) (𝓝[>] (0:ℝ)) atBot := by
      rw [tendsto_atBot]
      intro M
      filter_upwards [(tendsto_atBot.1
          (tendsto_div_mul_nhdsGT_zero_atBot hclog (Real.sqrt_pos.2 hT)) (M - 1)),
        hsT0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 2))] with σ h1 h2
      linarith
    have ht1 : Tendsto (fun σ => gbsd1 A K DF σ T) (𝓝[>] (0:ℝ)) atBot :=
      Tendsto.congr' hev hsum
    have ht2 : Tendsto (fun σ => gbsd2 A K DF σ T) (𝓝[>] (0:ℝ)) atBot := by
      rw [tendsto_atBot]
      intro M
      filter_upwards [(tendsto_atBot.1 ht1 (M - 1)), self_mem_nhdsWithin] with σ h1 hσ
      have h2 : (0:ℝ) < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.2 hT)
      change gbsd2 A K DF σ T ≤ M
      rw [show gbsd2 A K DF σ T = gbsd1 A K DF σ T - σ * Real.sqrt T from rfl]
      linarith
    have tP1 : Tendsto (fun σ => Phi (gbsd1 A K DF σ T)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_Phi_atBot.comp ht1
    have tP2 : Tendsto (fun σ => Phi (gbsd2 A K DF σ T)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_Phi_atBot.comp ht2
    have hprice : Tendsto (fun σ => bsVGarman A K DF σ T) (𝓝[>] (0:ℝ))
        (𝓝 (A * 0 - K * DF * 0)) :=
      (tP1.const_mul A).sub (tP2.const_mul (K * DF))
    rw [max_eq_right (sub_nonpos.2 hlt.le)]
    simpa using hprice
  · -- kink (`A = K·DF`): `d₁`, `d₂` → 0, price → midpoint = intrinsic = 0
    subst heq
    have tP1 : Tendsto (fun σ => Phi (gbsd1 (K * DF) K DF σ T)) (𝓝[>] (0:ℝ))
        (𝓝 (1 / 2)) := by
      have h := (continuous_Phi.continuousAt.tendsto).comp
        (tendsto_gbsd1_at_the_money K DF T hK hDF hT)
      rwa [Phi_zero] at h
    have tP2 : Tendsto (fun σ => Phi (gbsd2 (K * DF) K DF σ T)) (𝓝[>] (0:ℝ))
        (𝓝 (1 / 2)) := by
      have h := (continuous_Phi.continuousAt.tendsto).comp
        (tendsto_gbsd2_at_the_money K DF T hK hDF hT)
      rwa [Phi_zero] at h
    have hprice : Tendsto (fun σ => bsVGarman (K * DF) K DF σ T) (𝓝[>] (0:ℝ))
        (𝓝 (K * DF * (1 / 2) - K * DF * (1 / 2))) :=
      (tP1.const_mul (K * DF)).sub (tP2.const_mul (K * DF))
    simpa using hprice
  · -- ITM (`K·DF < A`): `d₁`, `d₂` → +∞, price → A − K·DF
    have hclog : 0 < Real.log (A / (K * DF)) := Real.log_pos ((one_lt_div hKD).2 hgt)
    have hsT0 : Tendsto (fun σ : ℝ => σ * Real.sqrt T) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_sqrtT_nhdsGT_zero T
    have ht1 : Tendsto (fun σ => gbsd1 A K DF σ T) (𝓝[>] (0:ℝ)) atTop := by
      refine tendsto_atTop_mono' _ ?_
        (tendsto_div_mul_nhdsGT_zero_atTop hclog (Real.sqrt_pos.2 hT))
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hd : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.2 hT)
      change Real.log (A / (K * DF)) / (σ * Real.sqrt T) ≤ gbsd1 A K DF σ T
      rw [show gbsd1 A K DF σ T
            = (Real.log (A / (K * DF)) + σ ^ 2 * T / 2) / (σ * Real.sqrt T) from rfl,
        div_le_div_iff₀ hd hd, add_mul]
      have hqD : (0:ℝ) ≤ σ ^ 2 * T / 2 * (σ * Real.sqrt T) :=
        mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg σ) hT.le) (by norm_num)) hd.le
      linarith
    have ht2 : Tendsto (fun σ => gbsd2 A K DF σ T) (𝓝[>] (0:ℝ)) atTop := by
      rw [tendsto_atTop]
      intro M
      filter_upwards [ht1.eventually_ge_atTop (M + 1),
        hsT0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with σ h1 h2
      change M ≤ gbsd2 A K DF σ T
      rw [show gbsd2 A K DF σ T = gbsd1 A K DF σ T - σ * Real.sqrt T from rfl]
      linarith
    have tP1 : Tendsto (fun σ => Phi (gbsd1 A K DF σ T)) (𝓝[>] (0:ℝ)) (𝓝 1) :=
      tendsto_Phi_atTop.comp ht1
    have tP2 : Tendsto (fun σ => Phi (gbsd2 A K DF σ T)) (𝓝[>] (0:ℝ)) (𝓝 1) :=
      tendsto_Phi_atTop.comp ht2
    have hprice : Tendsto (fun σ => bsVGarman A K DF σ T) (𝓝[>] (0:ℝ))
        (𝓝 (A * 1 - K * DF * 1)) :=
      (tP1.const_mul A).sub (tP2.const_mul (K * DF))
    rw [max_eq_left (sub_nonneg.2 hgt.le)]
    simpa using hprice

/-! ### The greek convention at the kink -/

/-- **The ATM kink convention `N(d₁) = 1/2` as the `σ ↓ 0⁺` limit.** At
`EA = K` (so the forward `DF·EA` equals the discounted strike `K·DF`),
`d₁ = σ√T/2 → 0` and `Φ(d₁) → Φ(0) = 1/2`. In the TW chain rule the
matched-`σ` delta is `DF · Φ(d₁) · ∂EA/∂S`, so the consistent kink delta is
`DF · (∂EA/∂S) · 1/2` — exactly the `0.5` QuantLib's `BlackCalculator`
hard-codes at the ATM kink, and what `bsVGarman`'s exact `σ = 0` substitution
computes (`bsVGarman_zero_vol`). Only the `Φ(d₁)` factor is formalized; the
chain-rule derivative itself is outside this file's limit-algebra scope. -/
theorem tendsto_Phi_gbsd1_at_the_money (EA K DF T : ℝ) (hEAK : EA = K) (hK : 0 < K)
    (hDF : 0 < DF) (hT : 0 < T) :
    Tendsto (fun σ => Phi (gbsd1 (DF * EA) K DF σ T)) (𝓝[>] (0:ℝ)) (𝓝 (1 / 2)) := by
  have hEq : DF * EA = K * DF := by rw [hEAK]; ring
  rw [hEq]
  have h := (continuous_Phi.continuousAt.tendsto).comp
    (tendsto_gbsd1_at_the_money K DF T hK hDF hT)
  rwa [Phi_zero] at h

/-! ### The B2.5 flagship: the moment-degeneration limit of the TW price -/

/-- **The matched effective volatility vanishes as the second moment
degenerates.** As `EA2 ↓ (EA²)⁺` from the admissible side (`EA2 > EA²`),
`twEffVol EA EA2 T → 0⁺`: the argument of the square root is
`log (EA2 / EA²) / T → 0` through positive values (positivity of `EA²` via
`EA ≠ 0` keeps the log's argument above `1` along the approach), so the limit
is taken inside the admissible cone rather than through junk values. This is
the σ-side bridge that turns any future moment-level convergence
`E[A²] → E[A]²` into a price statement via
`tendsto_twLognormalAnsatzPrice`. -/
theorem tendsto_twEffVol (EA T : ℝ) (hEA : EA ≠ 0) (hT : 0 < T) :
    Tendsto (fun EA2 => twEffVol EA EA2 T) (𝓝[>] (EA ^ 2)) (𝓝[>] (0:ℝ)) := by
  have hEAsq : 0 < EA ^ 2 := sq_pos_of_ne_zero hEA
  have hdiv : Tendsto (fun x : ℝ => x / EA ^ 2) (𝓝[>] (EA ^ 2)) (𝓝 1) := by
    have h2 : Tendsto (fun x : ℝ => x / EA ^ 2) (𝓝 (EA ^ 2)) (𝓝 ((EA ^ 2) / EA ^ 2)) :=
      (continuous_id.div_const (EA ^ 2)).tendsto _
    rw [div_self (pow_ne_zero 2 hEA)] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun x : ℝ => Real.log (x / EA ^ 2)) (𝓝[>] (EA ^ 2)) (𝓝 0) := by
    have hg : Tendsto Real.log (𝓝 1) (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (one_ne_zero)).tendsto
    rw [Real.log_one] at hg
    exact hg.comp hdiv
  have hval : Tendsto (fun x : ℝ => Real.log (x / EA ^ 2) / T) (𝓝[>] (EA ^ 2)) (𝓝 0) := by
    simpa using hlog.div_const T
  have hsq : Tendsto (fun y : ℝ => Real.sqrt y) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa using Real.continuous_sqrt.tendsto 0
  have hmain : Tendsto (fun x : ℝ => Real.sqrt (Real.log (x / EA ^ 2) / T))
      (𝓝[>] (EA ^ 2)) (𝓝 0) := hsq.comp hval
  have hpos : ∀ᶠ x in 𝓝[>] (EA ^ 2), 0 < Real.sqrt (Real.log (x / EA ^ 2) / T) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sqrt_pos.2 (div_pos (Real.log_pos ((one_lt_div hEAsq).2 hx)) hT)
  simp only [twEffVol]
  exact le_inf hmain (Filter.le_principal_iff.2 hpos)

/-- **The QuantLib #2954 consistency limit on the TW engine.** As the second
moment degenerates to the square of the first, `EA2 ↓ (EA²)⁺`, the
Turnbull–Wakeman moment-matched price converges to the discounted
deterministic payoff `DF · max (EA − K, 0)`. Composition of
`tendsto_twEffVol` (moment degeneration drives the matched `σ` to `0⁺`) with
`tendsto_bsVGarman_zero_vol` (the σ-limit of the Garman form is the discounted
intrinsic). This is the formal version of the obligation the FMGD framework
derives for degenerate states — the engine's zero-variance output must be the
continuous extension of its main pricing branch — proven here on our own
engine's math, with the moment degeneration taken as the hypothesis-side
limit (the law-level `λ ↓ 0` collapse of the tempered family needs new
probability; see the module docstring's Scope section). -/
theorem tendsto_twLognormalAnsatzPrice (EA K DF T : ℝ) (hEA : 0 < EA) (hK : 0 < K)
    (hDF : 0 < DF) (hT : 0 < T) :
    Tendsto (fun EA2 => twLognormalAnsatzPrice EA EA2 K DF T) (𝓝[>] (EA ^ 2))
      (𝓝 (DF * max (EA - K) 0)) := by
  have hcomp := (tendsto_bsVGarman_zero_vol (DF * EA) K DF T (mul_pos hDF hEA) hK hDF hT).comp
    (tendsto_twEffVol EA T hEA.ne' hT)
  have hval : max (DF * EA - K * DF) 0 = DF * max (EA - K) 0 := by
    rw [mul_max_of_nonneg (EA - K) 0 hDF.le, mul_zero]
    exact congrArg (fun z => max z 0) (by ring)
  rw [hval] at hcomp
  exact hcomp

end MathFin
