/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Credit.KMVMerton
public import MathFin.Risk.Credit.BernoulliMixture
public import MathFin.Risk.Credit.VasicekIRB

/-!
# The ends of the one-factor family, and the risk-neutral probability shift

The one-factor Gaussian threshold model of `Risk/Credit/BernoulliMixture.lean` has two
parameters, the default probability `π` and the asset correlation `ρ`, and two objects built on
them: the conditional default probability
`oneFactorPD π ρ f = Φ((Φ⁻¹(π) − √ρ f)/√(1 − ρ))` and the asymptotic single-risk-factor quantile
`asrfQuantile π ρ α = Φ((Φ⁻¹(π) + √ρ Φ⁻¹(α))/√(1 − ρ))`. This file proves the pointwise limits
of both objects as `ρ` and `π` reach the ends of their ranges, and the drift-shift identity that
relates the Merton–KMV default probability at the physical drift to the one at the risk-free
rate.

* **The independence end `ρ → 0`** (`oneFactorPD_tendsto_rho_zero`,
  `asrfQuantile_tendsto_rho_zero`): the conditional default probability tends to the constant
  `π` and the quantile to `π`. This is the law-of-large-numbers end: with vanishing asset
  correlation the portfolio loss is the constant `π`, which the paper reads as the loss
  distribution collapsing to a one-point distribution at `L = p` (Vasicek 2002, after eq. (5)).
* **The perfect-correlation end `ρ → 1`** (`oneFactorPD_tendsto_rho_one_lt`,
  `oneFactorPD_tendsto_rho_one_gt`, `oneFactorPD_tendsto_rho_one_eq`,
  `asrfQuantile_tendsto_rho_one_lt`, `asrfQuantile_tendsto_rho_one_gt`,
  `asrfQuantile_tendsto_rho_one_eq`): pointwise, `oneFactorPD π ρ f` tends to `1` on
  `f < Φ⁻¹(π)`, to `0` on `Φ⁻¹(π) < f`, and to `1/2` at the threshold `f = Φ⁻¹(π)`; the quantile
  tends to `1` when `1 − α < π`, to `0` when `π + α < 1`, and to `1/2` at `π + α = 1`. The
  conditional default probability becomes the indicator of the default scenario
  `{F < Φ⁻¹(π)}`, whose probability is `π`: the paper's zero-one loss distribution with
  probabilities `π` and `1 − π` (Vasicek 2002, after eq. (5)).
* **The default-probability ends** (`oneFactorPD_tendsto_pi_zero`,
  `oneFactorPD_tendsto_pi_one`, `asrfQuantile_tendsto_pi_zero`, `asrfQuantile_tendsto_pi_one`):
  as `π → 0` or `π → 1`, both objects collapse to `0` or `1` — the paper's loss distribution
  concentrated at `L = 0` and `L = 1` (Vasicek 2002, after eq. (5)).
* **The risk-neutral probability shift** (`kmvPD_eq_shift`,
  `kmvPD_eq_shift_of_physicalDefault`): the KMV-Merton default probability at the risk-free
  rate `r` is the one at the drift `m` displaced along the normal axis by `(m − r)√T/σ`:
  `kmvPD V₀ F r σ T = Φ(Φ⁻¹(kmvPD V₀ F m σ T) + (m − r)√T/σ)`. This is Vasicek's equation (6),
  `p* = N(N⁻¹(p) + λρ_M√T)`, whose displacement `λρ_M√T` — with `λ = (µ_M − r)/σ_M` the market
  price of risk and `ρ_M` the correlation of the firm asset value with the market — equals
  `(m − r)√T/σ` for a firm with drift `m`. The event form restates the physical side through
  the Brownian survival identification of `kmvPD`.

## Main results

* `oneFactorPD_tendsto_rho_zero`, `asrfQuantile_tendsto_rho_zero`: the `ρ → 0` end.
* `oneFactorPD_tendsto_rho_one_lt`, `oneFactorPD_tendsto_rho_one_gt`,
  `oneFactorPD_tendsto_rho_one_eq`, `asrfQuantile_tendsto_rho_one_lt`,
  `asrfQuantile_tendsto_rho_one_gt`, `asrfQuantile_tendsto_rho_one_eq`: the `ρ → 1` end.
* `oneFactorPD_tendsto_pi_zero`, `oneFactorPD_tendsto_pi_one`,
  `asrfQuantile_tendsto_pi_zero`, `asrfQuantile_tendsto_pi_one`: the `π` ends.
* `kmvPD_eq_shift`, `kmvPD_eq_shift_of_physicalDefault`: the risk-neutral probability shift.

## References

* [O. Vasicek, *Loan portfolio value*][Vasicek2002], equations (5)-(7)
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 24, equation (24.10)

The Hull text locates the worst-case default rate as equation (24.10); the printed forms of the
limits and of the shift are quoted from Vasicek (2002).

## Tags

one-factor model, Vasicek model, asset correlation, worst-case default rate, risk-neutral
default probability, distance to default, regulatory capital, MSC 91G40, MSC 60F15, JEL G28,
JEL G32, JEL G33
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology

/-! ### The normal quantile at the ends of its argument -/

/-- The standard normal CDF tends to `1` at `+∞`. -/
private lemma tendsto_Phi_atTop : Tendsto Phi atTop (𝓝 1) := by
  simpa only [cdf_gaussianReal_zero_one] using tendsto_cdf_atTop (μ := gaussianReal 0 1)

/-- The standard normal CDF tends to `0` at `−∞`. -/
private lemma tendsto_Phi_atBot : Tendsto Phi atBot (𝓝 0) := by
  simpa only [cdf_gaussianReal_zero_one] using tendsto_cdf_atBot (μ := gaussianReal 0 1)

/-- The normal quantile function tends to `−∞` as its argument approaches `0` from the right. -/
private lemma tendsto_PhiInv_atBot : Tendsto (fun p : ℝ => PhiInv p) (𝓝[Ioi 0] 0) atBot := by
  refine tendsto_atBot.2 fun M ↦ ?_
  have hΦ : 0 < Phi M := (Phi_mem_Ioo M).1
  have hΦ1 : Phi M < 1 := (Phi_mem_Ioo M).2
  have hmem : {p : ℝ | p ∈ Ioi 0 ∧ p ≤ Phi M} ∈ 𝓝[Ioi 0] 0 :=
    mem_nhdsWithin.2 ⟨Iio (Phi M), isOpen_Iio, mem_Iio.2 hΦ, fun p hp ↦ ⟨hp.2, hp.1.le⟩⟩
  filter_upwards [hmem] with p hp
  obtain ⟨hp0, hpΦ⟩ := hp
  have h01 : p ∈ Ioo 0 1 := ⟨hp0, lt_of_le_of_lt hpΦ hΦ1⟩
  exact le_of_not_gt fun h ↦ absurd ((PhiInv_le_iff h01).2 hpΦ) (not_le.2 h)

/-- The normal quantile function tends to `+∞` as its argument approaches `1` from the left. -/
private lemma tendsto_PhiInv_atTop : Tendsto (fun p : ℝ => PhiInv p) (𝓝[Iio 1] 1) atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  have hΦ : Phi M < 1 := (Phi_mem_Ioo M).2
  have hmem : {p : ℝ | p ∈ Iio 1 ∧ Phi M ≤ p} ∈ 𝓝[Iio 1] 1 :=
    mem_nhdsWithin.2 ⟨Ioi (Phi M), isOpen_Ioi, mem_Ioi.2 hΦ, fun p hp ↦ ⟨hp.2, hp.1.le⟩⟩
  filter_upwards [hmem] with p hp
  obtain ⟨hp1, hpΦ⟩ := hp
  have h01 : p ∈ Ioo 0 1 := ⟨lt_of_lt_of_le (Phi_mem_Ioo M |>.1) hpΦ, hp1⟩
  exact le_of_not_gt fun h ↦ by
    have hle : p ≤ Phi M := (PhiInv_le_iff h01).1 (le_of_lt h)
    have hEq : p = Phi M := le_antisymm hle hpΦ
    rw [hEq, PhiInv_Phi] at h
    exact absurd h (lt_irrefl M)

/-! ### The vanishing relative displacement of `√ρ` at `ρ → 1` -/

/-- The relative displacement of `√ρ` from `1`, normalised by `√(1 − ρ)`, vanishes at `ρ → 1⁻`:
on `0 ≤ ρ < 1` it equals `√(1 − ρ)/(1 + √ρ)`. -/
private lemma tendsto_one_sub_sqrt_div_sqrt :
    Tendsto (fun ρ : ℝ => (1 - Real.sqrt ρ) / Real.sqrt (1 - ρ)) (𝓝[Iio 1] 1) (𝓝 0) := by
  have hsq : Continuous fun ρ : ℝ => Real.sqrt ρ := Real.continuous_sqrt
  have hsq1 : Continuous fun ρ : ℝ => Real.sqrt (1 - ρ) :=
    hsq.comp (continuous_const.sub continuous_id)
  have hρ0mem : {ρ : ℝ | 0 ≤ ρ} ∈ 𝓝[Iio 1] 1 :=
    mem_nhdsWithin.2 ⟨Ioi (0 : ℝ), isOpen_Ioi, mem_Ioi.2 (by norm_num),
      fun p hp ↦ le_of_lt hp.1⟩
  have hsame : (fun ρ : ℝ => (1 - Real.sqrt ρ) / Real.sqrt (1 - ρ))
      =ᶠ[𝓝[Iio 1] 1] fun ρ : ℝ => Real.sqrt (1 - ρ) / (1 + Real.sqrt ρ) := by
    filter_upwards [hρ0mem, self_mem_nhdsWithin] with ρ hρ0 hρ1
    have hρlt : ρ < 1 := hρ1
    have hs : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.2 (by linarith)
    have hs2 : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ0
    refine (div_eq_div_iff hs.ne'
      (by have hs0 : (0 : ℝ) ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
          linarith : (1 : ℝ) + Real.sqrt ρ ≠ 0)).2 ?_
    have hexp : (1 - Real.sqrt ρ) * (1 + Real.sqrt ρ)
        = 1 + Real.sqrt ρ - (Real.sqrt ρ + Real.sqrt ρ * Real.sqrt ρ) := by ring
    rw [hexp, hs2, Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 - ρ by linarith)]
    ring
  have h3 : Tendsto (fun ρ : ℝ => Real.sqrt (1 - ρ) / (1 + Real.sqrt ρ)) (𝓝[Iio 1] 1) (𝓝 0) := by
    have hnum : ContinuousAt (fun ρ : ℝ => Real.sqrt (1 - ρ)) 1 :=
      hsq1.continuousAt
    have hden : ContinuousAt (fun ρ : ℝ => (1 : ℝ) + Real.sqrt ρ) 1 :=
      (continuous_const.add hsq).continuousAt
    have hc : ContinuousAt (fun ρ : ℝ => Real.sqrt (1 - ρ) / (1 + Real.sqrt ρ)) 1 :=
      hnum.div hden (by norm_num)
    simpa [sub_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact h3.congr' hsame.symm

/-- `√(1 − ρ)` is continuous in `ρ`. -/
private lemma continuous_sqrt_one_sub : Continuous fun ρ : ℝ => Real.sqrt (1 - ρ) :=
  Real.continuous_sqrt.comp (continuous_const.sub continuous_id)

/-! ### The normal tail route at `ρ → 1` -/

/-- If `g` is continuous at `1` with `g 1 > 0`, then `Φ(g(ρ)/√(1 − ρ))` tends to `1` within
`ρ → 1⁻`: for every level `M`, `g ρ` eventually clears `M·√(1 − ρ)` with room to spare, so the
argument of `Φ` leaves every compact set upward. -/
private lemma tendsto_Phi_div_sqrt_one_sub_atTop {g : ℝ → ℝ} (hg : ContinuousAt g 1)
    (hg1 : 0 < g 1) :
    Tendsto (fun ρ : ℝ => Phi (g ρ / Real.sqrt (1 - ρ))) (𝓝[Iio 1] 1) (𝓝 1) := by
  refine tendsto_Phi_atTop.comp (tendsto_atTop.2 fun M ↦ ?_)
  have hcont : ContinuousAt (fun ρ : ℝ => g ρ - M * Real.sqrt (1 - ρ)) 1 :=
    hg.sub ((continuous_const.mul continuous_sqrt_one_sub).continuousAt)
  have hpos : 0 < (fun ρ : ℝ => g ρ - M * Real.sqrt (1 - ρ)) 1 := by
    simpa using hg1
  have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 ((fun ρ : ℝ => g ρ - M * Real.sqrt (1 - ρ)) 1) :=
    mem_nhds_iff.2 ⟨Set.Ioi (0 : ℝ), fun x hx => hx, isOpen_Ioi, mem_Ioi.2 hpos⟩
  have hev := hcont.eventually hmem
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ρ hgt hρ1
  have hρlt : ρ < 1 := hρ1
  have hd : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.2 (by linarith)
  rw [le_div_iff₀ hd]
  linarith

/-- The mirrored route: if `g` is continuous at `1` with `g 1 < 0`, then `Φ(g(ρ)/√(1 − ρ))`
tends to `0` within `ρ → 1⁻`. -/
private lemma tendsto_Phi_div_sqrt_one_sub_atBot {g : ℝ → ℝ} (hg : ContinuousAt g 1)
    (hg1 : g 1 < 0) :
    Tendsto (fun ρ : ℝ => Phi (g ρ / Real.sqrt (1 - ρ))) (𝓝[Iio 1] 1) (𝓝 0) := by
  refine tendsto_Phi_atBot.comp (tendsto_atBot.2 fun M ↦ ?_)
  have hcont : ContinuousAt (fun ρ : ℝ => g ρ - M * Real.sqrt (1 - ρ)) 1 :=
    hg.sub ((continuous_const.mul continuous_sqrt_one_sub).continuousAt)
  have hneg : (fun ρ : ℝ => g ρ - M * Real.sqrt (1 - ρ)) 1 < 0 := by
    simpa using hg1
  have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 ((fun ρ : ℝ => g ρ - M * Real.sqrt (1 - ρ)) 1) :=
    mem_nhds_iff.2 ⟨Set.Iio (0 : ℝ), fun x hx => hx, isOpen_Iio, mem_Iio.2 hneg⟩
  have hev := hcont.eventually hmem
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ρ hgt hρ1
  have hρlt : ρ < 1 := hρ1
  have hd : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.2 (by linarith)
  rw [div_le_iff₀ hd]
  linarith

/-! ### The independence end: `ρ → 0` -/

/-- **The independence end for the conditional default probability**: as the asset correlation
`ρ` approaches `0`, the conditional default probability `oneFactorPD π ρ f` tends to the
constant `π` at every factor value `f` — with vanishing asset correlation the portfolio loss
collapses to the average default probability (Vasicek 2002: the loss distribution converges to
a one-point distribution at `L = p`). The statement is the two-sided limit at `0` in the
ambient encoding, where the formula extends to `ρ ≤ 0` with `√ρ = 0`. -/
theorem oneFactorPD_tendsto_rho_zero {π : ℝ} (hπ : π ∈ Ioo 0 1) (f : ℝ) :
    Tendsto (fun ρ : ℝ => oneFactorPD π ρ f) (𝓝 0) (𝓝 π) := by
  have hfun : (fun ρ : ℝ => oneFactorPD π ρ f)
      = fun ρ : ℝ => Phi ((PhiInv π - Real.sqrt ρ * f) / Real.sqrt (1 - ρ)) := rfl
  have hnum : ContinuousAt (fun ρ : ℝ => PhiInv π - Real.sqrt ρ * f) 0 := by fun_prop
  have hden : ContinuousAt (fun ρ : ℝ => Real.sqrt (1 - ρ)) 0 :=
    continuous_sqrt_one_sub.continuousAt
  have hcomp : ContinuousAt (fun ρ : ℝ => Phi ((PhiInv π - Real.sqrt ρ * f)
      / Real.sqrt (1 - ρ))) 0 := continuous_Phi.continuousAt.comp (hnum.div hden (by simp))
  rw [hfun]
  have ht := hcomp.tendsto
  have hval : Phi ((PhiInv π - Real.sqrt 0 * f) / Real.sqrt (1 - 0)) = π := by
    simp
    exact Phi_PhiInv hπ
  rw [hval] at ht
  exact ht

/-- **The independence end for the worst-case default rate**: as the asset correlation `ρ`
approaches `0`, the asymptotic single-risk-factor quantile `asrfQuantile π ρ α` tends to `π`
at every confidence `α` — the worst-case default rate of a portfolio without systematic risk
is the average default probability itself. -/
theorem asrfQuantile_tendsto_rho_zero {π : ℝ} (hπ : π ∈ Ioo 0 1) (α : ℝ) :
    Tendsto (fun ρ : ℝ => asrfQuantile π ρ α) (𝓝 0) (𝓝 π) := by
  have hfun : (fun ρ : ℝ => asrfQuantile π ρ α)
      = fun ρ : ℝ => Phi ((PhiInv π + Real.sqrt ρ * PhiInv α) / Real.sqrt (1 - ρ)) := rfl
  have hnum : ContinuousAt (fun ρ : ℝ => PhiInv π + Real.sqrt ρ * PhiInv α) 0 := by fun_prop
  have hden : ContinuousAt (fun ρ : ℝ => Real.sqrt (1 - ρ)) 0 :=
    continuous_sqrt_one_sub.continuousAt
  have hcomp : ContinuousAt (fun ρ : ℝ => Phi ((PhiInv π + Real.sqrt ρ * PhiInv α)
      / Real.sqrt (1 - ρ))) 0 := continuous_Phi.continuousAt.comp (hnum.div hden (by simp))
  rw [hfun]
  have ht := hcomp.tendsto
  have hval : Phi ((PhiInv π + Real.sqrt 0 * PhiInv α) / Real.sqrt (1 - 0)) = π := by
    simp
    exact Phi_PhiInv hπ
  rw [hval] at ht
  exact ht

/-! ### The perfect-correlation end: `ρ → 1` -/

/-- **The perfect-correlation end, default scenario**: as the asset correlation `ρ` approaches
`1` from below, the conditional default probability `oneFactorPD π ρ f` tends to `1` at every
factor value below the default threshold `Φ⁻¹(π)`. At `ρ = 1` default is certain in the
scenario `F < Φ⁻¹(π)`: the loss distribution converges to a zero-one distribution with the
mass `π` at `1` (Vasicek 2002). -/
theorem oneFactorPD_tendsto_rho_one_lt {π : ℝ} {f : ℝ} (hf : f < PhiInv π) :
    Tendsto (fun ρ : ℝ => oneFactorPD π ρ f) (𝓝[Iio 1] 1) (𝓝 1) := by
  have hfun : (fun ρ : ℝ => oneFactorPD π ρ f)
      = fun ρ : ℝ => Phi ((PhiInv π - Real.sqrt ρ * f) / Real.sqrt (1 - ρ)) := rfl
  rw [hfun]
  refine tendsto_Phi_div_sqrt_one_sub_atTop
    (g := fun ρ : ℝ => PhiInv π - Real.sqrt ρ * f) (by fun_prop)
    (by simp only [Real.sqrt_one]; linarith)

/-- **The perfect-correlation end, survival scenario**: as the asset correlation `ρ` approaches
`1` from below, the conditional default probability `oneFactorPD π ρ f` tends to `0` at every
factor value above the default threshold `Φ⁻¹(π)` — the mirror of
`oneFactorPD_tendsto_rho_one_lt`, the mass `1 − π` at `0`. -/
theorem oneFactorPD_tendsto_rho_one_gt {π : ℝ} {f : ℝ} (hf : PhiInv π < f) :
    Tendsto (fun ρ : ℝ => oneFactorPD π ρ f) (𝓝[Iio 1] 1) (𝓝 0) := by
  have hfun : (fun ρ : ℝ => oneFactorPD π ρ f)
      = fun ρ : ℝ => Phi ((PhiInv π - Real.sqrt ρ * f) / Real.sqrt (1 - ρ)) := rfl
  rw [hfun]
  refine tendsto_Phi_div_sqrt_one_sub_atBot
    (g := fun ρ : ℝ => PhiInv π - Real.sqrt ρ * f) (by fun_prop)
    (by simp only [Real.sqrt_one]; linarith)

/-- **The perfect-correlation end, at the threshold**: at the factor value `f = Φ⁻¹(π)` the
conditional default probability tends to `1/2` as `ρ → 1⁻` — the factor sits exactly on the
default boundary of the degenerate limit. -/
theorem oneFactorPD_tendsto_rho_one_eq {π : ℝ} {f : ℝ} (hf : f = PhiInv π) :
    Tendsto (fun ρ : ℝ => oneFactorPD π ρ f) (𝓝[Iio 1] 1) (𝓝 (1 / 2)) := by
  have hfun : (fun ρ : ℝ => oneFactorPD π ρ f)
      = fun ρ : ℝ => Phi ((PhiInv π - Real.sqrt ρ * f) / Real.sqrt (1 - ρ)) := rfl
  rw [hfun, hf]
  have harg : Tendsto (fun ρ : ℝ => (PhiInv π - Real.sqrt ρ * PhiInv π)
      / Real.sqrt (1 - ρ)) (𝓝[Iio 1] 1) (𝓝 0) := by
    have hsame : (fun ρ : ℝ => (PhiInv π - Real.sqrt ρ * PhiInv π) / Real.sqrt (1 - ρ))
        =ᶠ[𝓝[Iio 1] 1] fun ρ : ℝ =>
          PhiInv π * ((1 - Real.sqrt ρ) / Real.sqrt (1 - ρ)) := by
      filter_upwards [self_mem_nhdsWithin] with ρ _
      ring
    have hR := tendsto_one_sub_sqrt_div_sqrt.const_mul (PhiInv π)
    simpa using hR.congr' hsame.symm
  have hc := continuous_Phi.continuousAt.tendsto.comp harg
  rw [Phi_zero] at hc
  exact hc

end MathFin
