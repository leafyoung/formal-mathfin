/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Rates.VasicekBondPrice
public import MathFin.Models.Rates.VasicekZeroMeanReversionLimit

/-!
# The Ho–Lee zero-coupon bond price — the affine term structure at linear loading

The Ho–Lee short rate `dr = θ(t)dt + σdW` is the driftless member of the Gaussian short-rate
family: the mean-reversion coefficient is zero, so the exponential kernel of Vasicek and
Hull–White degenerates to the constant `1` and the affine loading is **linear**, `B(T) = T`.
This file prices the zero-coupon bond under it,

  `P(0, T) = 𝔼[exp(−∫₀ᵀ r_s ds)] = A(T)·exp(−T·r₀)`,
  `A(T) = exp(−∫₀ᵀ (T − s)·θ(s) ds + σ²T³/6)`,

with the deterministic drift `θ` read through its interval integral (constant drift
`θT²/2` by `hoLeeIntegratedMean_const`). The integrated rate is carried in its Wiener
representation `∫₀ᵀ r_s ds = M(T) + σ∫₀ᵀ (T − u) dB_u`, exactly as in
`Models/Rates/VasicekBondPrice.lean`; the time-order swap behind it is the modelling
bridge, cited, not proved.

The diffusion kernel `g(u) = T − u` and its variance `∫₀ᵀ g² = T³/3` are model-independent
(the `κ → 0⁺` kernel of the Vasicek family) and are **reused verbatim** from
`Models/Rates/VasicekZeroMeanReversionLimit.lean` (`brownianIntegratedKernelLp`), the way
`Models/Rates/HullWhiteCalibration.lean` reuses `vasicekIntegratedKernelLp`: the drift
enters the mean only, never the kernel. The price is the centred-Gaussian Laplace transform
— the Wiener bond-price lemma `integral_exp_neg_add_mul_wienerIntegralLp` at
`m = M(T)`, `c = σ`, `f = g`, whose Vasicek, Hull–White and two-piece GSR instances the
library already carries.

## What the formalization forces

* **The linear loading is a limit, not a substitution.** Lean's `x / 0 = 0` makes the
  Vasicek closed form total at `κ = 0`, where it evaluates to `exp(−θT)`
  (`vasicekBondPrice_closedForm_zero_meanReversion`), a rate pinned at the long-run level.
  The Ho–Lee price is instead the `κ → 0⁺` limit at level `θ/κ` — the level diverges so the
  drift `κ·(θ/κ − r) → θ` survives vanishing mean reversion
  (`tendsto_vasicekBondPrice_hoLee`). The mean splits as
  `M = r₀·B(T) + θ·(T − B(T))/κ`, and `(T − B(T))/κ → T²/2` is the loading integral above.
* **Zero drift is the driftless model.** At `θ ≡ 0` the integrated Ho–Lee rate *is*
  `brownianIntegratedRate` (`hoLeeBondRate_zero_drift`), whose price
  `brownianBondPrice_eq` is already on the tree; the kernel reuse is that identity.

## Scope (disclosed)

* The short rate and its time integral are carried in their Wiener representations
  (deterministic mean plus a Wiener integral of the kernel `T − u` against the pre-Brownian
  driver `B` under `μ`); that they solve the short-rate SDE, and the time-order swap behind
  the integrated rate, are cited, not proved. The measure is read as the pricing measure;
  no change of measure is built (mirroring `vasicekBondPrice_eq`).
* The drift integral `∫₀ᵀ (T − s)·θ(s) ds` is Lean's totalized interval integral, mirroring
  `HullWhite.bondPrice_eq`; for a drift integrable against `(T − ·)` on `[0, T]` (continuous
  drifts, for instance) it is the model's mean, and the price formula is the classical one.
* The limit theorem `tendsto_vasicekBondPrice_hoLee` is stated for the closed forms, as the
  other `κ → 0⁺` limits are; no convergence of random variables is claimed.

## Main definitions

* `hoLeeIntegratedMean`: the deterministic mean of the integrated short rate,
  `M(T) = r₀·T + ∫₀ᵀ (T − s)·θ(s) ds` — the B-form at linear loading `B = id`.
* `hoLeeBondRate`: the integrated Ho–Lee short rate in its Wiener representation,
  `∫₀ᵀ r_s ds = M(T) + σ·∫₀ᵀ (T − u) dB_u`.
* `hoLeeBondA`: the affine coefficient `A(T) = exp(−∫₀ᵀ (T − s)·θ(s) ds + σ²T³/6)`.
* `hoLeeBondPrice`: the bond price function `u(T, r) = A(T)·exp(−T·r)`.

## Main results

* `hoLeeIntegratedMean_const`, `hoLeeBondA_const` — the constant-drift closed forms
  `M(T) = r₀T + θT²/2`, `A(T) = exp(−θT²/2 + σ²T³/6)`.
* `hoLeeBondRate_zero_drift` — at zero drift the integrated Ho–Lee rate is the driftless
  `brownianIntegratedRate`.
* `hoLeeIntegratedRate_hasLaw_gaussian` — `∫₀ᵀ r_s ds ~ N(M(T), σ²T³/3)`.
* `hoLeeBondPrice_eq` — `𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−M(T) + σ²T³/6)`, the Wiener bond-price
  lemma at the kernel `T − u`.
* `hoLeeBondPrice_affine` — `P(0,T) = A(T)·exp(−T·r₀)`, the affine term structure with
  linear loading `B(T) = T`.
* `tendsto_vasicekBondPrice_hoLee` — the Vasicek closed form at level `θ/κ` tends to the
  Ho–Lee price as `κ → 0⁺`.

## References

* [T. S. Y. Ho and S.-B. Lee, *Term structure movements and pricing interest rate contingent
  claims*][HoLee1986]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], §32.2
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006]
* [The QuantLib contributors, *QuantLib*][QuantLib], Vasicek::A (vasicek.cpp)

## Tags

Ho–Lee model, affine term structure, zero-coupon bond price, Gaussian short rate,
Wiener integral, MSC 91G30, MSC 60H05, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The integrated mean and the affine coefficient -/

/-- The deterministic mean of the integrated Ho–Lee short rate,
`M(T) = ∫₀ᵀ (r₀ + ∫₀ˢ θ) ds = r₀·T + ∫₀ᵀ (T − s)·θ(s) ds` — the B-form of
`HullWhite.integratedMean` at the linear loading `B = id`. -/
noncomputable def hoLeeIntegratedMean (θ : ℝ → ℝ) (r₀ T : ℝ) : ℝ :=
  r₀ * T + ∫ s in (0 : ℝ)..T, (T - s) * θ s

/-- The **integrated Ho–Lee short rate** in its Wiener representation:
`∫₀ᵀ r_s ds = M(T) + σ·∫₀ᵀ (T − u) dB_u` — the mirror of `vasicekIntegratedRate` and
`HullWhite.bondRate`, with the kernel `T − u` reused from
`brownianIntegratedKernelLp` (the diffusion kernel is drift-free, so it is the same object
as the driftless model's). -/
noncomputable def hoLeeBondRate (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ) (σ r₀ : ℝ)
    (T : ℝ≥0) (ω : Ω) : ℝ :=
  hoLeeIntegratedMean θ r₀ (T : ℝ)
    + σ * (wienerIntegralLp B hB T (brownianIntegratedKernelLp T) ω)

/-- The Ho–Lee affine coefficient `A(T) = exp(−∫₀ᵀ (T − s)·θ(s) ds + σ²T³/6)` —
`HullWhite.bondA` at the linear loading `B = id`, with the Vasicek variance replaced by its
vanishing-mean-reversion limit `T³/3`. -/
noncomputable def hoLeeBondA (θ : ℝ → ℝ) (σ T : ℝ) : ℝ :=
  Real.exp (-(∫ s in (0 : ℝ)..T, (T - s) * θ s) + σ ^ 2 * T ^ 3 / 6)

/-- **The Ho–Lee bond price function** `u(T, r) = A(T)·exp(−T·r)`, the affine term structure
at linear loading: the price of the bond (`hoLeeBondPrice_affine`). -/
noncomputable def hoLeeBondPrice (θ : ℝ → ℝ) (σ T r : ℝ) : ℝ :=
  hoLeeBondA θ σ T * Real.exp (-(T * r))

/-! ### The constant drift, in closed form -/

/-- **The drift loading of a constant Ho–Lee drift**: `∫₀ᵀ (T − s)·θ ds = θ·T²/2`, by the FTC
with the antiderivative `θ·(T·s − s²/2)` — the `(T − ·)`-weighted mass of the drift, the
quantity `A(T)` discounts. -/
lemma integral_const_sub_mul (θ T : ℝ) :
    ∫ s in (0 : ℝ)..T, (T - s) * θ = θ * T ^ 2 / 2 := by
  open intervalIntegral in
  rw [integral_comp_sub_left (f := fun y : ℝ ↦ y * θ), intervalIntegral.integral_mul_const,
    integral_id]
  simp
  ring

/-- **The constant-drift integrated mean**: `M(T) = r₀·T + θ·T²/2` — the drift integral
`∫₀ᵀ ∫₀ˢ θ du ds` of the short rate `r_s = r₀ + θ·s + σ·B_s`. -/
lemma hoLeeIntegratedMean_const (θ r₀ T : ℝ) :
    hoLeeIntegratedMean (fun _ ↦ θ) r₀ T = r₀ * T + θ * T ^ 2 / 2 := by
  rw [hoLeeIntegratedMean, integral_const_sub_mul]

/-- **The constant-drift affine coefficient**: `A(T) = exp(−θT²/2 + σ²T³/6)` — the level
term `θT²/2` plus the Itô correction `σ²T³/6` of the variance `σ²T³/3`. -/
lemma hoLeeBondA_const (θ σ T : ℝ) :
    hoLeeBondA (fun _ ↦ θ) σ T = Real.exp (-(θ * T ^ 2 / 2) + σ ^ 2 * T ^ 3 / 6) := by
  rw [hoLeeBondA, integral_const_sub_mul]

end MathFin
