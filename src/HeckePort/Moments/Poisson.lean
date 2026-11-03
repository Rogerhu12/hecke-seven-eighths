import HeckePort.Moments.Fourier

/-!
# Poisson summation for pairs of Gauss sums

Port of the formal part of openai/math `OAI/NumberTheory/DirichletL/Moments/Poisson.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

The analytic input of openai's file is `EisensteinSchwartzPoisson.actual_radial_paper_poisson_trace`,
the Poisson summation formula for the lattice `ℤ[ω]` and a radial Schwartz function
`z ↦ W (‖z‖² / K)`, with the cubic radial Fourier transform `paperRadialFourier`.  It has no
direct analogue over a general `𝓞 K` (the unit group is infinite; the project's replacement is the
sector theta reflection), so it is the explicit hypothesis bundle `RadialPoissonData`: a squared
norm `norm2` on `𝓞 K` (`‖eisEmbedding z‖²`), a transform (`paperRadialFourier`), the identity
`card (𝓞/(m)) = norm2 m`, and the Poisson formula for a function `P` on `𝓞 / (m)` with the trace
character.  Everything else (`full_gauss_pair_poisson`, `normalized_gauss_pair_poisson`) is the
formal derivation of openai.  `sextic_gauss_pair_poisson` is the specialization to the sextic
Gauss sum (`ProbePhysical.sexticGauss`) and is not ported.
-/

noncomputable section

namespace HeckePort.Moments.Poisson

open scoped NumberField BigOperators Classical SchwartzMap
open HeckePort.Moments HeckePort.Moments.CommonSupport HeckePort.Moments.Fourier

variable {K : Type*} [Field K] [NumberField K]

/-- The lattice Poisson summation formula, as a hypothesis (see the module docstring). -/
structure RadialPoissonData (T : TraceFamily K) where
  norm2 : 𝓞 K → ℝ
  transform : 𝓢(ℝ, ℂ) → ℝ → ℂ
  norm2_ne_zero : ∀ m : 𝓞 K, m ≠ 0 → norm2 m ≠ 0
  card_eq : ∀ (m : 𝓞 K), m ≠ 0 → ∀ [Fintype (Residue m)],
    (Fintype.card (Residue m) : ℂ) = (norm2 m : ℂ)
  poisson : ∀ (m : 𝓞 K), m ≠ 0 → ∀ [Fintype (Residue m)] (P : Residue m → ℂ) (W : 𝓢(ℝ, ℂ))
    (Kk : ℝ), 0 < Kk →
    (∑' z : 𝓞 K, P (Ideal.Quotient.mk _ z) * W (norm2 z / Kk)) =
      (Kk / norm2 m : ℝ) • ∑' j : 𝓞 K,
        (∑ r : Residue m, P r * T.ψ m (Ideal.Quotient.mk _ j * r)) *
          transform W (Kk * norm2 j / norm2 m)

variable {T : TraceFamily K} (R : RadialPoissonData T)

theorem full_gauss_pair_poisson (u v : 𝓞 K) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ)
    (W : 𝓢(ℝ, ℂ)) (Kk : ℝ) (hK : 0 < Kk) :
    (∑' z : 𝓞 K, residueGauss T u χu (Ideal.Quotient.mk _ z) *
      star (residueGauss T v χv (Ideal.Quotient.mk _ z)) * W (R.norm2 z / Kk)) =
      (Kk : ℂ) * ∑' j : 𝓞 K, fullModulusCorrelation u v χu χv (-j) *
        R.transform W (Kk * R.norm2 j / R.norm2 (u * v)) := by
  have huv : u * v ≠ 0 := mul_ne_zero hu hv
  let P := fun h : Residue (u * v) =>
    residueGauss T u χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
      star (residueGauss T v χv (frequencyReduction v (u * v) (dvd_mul_left v u) h))
  have hcoeff (j : 𝓞 K) :
      (∑ r : Residue (u * v), P r * T.ψ (u * v) (Ideal.Quotient.mk _ j * r)) =
      (Fintype.card (Residue (u * v)) : ℂ) * fullModulusCorrelation u v χu χv (-j) := by
    have ht := gauss_correlation T u v hu hv χu χv (-j)
    have heq (r : Residue (u * v)) : -(r * Ideal.Quotient.mk _ (-j)) =
        Ideal.Quotient.mk _ j * r := by
      simp only [map_neg, mul_neg, neg_neg]
      exact mul_comm _ _
    simp_rw [heq] at ht
    exact ht
  have hcard : (Fintype.card (Residue (u * v)) : ℂ) = (R.norm2 (u * v) : ℂ) :=
    R.card_eq (u * v) huv
  have hpoisson := R.poisson (u * v) huv P W Kk hK
  have hmain : (∑' z : 𝓞 K, residueGauss T u χu (Ideal.Quotient.mk _ z) *
      star (residueGauss T v χv (Ideal.Quotient.mk _ z)) * W (R.norm2 z / Kk)) =
      (∑' z : 𝓞 K, P (Ideal.Quotient.mk _ z) * W (R.norm2 z / Kk)) := by
    apply tsum_congr
    intro z
    simp only [P, frequencyReduction_mk]
  rw [hmain, hpoisson]
  simp_rw [hcoeff, hcard, mul_assoc]
  rw [tsum_mul_left, Complex.real_smul, Complex.ofReal_div, ← mul_assoc]
  have hn : (R.norm2 (u * v) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (R.norm2_ne_zero _ huv)
  rw [div_mul_cancel₀ _ hn]

theorem normalized_gauss_pair_poisson (u v : 𝓞 K) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ)
    (W : 𝓢(ℝ, ℂ)) (Kk : ℝ) (hK : 0 < Kk) :
    (∑' z : 𝓞 K, normalizedResidueGauss T u χu (Ideal.Quotient.mk _ z) *
      star (normalizedResidueGauss T v χv (Ideal.Quotient.mk _ z)) * W (R.norm2 z / Kk)) =
      ((Kk : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))) *
      ∑' j : 𝓞 K, fullModulusCorrelation u v χu χv (-j) *
        R.transform W (Kk * R.norm2 j / R.norm2 (u * v)) := by
  let ru : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)
  let rv : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ)
  have hterm (z : 𝓞 K) :
      normalizedResidueGauss T u χu (Ideal.Quotient.mk _ z) *
        star (normalizedResidueGauss T v χv (Ideal.Quotient.mk _ z)) * W (R.norm2 z / Kk) =
      (ru * rv)⁻¹ * (residueGauss T u χu (Ideal.Quotient.mk _ z) *
        star (residueGauss T v χv (Ideal.Quotient.mk _ z)) * W (R.norm2 z / Kk)) := by
    simp only [normalizedResidueGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
    dsimp only [ru, rv]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, full_gauss_pair_poisson R u v hu hv χu χv W Kk hK]
  dsimp only [ru, rv]
  ring

end HeckePort.Moments.Poisson

end
