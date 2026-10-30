import HeckeGeneral.Analysis.LocalThetaInput
import HeckeGeneral.Analysis.LogGaussianMellin
import HeckeGeneral.Arithmetic.SIntegerLocalDiagonal
import HeckeGeneral.Arithmetic.SUnitFiniteGeneration
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
Concrete coefficient and Mellin data for the marked theta reflection.

Sources: marked_reflection_supplement.tex (Tsum), (mult), (Phi), and P,
primitive-04-reflection.tex (reflection-local-formula). These definitions
do not construct the Kazhdan--Patterson representation. In particular the
finite-place rotated valuation tables below are PENDING data, with their
automorphic realization to be supplied separately. No physical-probe bound,
zero-free region, or unspecified reflected function is a field of this file.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Global

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def exteriorMul (I J : ExteriorIdeal K S) : ExteriorIdeal K S :=
  ⟨I.val * J.val, by
    intro p hp
    rcases (p.prime.dvd_mul (a := I.val.val) (b := J.val.val)).mp hp with hi | hj
    · exact I.property p hi
    · exact J.property p hj⟩

def completedIdeal (c n : ExteriorIdeal K S) : ExteriorIdeal K S :=
  exteriorMul K S c (exteriorMul K S n (exteriorMul K S n n))

def exteriorNorm (I : ExteriorIdeal K S) : ℝ := (I.val.val.absNorm : ℝ)

def idealSymbol (I : ExteriorIdeal K S) (a : S.integer K) : ℂ :=
  sIntegerSexticIdealEvaluation K S D.root6 D.primitive6 D.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a

def wholeIndexMask (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    (I : ExteriorIdeal K S) : Prop :=
  IsCoprime I.val.val r.val.val ∧ ∀ p ∈ Q, p.val.asIdeal ∣ I.val.val

/-- The literal coefficient, including the whole-index coprimality/mark
mask. A mark dividing m kills the term through the actual residue symbol. -/
def completedTerm (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    (V : ℝ → ℂ) (X : ℝ) (cn : ExteriorIdeal K S × ExteriorIdeal K S) : ℂ :=
  let c := cn.1
  let n := cn.2
  let A := completedIdeal K S c n
  if Squarefree c.val.val ∧ wholeIndexMask K S r Q A then
    thetaGamma K S D c 2 /
      ((Real.sqrt (exteriorNorm K S c) : ℂ) * (exteriorNorm K S n : ℂ)) *
      heckeIdealCoefficient K θ A.val * idealSymbol K S D A m *
      V (exteriorNorm K S A / X)
  else 0

/-- Defined as an actual ideal sum; meaningful reflection hypotheses below
must additionally assert Summable, rather than rely on tsum's zero default. -/
def completedThetaSum (θ : HeckeCharacter K) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' cn, completedTerm K S D θ m r Q V X cn

/-- The Euler derivative on the positive multiplicative line. -/
def eulerDerivative (f : ℝ → ℂ) : ℝ → ℂ := fun y => (y : ℂ) * deriv f y

def eulerDerivativeOrder (h : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (eulerDerivative^[h]) f

def testIntegral (V : ℝ → ℂ) (j : ℕ) (A : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), ‖eulerDerivativeOrder j V y‖ *
    (y ^ (1 / 4 : ℝ) + y ^ (-A)) / y

/-- A finite maximum (with 0 adjoined) of the source's actual integrals. -/
def testSeminorm (V : ℝ → ℂ) (J : ℕ) (A : ℝ) : ℝ :=
  (Finset.range (J + 1)).sup' (by simp) (fun j => max 0 (testIntegral V j A))

/-- Annular tests have support bounded away from zero. The bounds are data,
not an assumption on the final Mellin kernel. -/
structure SmoothAnnularTest where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_ge : lower ≤ upper
  support : Function.support toFun ⊆ Icc lower upper

abbrev SixthUnitClasses :=
  S.unit K ⧸ (powMonoidHom 6 : S.unit K →* S.unit K).range

instance sixthUnitClassesFinite : Finite (SixthUnitClasses K S) := by
  let := sUnit_power_range_finiteIndex K S 6 (by decide)
  exact inferInstance

abbrev SixthLocalClasses := sLocalMultiplicativeGroup K S ⧸
  (powMonoidHom 6 : sLocalMultiplicativeGroup K S →*
    sLocalMultiplicativeGroup K S).range

def generatorLocalClass (I : ExteriorIdeal K S) : SixthLocalClasses K S :=
  QuotientGroup.mk (sLocalNonzeroIntegerDiagonal K S ⟨D.generator I, D.generator_ne_zero I⟩)

def unitLocalClass (u : S.unit K) : SixthLocalClasses K S :=
  QuotientGroup.mk (sLocalDiagonal K S u)

/-- Actual archimedean parameters of the period character, not an arbitrary
list of parameters whose connection to the Hecke character is unstated. -/
def archShift (θ : HeckeCharacter K) (v : {v : InfinitePlace K // v.IsComplex}) : ℝ :=
  ((|heckeComplexWeight K v.val v.property θ| : ℤ) : ℝ) / 2 + 1 / 2

def archRadial (θ : HeckeCharacter K) (v : {v : InfinitePlace K // v.IsComplex}) : ℝ :=
  -heckeComplexParameter K v.val v.property θ

def archGammaProduct (θ : HeckeCharacter K) (s : ℂ) : ℂ :=
  ∏ v : {v : InfinitePlace K // v.IsComplex},
    Complex.Gamma ((archShift K θ v : ℂ) + s +
      Complex.I * archRadial K θ v + 1 / 6) *
    Complex.Gamma ((archShift K θ v : ℂ) + s +
      Complex.I * archRadial K θ v - 1 / 6)

/-- Concrete finite-place presentation of the rotated vector. For each
unit sector/local sixth-power class there is a finite sum of tensors of
valuation sequences on the ACTUAL primes in S. These sequences are pending
KP data, not free holomorphic multipliers. Cutoff and decay are separately
required by `FiniteMellinAdmissible`; realization is not claimed. -/
structure FiniteMellinData where
  terms : ℕ
  coefficient : SixthUnitClasses K S → SixthLocalClasses K S →
    Fin terms → (p : S) → ℤ → ℂ
  C₀ : ℂ
  C₀_ne_zero : C₀ ≠ 0
  A₀ : ℝ
  A₀_pos : 0 < A₀

variable (F : FiniteMellinData K S)

def localMellinSeries (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (l : Fin F.terms) (p : S) (s : ℂ) : ℂ :=
  ∑' k : ℤ, F.coefficient u κ l p k * (p.val.asIdeal.absNorm : ℂ) ^ (-(k : ℂ) * s)

def finiteMellinFactor (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S)
    (s : ℂ) : ℂ :=
  ∑ l : Fin F.terms, ∏ p : S, localMellinSeries K S F u κ l p s

/-- The denominator has the opposite radial parameter:
Gamma(a-s-iτ±1/6), as in the source's Mellin quotient. -/
def reflectionMultiplier (θ : HeckeCharacter K)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ) : ℂ :=
  F.C₀⁻¹ * (F.A₀ : ℂ) ^ (2 * s) * finiteMellinFactor K S F u κ s *
    ∏ v : {v : InfinitePlace K // v.IsComplex},
      (Complex.Gamma ((archShift K θ v : ℂ) + s + Complex.I * archRadial K θ v + 1 / 6) /
       Complex.Gamma ((archShift K θ v : ℂ) - s - Complex.I * archRadial K θ v + 1 / 6)) *
      (Complex.Gamma ((archShift K θ v : ℂ) + s + Complex.I * archRadial K θ v - 1 / 6) /
       Complex.Gamma ((archShift K θ v : ℂ) - s - Complex.I * archRadial K θ v - 1 / 6))

def kernelIntegrand (θ : HeckeCharacter K) (u : SixthUnitClasses K S)
    (κ : SixthLocalClasses K S) (V : ℝ → ℂ) (σ y t : ℝ) : ℂ :=
  let w : ℂ := σ + t * Complex.I
  mellin V (-w) * reflectionMultiplier K S F θ u κ w * (y : ℂ) ^ (-w)

/-- Parameterizing dw = i dt cancels the i in 1/(2πi). -/
def mellinReflectionKernel (θ : HeckeCharacter K) (u : SixthUnitClasses K S)
    (κ : SixthLocalClasses K S) (V : ℝ → ℂ) (σ y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, kernelIntegrand K S F θ u κ V σ y t

structure FiniteMellinAdmissible : Prop where
  valuation_cutoff : ∃ k₀ : ℤ, ∀ u κ l p k, k < k₀ → F.coefficient u κ l p k = 0
  valuation_decay : ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ u κ l p k, 0 ≤ k →
      ‖F.coefficient u κ l p k‖ ≤ C * (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * δ)
  absolute_mellin : ∀ u κ l p s, -(1 / 3 : ℝ) < s.re →
    Summable (fun k : ℤ => F.coefficient u κ l p k *
      (p.val.asIdeal.absNorm : ℂ) ^ (-(k : ℂ) * s))

/-- Explicit analytic reflection-kernel obligations. These stop before
physical-probe/row-energy estimates and do not assert a zero-free region.
The constant is chosen before the test, sector, class, and scale y. -/
structure MellinKernelInput (θ : HeckeCharacter K) : Prop where
  finite_admissible : FiniteMellinAdmissible K S F
  integrable : ∀ (V : SmoothAnnularTest) u κ σ y, -(1 / 3 : ℝ) < σ → 0 < y →
    Integrable (kernelIntegrand K S F θ u κ V.toFun σ y)
  line_independent : ∀ (V : SmoothAnnularTest) u κ σ σ' y,
    -(1 / 3 : ℝ) < σ → -(1 / 3 : ℝ) < σ' → 0 < y →
    mellinReflectionKernel K S F θ u κ V.toFun σ y =
      mellinReflectionKernel K S F θ u κ V.toFun σ' y
  derivative_bound : ∀ (A : ℝ) (h J : ℕ), 0 ≤ A →
    4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) * A + h + 1 < J →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SmoothAnnularTest) u κ y, 0 < y →
      ‖eulerDerivativeOrder h
        (mellinReflectionKernel K S F θ u κ V.toFun 0) y‖ ≤
      C * testSeminorm V.toFun J A * min (y ^ (1 / 4 : ℝ)) (y ^ (-A))

end HeckeGeneral.ThetaSkeleton.Global
