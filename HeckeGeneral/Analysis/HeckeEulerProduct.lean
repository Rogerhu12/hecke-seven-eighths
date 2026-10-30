import HeckeGeneral.Analysis.HeckeSeries
import HeckeGeneral.Analysis.IdealEulerIdentity

/-!
# The Euler product of an actual Hecke character on Re(s) > 1

These are unconditional statements for actual continuous unitary idèle
class characters. The ideal series and prime product are identified using
the proved ideal factorization equivalence and unconditional summation.
No continuation into Re(s) ≤ 1 is asserted.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Arithmetic
open scoped BigOperators

variable (K : Type*) [Field K] [NumberField K]

/-- The local Euler factors genuinely converge to the actual Hecke ideal series. -/
theorem hasProd_heckeLSeries (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v => heckeLocalEulerFactor K χ v s) (heckeLSeries K χ s) := by
  apply (hasProd_idealDirichletSeries K (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) hs).congr_fun
  intro v
  simp only [heckeLocalEulerFactor, eulerPolynomial, residueCard,
    Complex.ofReal_natCast, primeIdealRatio]

theorem heckeLSeries_eq_eulerProduct (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    heckeLSeries K χ s = ∏' v, heckeLocalEulerFactor K χ v s :=
  (hasProd_heckeLSeries K χ hs).tprod_eq.symm

/-- Unconditional nonvanishing on the domain of absolute convergence. -/
theorem heckeLSeries_ne_zero (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    heckeLSeries K χ s ≠ 0 :=
  idealDirichletSeries_ne_zero K (primeCoefficient K χ) (norm_primeCoefficient_le_one K χ) hs

theorem meromorphicOrderAt_heckeLSeries (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    meromorphicOrderAt (heckeLSeries K χ) s = 0 := by
  have h := analyticAt_heckeLSeries K χ hs
  rw [h.meromorphicOrderAt_eq, h.analyticOrderAt_eq_zero.mpr (heckeLSeries_ne_zero K χ hs)]
  rfl

/-- The existing meromorphic-order interface now applies to a genuine L-function
on its proved half-plane of absolute convergence. -/
theorem meromorphicZeroFreeOn_heckeLSeries (χ : HeckeCharacter K) :
    MeromorphicZeroFreeOn (heckeLSeries K χ) {s : ℂ | 1 < s.re} := by
  refine ⟨fun s hs => (analyticAt_heckeLSeries K χ hs).meromorphicAt, fun s hs => ?_⟩
  exact (meromorphicOrderAt_heckeLSeries K χ hs).le

theorem analyticAt_heckeReciprocal (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (fun z => (heckeLSeries K χ z)⁻¹) s :=
  (analyticAt_heckeLSeries K χ hs).inv (heckeLSeries_ne_zero K χ hs)

end HeckeGeneral.Analysis
