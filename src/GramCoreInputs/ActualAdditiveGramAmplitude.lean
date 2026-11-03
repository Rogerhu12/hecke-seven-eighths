import HeckeGeneral.Analysis.PhysicalProbeData
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
UNCOMPILED / native 0. The literal additive amplitude in revised (3.33),
using exterior ideals, the actual finite Gauss sum of P.arithmetic, and the
original complex annular test. The coefficient c is a fixed function of
the ideal alone, placed before the scale, Mellin parameter and row.

These definitions and finite algebra hold for every such c. They do not
assert that c has the manuscript's fixed finite ray shape, that the chosen
generators satisfy AllowedGeneratorInput, or that the amplitude descends
through any unit quotient. No unit subgroup is selected or changed here.
The square expansion includes the zero row and every exterior denominator;
no squarefree or coprimality restriction is inserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The central real normalization Y^(-3/2), embedded into the complex field. -/
def additiveGramCentralNormalization (Y : ℝ) : ℂ :=
  (Y ^ (-(3 / 2 : ℝ)) : ℝ)

/-- The original ideal summand. In particular the Gauss frequency is -m. -/
def actualAdditiveGramTerm (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (m : S.integer K) (I : ExteriorIdeal K S) : ℂ :=
  c I * W.toFun (exteriorNorm K S I / Y) *
    (((exteriorNorm K S I / Y : ℝ) : ℂ) ^
      ((-1 : ℂ) + Complex.I * (ν : ℂ))) *
    probeGauss K S P I (-m)

/-- The literal A_m(Y;nu) of (3.33), prior to any unit-quotient descent. -/
def actualAdditiveGramAmplitude (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (m : S.integer K) : ℂ :=
  additiveGramCentralNormalization Y *
    ∑' I : ExteriorIdeal K S, actualAdditiveGramTerm K S P c W Y ν m I

/-- A common finite ideal envelope, independent of c, nu, m and P. -/
def additiveGramIdealSupport (W : SmoothAnnularTest) (Y : ℝ) :
    Finset (ExteriorIdeal K S) :=
  (dyadicIdealSupport K (W.upper * Y / 2)).subtype
    (fun I : NonzeroIdeal K =>
      ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S)

theorem mem_additiveGramIdealSupport_iff (W : SmoothAnnularTest)
    (Y : ℝ) (hY : 0 < Y) (I : ExteriorIdeal K S) :
    I ∈ additiveGramIdealSupport K S W Y ↔
      exteriorNorm K S I ≤ W.upper * Y := by
  have hu : 0 < W.upper := lt_of_lt_of_le W.lower_pos W.upper_ge
  have hD : 0 ≤ W.upper * Y / 2 :=
    div_nonneg (mul_nonneg hu.le hY.le) (by norm_num)
  rw [additiveGramIdealSupport, Finset.mem_subtype,
    mem_dyadicIdealSupport_iff K hD I.val]
  change exteriorNorm K S I ≤ 2 * (W.upper * Y / 2) ↔ _
  have hscale : 2 * (W.upper * Y / 2) = W.upper * Y := by ring
  rw [hscale]

/-- Nonzero original terms have the actual annular ideal norm cutoff. -/
theorem actualAdditiveGramTerm_norm_le_of_ne_zero (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) (I : ExteriorIdeal K S)
    (hI : actualAdditiveGramTerm K S P c W Y ν m I ≠ 0) :
    exteriorNorm K S I ≤ W.upper * Y := by
  have hW : W.toFun (exteriorNorm K S I / Y) ≠ 0 := by
    intro hz
    apply hI
    simp only [actualAdditiveGramTerm, hz, mul_zero, zero_mul]
  exact (div_le_iff₀ hY).mp (W.support hW).2

theorem actualAdditiveGramTerm_eq_zero_outside (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) (I : ExteriorIdeal K S)
    (hI : I ∉ additiveGramIdealSupport K S W Y) :
    actualAdditiveGramTerm K S P c W Y ν m I = 0 := by
  by_contra hn
  exact hI ((mem_additiveGramIdealSupport_iff K S W Y hY I).mpr
    (actualAdditiveGramTerm_norm_le_of_ne_zero K S P c W Y ν hY m I hn))

theorem actualAdditiveGramTerm_hasFiniteSupport (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) :
    Function.HasFiniteSupport (actualAdditiveGramTerm K S P c W Y ν m) := by
  apply (additiveGramIdealSupport K S W Y).finite_toSet.subset
  intro I hI
  exact (mem_additiveGramIdealSupport_iff K S W Y hY I).mpr
    (actualAdditiveGramTerm_norm_le_of_ne_zero K S P c W Y ν hY m I hI)

theorem actualAdditiveGramTerm_summable (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) :
    Summable (actualAdditiveGramTerm K S P c W Y ν m) :=
  summable_of_hasFiniteSupport
    (actualAdditiveGramTerm_hasFiniteSupport K S P c W Y ν hY m)

theorem actualAdditiveGramTerm_norm_summable (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) :
    Summable (fun I => ‖actualAdditiveGramTerm K S P c W Y ν m I‖) := by
  apply summable_of_hasFiniteSupport
  apply (actualAdditiveGramTerm_hasFiniteSupport K S P c W Y ν hY m).subset
  intro I hI
  exact norm_ne_zero_iff.mp hI

/-- One common finite sum represents A_m for every Mellin parameter and row. -/
theorem actualAdditiveGramAmplitude_eq_sum (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) :
    actualAdditiveGramAmplitude K S P c W Y ν m =
      additiveGramCentralNormalization Y *
        ∑ I ∈ additiveGramIdealSupport K S W Y,
          actualAdditiveGramTerm K S P c W Y ν m I := by
  unfold actualAdditiveGramAmplitude
  rw [tsum_eq_sum (fun I hI =>
    actualAdditiveGramTerm_eq_zero_outside K S P c W Y ν hY m I hI)]

/-- The full two-column factor, before any correlation or Poisson identity. -/
def actualAdditiveGramPairTerm (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (m : S.integer K) (I J : ExteriorIdeal K S) : ℂ :=
  (c I * conj (c J)) *
    (W.toFun (exteriorNorm K S I / Y) *
      conj (W.toFun (exteriorNorm K S J / Y))) *
    ((((exteriorNorm K S I / Y : ℝ) : ℂ) ^
        ((-1 : ℂ) + Complex.I * (ν : ℂ))) *
      conj ((((exteriorNorm K S J / Y : ℝ) : ℂ) ^
        ((-1 : ℂ) + Complex.I * (ν : ℂ))))) *
    (probeGauss K S P I (-m) * conj (probeGauss K S P J (-m)))

theorem actualAdditiveGramPairTerm_eq (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (m : S.integer K) (I J : ExteriorIdeal K S) :
    actualAdditiveGramPairTerm K S P c W Y ν m I J =
      actualAdditiveGramTerm K S P c W Y ν m I *
        conj (actualAdditiveGramTerm K S P c W Y ν m J) := by
  simp only [actualAdditiveGramPairTerm, actualAdditiveGramTerm, map_mul]
  ring

theorem actualAdditiveGramPairTerm_hasFiniteSupport (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) :
    Function.HasFiniteSupport (fun IJ : ExteriorIdeal K S × ExteriorIdeal K S =>
      actualAdditiveGramPairTerm K S P c W Y ν m IJ.1 IJ.2) := by
  apply ((additiveGramIdealSupport K S W Y).product
    (additiveGramIdealSupport K S W Y)).finite_toSet.subset
  intro IJ hIJ
  have hprod : actualAdditiveGramTerm K S P c W Y ν m IJ.1 *
      conj (actualAdditiveGramTerm K S P c W Y ν m IJ.2) ≠ 0 := by
    simpa only [Function.mem_support, actualAdditiveGramPairTerm_eq] using hIJ
  have h₁ : actualAdditiveGramTerm K S P c W Y ν m IJ.1 ≠ 0 := by
    intro hz
    exact hprod (by simp only [hz, zero_mul])
  have h₂ : actualAdditiveGramTerm K S P c W Y ν m IJ.2 ≠ 0 := by
    intro hz
    exact hprod (by simp only [hz, map_zero, mul_zero])
  exact Finset.mem_product.mpr
    ⟨(mem_additiveGramIdealSupport_iff K S W Y hY IJ.1).mpr
      (actualAdditiveGramTerm_norm_le_of_ne_zero K S P c W Y ν hY m IJ.1 h₁),
     (mem_additiveGramIdealSupport_iff K S W Y hY IJ.2).mpr
      (actualAdditiveGramTerm_norm_le_of_ne_zero K S P c W Y ν hY m IJ.2 h₂)⟩

theorem additiveGramCentralNormalization_mul_conj (Y : ℝ) (hY : 0 < Y) :
    additiveGramCentralNormalization Y * conj (additiveGramCentralNormalization Y) =
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) := by
  have hp : (Y ^ (-(3 / 2 : ℝ))) ^ 2 = Y ^ (-3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le]
    norm_num
  calc
    _ = (((Y ^ (-(3 / 2 : ℝ))) * (Y ^ (-(3 / 2 : ℝ))) : ℝ) : ℂ) := by
      simp only [additiveGramCentralNormalization, Complex.conj_ofReal, Complex.ofReal_mul]
    _ = ((Y ^ (-3 : ℝ) : ℝ) : ℂ) := by rw [← pow_two, hp]

/-- The exact central factor is Y^(-3). All two-column terms remain present,
including noncoprime denominators and any zero masks in the actual Gauss sums. -/
theorem actualAdditiveGramAmplitude_norm_sq_eq_double_sum (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) :
    ((‖actualAdditiveGramAmplitude K S P c W Y ν m‖ ^ 2 : ℝ) : ℂ) =
      ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        ∑ I ∈ additiveGramIdealSupport K S W Y,
          ∑ J ∈ additiveGramIdealSupport K S W Y,
            actualAdditiveGramPairTerm K S P c W Y ν m I J := by
  calc
    _ = actualAdditiveGramAmplitude K S P c W Y ν m *
        conj (actualAdditiveGramAmplitude K S P c W Y ν m) := by
      simpa only [Complex.ofReal_pow] using
        (Complex.mul_conj' (actualAdditiveGramAmplitude K S P c W Y ν m)).symm
    _ = (additiveGramCentralNormalization Y * conj (additiveGramCentralNormalization Y)) *
        ((∑ I ∈ additiveGramIdealSupport K S W Y,
          actualAdditiveGramTerm K S P c W Y ν m I) *
        conj (∑ J ∈ additiveGramIdealSupport K S W Y,
          actualAdditiveGramTerm K S P c W Y ν m J)) := by
      simp only [actualAdditiveGramAmplitude_eq_sum K S P c W Y ν hY m, map_mul]
      ring
    _ = ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        ∑ I ∈ additiveGramIdealSupport K S W Y,
          ∑ J ∈ additiveGramIdealSupport K S W Y,
            actualAdditiveGramTerm K S P c W Y ν m I *
              conj (actualAdditiveGramTerm K S P c W Y ν m J) := by
      rw [additiveGramCentralNormalization_mul_conj Y hY]
      simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro I _hI
      apply Finset.sum_congr rfl
      intro J _hJ
      exact (actualAdditiveGramPairTerm_eq K S P c W Y ν m I J).symm

theorem actualAdditiveGramAmplitude_norm_sq_eq_double_sum_re (P : ProbeData K S)
    (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (m : S.integer K) :
    ‖actualAdditiveGramAmplitude K S P c W Y ν m‖ ^ 2 =
      Y ^ (-3 : ℝ) *
        (∑ I ∈ additiveGramIdealSupport K S W Y,
          ∑ J ∈ additiveGramIdealSupport K S W Y,
            actualAdditiveGramPairTerm K S P c W Y ν m I J).re := by
  have h := congrArg Complex.re
    (actualAdditiveGramAmplitude_norm_sq_eq_double_sum K S P c W Y ν hY m)
  simpa only [Complex.ofReal_re, Complex.re_ofReal_mul] using h

end HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
