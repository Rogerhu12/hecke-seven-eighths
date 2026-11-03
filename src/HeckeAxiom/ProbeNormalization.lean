import HeckeAxiom.DenominatorAdapter
import HeckeGeneral.Analysis.PhysicalProbePrincipal
import HeckeGeneral.Analysis.HeckeNormPole

/-!
# The physical residue normalizer is a positive real

The normalizer is `c_K · (1/6) · R² · M · m`, where `c_K > 0` is the fixed
Poisson lattice scalar and `R` is the deleted residue of the Dedekind
zeta function, `M` the additive Mellin value of the probe test at `1/6` and `m` the Mellin
value of the denominator test at `1`.

* The pole-cleared Dedekind zeta function is `(s - 1) ζ_K(s)` on `Re s > 1` and is
  continuous, so its value at `1` is the residue of `ζ_K`, a positive real.
* The deleted Euler polynomial of the trivial character at `1` is `∏ (1 - N𝔭⁻¹)`, a
  positive real.
* The Mellin value at `1` of a nonnegative nonzero weight supported in `(0, ∞)` is its
  integral, a positive real.

So the normalizer is a positive real as soon as `M` is.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain MeasureTheory Set Filter Topology
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical

namespace ProbeNormalization

variable {K : Type} [Field K] [NumberField K]

/-- The pole-cleared Dedekind zeta function at `1` is the residue. -/
theorem dedekindPoleCleared_one :
    dedekindPoleCleared K 1 = (NumberField.dedekindZeta_residue K : ℂ) := by
  obtain ⟨hdiff, -, heq, -⟩ : Differentiable ℂ (dedekindPoleCleared K) ∧
      dedekindPoleCleared K 1 ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → dedekindPoleCleared K s = (s - 1) * NumberField.dedekindZeta K s) ∧
      ∀ n : ℕ, dedekindPoleCleared K (-2 * (n + 1)) = 0 :=
    Classical.choose_spec
      (NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K)
  have hcont : Tendsto (fun s : ℝ => dedekindPoleCleared K (s : ℂ)) (𝓝[>] 1)
      (𝓝 (dedekindPoleCleared K 1)) := by
    have h := ((hdiff.continuous.comp Complex.continuous_ofReal).tendsto 1).mono_left
      (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    simpa [Function.comp_def] using h
  have heventually : (fun s : ℝ => ((s : ℂ) - 1) * NumberField.dedekindZeta K s) =ᶠ[𝓝[>] 1]
      fun s : ℝ => dedekindPoleCleared K (s : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (heq s (by simpa using hs)).symm
  exact tendsto_nhds_unique hcont
    ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' heventually)

/-- The deleted Euler polynomial of the trivial character at `1`. -/
theorem deletionPolynomial_one (T : Finset (HeightOneSpectrum (𝓞 K))) :
    heckeEulerDeletionPolynomial K 1 T 1 =
      ((∏ p ∈ T, (1 - ((residueCard K p : ℝ))⁻¹) : ℝ) : ℂ) := by
  unfold heckeEulerDeletionPolynomial finiteEulerPolynomial eulerPolynomial
  push_cast
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [primeCoefficient_trivial, one_mul, Complex.cpow_neg_one]

theorem deletionPolynomial_factor_pos (T : Finset (HeightOneSpectrum (𝓞 K))) :
    0 < ∏ p ∈ T, (1 - ((residueCard K p : ℝ))⁻¹) := by
  refine Finset.prod_pos fun p _ => ?_
  have h : (1 : ℝ) < residueCard K p := by exact_mod_cast one_lt_residueCard K p
  rw [sub_pos]
  exact inv_lt_one_of_one_lt₀ h

/-- The deleted residue, as a positive real. -/
def residueValue (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] : ℝ :=
  NumberField.dedekindZeta_residue K *
    ∏ p ∈ exceptionalPrimes K S, (1 - ((residueCard K p : ℝ))⁻¹)

theorem deletedZetaResidue_eq (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] :
    deletedZetaResidue K S = (residueValue S : ℂ) := by
  unfold deletedZetaResidue residueValue
  rw [dedekindPoleCleared_one, deletionPolynomial_one]
  push_cast
  rfl

theorem residueValue_pos (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] :
    0 < residueValue (K := K) S :=
  mul_pos (NumberField.dedekindZeta_residue_pos K) (deletionPolynomial_factor_pos _)

/-- The Mellin value at `1` of the denominator test from a real annular weight. -/
theorem mellin_denominatorTest_one (W : DedekindZetaZeroFree.ProbeRealAnnularWeight) :
    mellin (denominatorTest W).toFun 1 = ((∫ y, W.toFun y : ℝ) : ℂ) := by
  have hzero : ∀ y ∉ Ioi (0 : ℝ), W.toFun y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (W.support_positive h)
  unfold mellin
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  simp

theorem integral_pos (W : DedekindZetaZeroFree.ProbeRealAnnularWeight) :
    0 < ∫ y, W.toFun y := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, W.toFun x ≠ 0 := Function.ne_iff.mp W.nonzero
  exact W.smooth.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    W.compactSupport W.nonnegative hx

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))

/-- **PR-NORMALIZATION.** With the denominator test from `W`, the physical residue
normalizer is a positive real whenever the probe test's Mellin value at `1/6` is. -/
theorem physicalResidueNormalizer_pos (P : ProbeData K S)
    (W : DedekindZetaZeroFree.ProbeRealAnnularWeight) (hden : P.denominator = denominatorTest W)
    (him : (additiveMellin K S μ P.additive (1 / 6)).im = 0)
    (hre : 0 < (additiveMellin K S μ P.additive (1 / 6)).re) :
    (physicalResidueNormalizer K S μ P).im = 0 ∧ 0 < (physicalResidueNormalizer K S μ P).re := by
  set z := additiveMellin K S μ P.additive (1 / 6)
  have hz : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
  have hval : physicalResidueNormalizer K S μ P =
      ((physicalPoissonScalar K *
        (1 / 6 * residueValue (K := K) S ^ 2 * z.re * ∫ y, W.toFun y) : ℝ) : ℂ) := by
    unfold physicalResidueNormalizer
    rw [deletedZetaResidue_eq, hden, mellin_denominatorTest_one,
      show additiveMellin K S μ P.additive (1 / 6) = (z.re : ℂ) from hz]
    push_cast
    ring
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, by
    have := physicalPoissonScalar_pos K
    have := residueValue_pos (K := K) S
    have := integral_pos W
    positivity⟩

end ProbeNormalization

end HeckeAxiom
