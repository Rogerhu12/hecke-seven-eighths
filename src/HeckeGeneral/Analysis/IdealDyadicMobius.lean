import HeckeGeneral.Analysis.IdealMobiusDeletion
import HeckeGeneral.Analysis.SIntegerSexticDyadicAmplification

/-!
The actual dyadic decomposition of the S-excluded Moebius--Hecke series.
Each shell is an actual finite ideal sum. The nonnegative smooth partition
and absolute convergence justify the two summation orders on Re(s)>1.
No continuation or estimate beyond this half-plane is assumed here.
-/

noncomputable section
namespace HeckeGeneral.Analysis.IdealDyadicMobius

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open IdealMobiusReciprocal
open scoped BigOperators Classical nonZeroDivisors Topology

variable (K : Type) [Field K] [NumberField K]

/-- The coefficient is the proved literal S-excluded actual Moebius--Hecke term. -/
def dyadicTerm (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : NonzeroIdeal K) (j : ℕ) (s : ℂ) : ℂ :=
  (fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ) *
    excludedTerm K S (primeCoefficient K χ) s I

def shell (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (j : ℕ) (s : ℂ) : ℂ :=
  ∑ I ∈ SquarefreeAmplification.dyadicIdealSupport K ((2 : ℝ) ^ j),
    dyadicTerm K χ S I j s

def dyadicTotal (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (s : ℂ) : ℂ := ∑' j : ℕ, shell K χ S j s

theorem dyadicTerm_eq_zero_outside (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) (j : ℕ) (s : ℂ)
    (hI : I ∉ SquarefreeAmplification.dyadicIdealSupport K ((2 : ℝ) ^ j)) :
    dyadicTerm K χ S I j s = 0 := by
  have hj : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) j
  have hn : ¬idealNorm K I ≤ 2 * (2 : ℝ) ^ j := fun h =>
    hI ((SquarefreeAmplification.mem_dyadicIdealSupport_iff K hj.le I).mpr h)
  have hr : 2 ≤ idealNorm K I / (2 : ℝ) ^ j :=
    (le_div_iff₀ hj).mpr (le_of_lt (lt_of_not_ge hn))
  simp only [dyadicTerm, fixedDyadicWeight_zero_of_ge hr, Complex.ofReal_zero, zero_mul]

theorem shell_eq_tsum (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (j : ℕ) (s : ℂ) :
    shell K χ S j s = ∑' I, dyadicTerm K χ S I j s := by
  exact (tsum_eq_sum (fun I hI => dyadicTerm_eq_zero_outside K χ S I j s hI)).symm

theorem hasSum_shell_terms (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (j : ℕ) (s : ℂ) :
    HasSum (fun I => dyadicTerm K χ S I j s) (shell K χ S j s) := by
  exact hasSum_sum_of_ne_finset_zero (fun I hI =>
    dyadicTerm_eq_zero_outside K χ S I j s hI)

theorem norm_dyadicTerm (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) (j : ℕ) (s : ℂ) :
    ‖dyadicTerm K χ S I j s‖ =
      fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) *
        ‖excludedTerm K S (primeCoefficient K χ) s I‖ := by
  rw [dyadicTerm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (fixedDyadicWeight_nonneg _)]

theorem hasSum_norm_dyadicTerm (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) (s : ℂ) :
    HasSum (fun j => ‖dyadicTerm K χ S I j s‖)
      ‖excludedTerm K S (primeCoefficient K χ) s I‖ := by
  simpa only [norm_dyadicTerm, one_mul] using
    (fixedDyadicWeight_hasSum (one_le_idealNorm K I)).mul_right
      ‖excludedTerm K S (primeCoefficient K χ) s I‖

theorem hasSum_dyadicTerm (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) (s : ℂ) :
    HasSum (fun j => dyadicTerm K χ S I j s)
      (excludedTerm K S (primeCoefficient K χ) s I) := by
  have h : HasSum (fun j : ℕ =>
      (fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ)) (1 : ℂ) :=
    Complex.hasSum_ofReal.mpr (fixedDyadicWeight_hasSum (one_le_idealNorm K I))
  simpa only [dyadicTerm, one_mul] using
    h.mul_right (excludedTerm K S (primeCoefficient K χ) s I)

/-- Absolute convergence of the actual ideal by dyadic-scale double series. -/
theorem absolutelySummable_double (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ij : NonzeroIdeal K × ℕ => ‖dyadicTerm K χ S ij.1 ij.2 s‖) := by
  apply (summable_prod_of_nonneg (fun ij => norm_nonneg
    (dyadicTerm K χ S ij.1 ij.2 s))).mpr
  constructor
  · intro I
    exact (hasSum_norm_dyadicTerm K χ S I s).summable
  · simp_rw [(hasSum_norm_dyadicTerm K χ S _ s).tsum_eq]
    exact absolutelySummable_excluded K S (primeCoefficient K χ)
      (norm_primeCoefficient_le_one K χ) hs

theorem summable_double (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ij : NonzeroIdeal K × ℕ => dyadicTerm K χ S ij.1 ij.2 s) :=
  (absolutelySummable_double K χ S hs).of_norm

theorem hasSum_shell (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun j => shell K χ S j s)
      (∑' I, excludedTerm K S (primeCoefficient K χ) s I) := by
  have hd := (summable_double K χ S hs).hasSum
  have hi := hd.prod_fiberwise (fun I => hasSum_dyadicTerm K χ S I s)
  have hd' : HasSum (fun ij : NonzeroIdeal K × ℕ => dyadicTerm K χ S ij.1 ij.2 s)
      (∑' I, excludedTerm K S (primeCoefficient K χ) s I) := by
    rw [hi.tsum_eq]
    exact hd
  have hswap : HasSum (fun ji : ℕ × NonzeroIdeal K => dyadicTerm K χ S ji.2 ji.1 s)
      (∑' I, excludedTerm K S (primeCoefficient K χ) s I) :=
    (Equiv.prodComm ℕ (NonzeroIdeal K)).hasSum_iff.mpr hd'
  exact hswap.prod_fiberwise (fun j => hasSum_shell_terms K χ S j s)

theorem summable_shell (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun j => shell K χ S j s) := (hasSum_shell K χ S hs).summable

/-- On its genuine convergence domain the actual dyadic total is the
reciprocal of the actual finitely deleted Hecke continuation. -/
theorem dyadicTotal_eq_reciprocal (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    dyadicTotal K χ S s = (heckeDeletedContinuation K χ S s)⁻¹ := by
  rw [dyadicTotal, (hasSum_shell K χ S hs).tsum_eq]
  simp_rw [hecke_excludedTerm_eq_literal]
  exact hecke_excluded_moebius_series_eq_reciprocal K χ S hs

theorem differentiable_excludedTerm (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) :
    Differentiable ℂ (fun s => excludedTerm K S (primeCoefficient K χ) s I) := by
  unfold excludedTerm
  split
  · exact differentiable_idealDirichletTerm K (coefficient K (primeCoefficient K χ)) I
  · exact differentiable_const 0

theorem differentiable_shell (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (j : ℕ) :
    Differentiable ℂ (shell K χ S j) := by
  unfold shell
  apply Differentiable.fun_sum
  intro I _hI
  exact (differentiable_const
    (fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ)).mul
      (differentiable_excludedTerm K χ S I)

end HeckeGeneral.Analysis.IdealDyadicMobius
