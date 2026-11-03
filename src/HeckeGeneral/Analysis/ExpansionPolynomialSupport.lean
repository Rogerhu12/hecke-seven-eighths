import HeckeGeneral.Analysis.ExpansionBufferedPolynomials
import ExpansionDetector.AnnularNormalization

/-! The contour estimate may use the finite full norm window. The actual
IdealTest support is smaller; the sums agree by their literal zero terms.
This module also applies the exact Fourier/Mellin normalization. -/

noncomputable section
namespace HeckeGeneral.Analysis.ExpansionBufferedPolynomials

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open ExpansionInterfaces.Mellin ExpansionDetector.Fourier
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

def finiteIdealNormWindow (B : ℝ) : Finset (NonzeroIdeal K) :=
  (Ideal.finite_setOfPred_absNorm_le ⌈B⌉₊).toFinset.preimage
    (fun I : NonzeroIdeal K => I.val) (by
      intro I _ J _ h
      exact Subtype.ext h)

theorem mem_finiteIdealNormWindow_of_le (B : ℝ) (I : NonzeroIdeal K)
    (hI : idealNorm K I ≤ B) : I ∈ finiteIdealNormWindow K B := by
  unfold finiteIdealNormWindow
  apply Finset.mem_preimage.mpr
  apply (Set.Finite.mem_toFinset _).mpr
  change Ideal.absNorm I.val ≤ ⌈B⌉₊
  have h : (Ideal.absNorm I.val : ℝ) ≤ (⌈B⌉₊ : ℝ) := hI.trans (Nat.le_ceil B)
  exact_mod_cast h

/-- Replacing a literal test support by the full finite norm window does
not change the polynomial; both omitted sets contain only zero terms. -/
theorem annular_sum_eq_normWindow (W : AnnularProfile) (c : NonzeroIdeal K → ℂ)
    (s : ℂ) (X : ℝ) (hX : 0 < X) (S : Finset (NonzeroIdeal K))
    (hS : ∀ I, W.function (idealNorm K I / X) ≠ 0 → I ∈ S) :
    (∑ I ∈ S, smoothedTerm W c (idealNorm K) s X I) =
      ∑ I ∈ finiteIdealNormWindow K (W.upper * X), smoothedTerm W c (idealNorm K) s X I := by
  have hleft : (∑' I, smoothedTerm W c (idealNorm K) s X I) =
      ∑ I ∈ S, smoothedTerm W c (idealNorm K) s X I := by
    apply tsum_eq_sum
    intro I hI
    have hz : W.function (idealNorm K I / X) = 0 := by
      by_contra hn
      exact hI (hS I hn)
    simp only [smoothedTerm, hz, mul_zero]
  have hright : (∑' I, smoothedTerm W c (idealNorm K) s X I) =
      ∑ I ∈ finiteIdealNormWindow K (W.upper * X), smoothedTerm W c (idealNorm K) s X I := by
    apply tsum_eq_sum
    intro I hI
    have hz : W.function (idealNorm K I / X) = 0 := by
      by_contra hn
      have hu : idealNorm K I / X ≤ W.upper := (W.supported hn).2
      exact hI (mem_finiteIdealNormWindow_of_le K (W.upper * X) I ((div_le_iff₀ hX).mp hu))
    simp only [smoothedTerm, hz, mul_zero]
  exact hleft.symm.trans hright

/-- The actual normalized detector polynomial is the same finite sum
controlled by the Mellin theorem, with the exact central factor. -/
theorem actual_normalized_norm_eq_annular (reciprocal : Bool)
    (χ : HeckeCharacter K) (E : Finset (HeightOneSpectrum (𝓞 K)))
    (W : AnnularProfile) (S : Finset (NonzeroIdeal K)) (X β ν : ℝ) (hX : 0 < X) :
    ‖normalizedPolynomial S (deletedAnnularCoefficient K reciprocal χ E)
      (idealNorm K) W.function X β ν‖ =
      X ^ (β - 1 / 2) *
        ‖∑ I ∈ S, smoothedTerm W (deletedAnnularCoefficient K reciprocal χ E)
          (idealNorm K) (centralShift β ν) X I‖ := by
  exact normalizedPolynomial_norm_eq_dirichlet S
    (deletedAnnularCoefficient K reciprocal χ E) (idealNorm K)
    (fun I _ => idealNorm_pos K I) W.function X β ν hX

end HeckeGeneral.Analysis.ExpansionBufferedPolynomials
