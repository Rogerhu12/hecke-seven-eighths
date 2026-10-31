import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceColumns
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalGaussCalibration
import HeckeSkeleton.Moments.MOM_INV_STEP.MarkPriority

/-!
# A second Moebius divisor in a fixed original common-factor slice

After the genuine second transform, its computed common ideal g is
fixed. Full mutual-coprimality extension acts on the already transformed
canonical residual columns. The new common divisor v is then extracted
from each extended residual separately. It is never incorporated into a
recomputed gcd of the historical inverse source.

The real a₀ multiplication formula inserts v into the fourth-power
label. The row and original unit sector are unchanged. Original marks
on g z are assigned at the fixed ideal g v, using their original
individual coefficients, and the norm test is rescaled exactly.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondOverlapColumns

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalSectorRows SecondSourceCharacters
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

abbrev residual (z v : Ext) : Ext := ActualInverseFactors.residual K Sset z v

theorem divisor_factorization (z v : Ext) (hz : Squarefree z.val.val)
    (hv : v.val.val ∣ z.val.val) :
    exteriorMul K Sset v (residual K S z v) = z := by
  apply Subtype.ext
  apply Subtype.ext
  exact (FirstSourceDecomposition.squarefree_divisor_decomposition z.val v.val hz hv).1.symm

theorem divisor_residual_coprime (z v : Ext) (hz : Squarefree z.val.val)
    (hv : v.val.val ∣ z.val.val) : IsCoprime v.val.val (residual K S z v).val.val :=
  (FirstSourceDecomposition.squarefree_divisor_decomposition z.val v.val hz hv).2.1

def forwardCoefficient (Λ ν : HeckeCharacter K) (n f I : Ext) (ξ : Sector) : ℂ :=
  (CoefficientCycle.canonicalCoefficient K Sset D Λ n *
    heckeIdealCoefficient K ν n.val) *
    (idealSymbol K Sset D n (D.generator f) ^ 4 * sectorCharacter K S Γ D n I ξ)

theorem actual_childCoefficient (Λ ν : HeckeCharacter K) (n j I : Ext) (ξ : Sector)
    (dk d₂ : NonzeroRingElements (Set.integer Sset K)) :
    SecondSourceColumns.childCoefficient K S Γ D Λ ν n j I ξ dk d₂ =
      forwardCoefficient K S Γ D Λ ν n (SecondSourceColumns.newLabel K S j d₂)
        (SecondSourceColumns.newRowIdeal K S I dk d₂)
        (SecondSourceColumns.newSector K S Γ D dk d₂ ξ) := rfl

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
/-- This is a factorization of the actual forward coefficient at z,
with the quotient computed from the selected divisor, not supplied. -/
theorem extract_overlap (Λ ν : HeckeCharacter K) (z v f I : Ext) (ξ : Sector)
    (hz : Squarefree z.val.val) (hv : v.val.val ∣ z.val.val) :
    forwardCoefficient K S Γ D Λ ν z f I ξ =
      forwardCoefficient K S Γ D Λ ν v f I ξ *
        forwardCoefficient K S Γ D Λ ν (residual K S z v)
          (exteriorMul K Sset f v) I ξ := by
  let u := residual K S z v
  have ha := CanonicalGaussCalibration.canonicalCoefficient_mul K S D hallowed Λ v u
    (divisor_residual_coprime K S z v hz hv)
  rw [hallowed.reciprocity v u] at ha
  have hν : heckeIdealCoefficient K ν (exteriorMul K Sset v u).val =
      heckeIdealCoefficient K ν v.val * heckeIdealCoefficient K ν u.val :=
    heckeIdealCoefficient_mul K ν v.val u.val
  calc
    _ = forwardCoefficient K S Γ D Λ ν (exteriorMul K Sset v u) f I ξ :=
      congrArg (fun n => forwardCoefficient K S Γ D Λ ν n f I ξ)
        (divisor_factorization K S z v hz hv).symm
    _ = _ := by
      unfold forwardCoefficient
      rw [ha, hν, generator_mul_character K S D hallowed]
      simp only [sectorCharacter, ThetaGaussCRT.idealSymbol_mul_denominator, mul_pow]
      ring

theorem residual_norm_argument (z v : Ext) (hz : Squarefree z.val.val)
    (hv : v.val.val ∣ z.val.val) (X : ℝ) :
    (z.val.val.absNorm : ℝ) / X =
      ((residual K S z v).val.val.absNorm : ℝ) / (X / (v.val.val.absNorm : ℝ)) := by
  have he : z.val.val = v.val.val * (residual K S z v).val.val :=
    (FirstSourceDecomposition.squarefree_divisor_decomposition z.val v.val hz hv).1
  rw [he, map_mul, Nat.cast_mul, div_div_eq_mul_div]
  ring

variable {σ : Type*} [DecidableEq σ]

/-- The fixed g is the original second common factor. The moving z is
an independent residual in its fully extended canonical kernel. -/
def markedColumnTerm (Λ ν : HeckeCharacter K) (g z f I : Ext) (ξ : Sector)
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  forwardCoefficient K S Γ D Λ ν z f I ξ *
    divisorMark slots lists a (g.val.val * z.val.val) * W ((z.val.val.absNorm : ℝ) / X)

include hallowed in
/-- The exact second priority split uses g v with g fixed throughout
the Moebius extension. Both the mark coefficients and norm test are
the original ones. The returned column has the label f v. -/
theorem actual_marked_overlap (Λ ν : HeckeCharacter K) (g z v f I : Ext) (ξ : Sector)
    (hz : Squarefree z.val.val) (hv : v.val.val ∣ z.val.val)
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (hprime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p)
    (W : ℝ → ℂ) (X : ℝ) :
    markedColumnTerm K S Γ D Λ ν g z f I ξ slots lists a W X =
      forwardCoefficient K S Γ D Λ ν v f I ξ *
        ∑ J ∈ slots.powerset, divisorMark J lists a (g.val.val * v.val.val) *
          (forwardCoefficient K S Γ D Λ ν (residual K S z v)
              (exteriorMul K Sset f v) I ξ *
            divisorMark (slots \ J) (residualDivisorLists (g.val.val * v.val.val) lists)
              a (residual K S z v).val.val *
            W (((residual K S z v).val.val.absNorm : ℝ) / (X / (v.val.val.absNorm : ℝ)))) := by
  have he : g.val.val * z.val.val =
      (g.val.val * v.val.val) * (residual K S z v).val.val := by
    rw [(FirstSourceDecomposition.squarefree_divisor_decomposition z.val v.val hz hv).1,
      mul_assoc]
  unfold markedColumnTerm
  rw [extract_overlap K S Γ D hallowed Λ ν z v f I ξ hz hv,
    residual_norm_argument K S z v hz hv X, he,
    mark_priority slots lists a (g.val.val * v.val.val) (residual K S z v).val.val hprime]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

theorem original_mark_coefficients (slots J : Finset σ)
    (lists : σ → Finset (Ideal (𝓞 K))) (a : σ → Ideal (𝓞 K) → ℂ)
    (g v : Ext) (hJ : J ⊆ slots)
    (hdis : (slots : Set σ).PairwiseDisjoint lists)
    (ha : ∀ i ∈ slots, ∀ p ∈ lists i, ‖a i p‖ ≤ 1) :
    (J : Set σ).PairwiseDisjoint (residualDivisorLists (g.val.val * v.val.val) lists) ∧
      (∀ i ∈ J, ∀ p ∈ residualDivisorLists (g.val.val * v.val.val) lists i, ‖a i p‖ ≤ 1) ∧
      (∀ i ∈ J, ∀ p ∈ residualDivisorLists (g.val.val * v.val.val) lists i,
        ¬p ∣ g.val.val * v.val.val) :=
  residual_lists_preserve slots J (g.val.val * v.val.val) lists a hJ hdis ha

/-- A live extracted coefficient keeps the new averaged label
squarefree. The bad source terms remain zero before any enlargement. -/
theorem overlap_label_squarefree (Λ ν : HeckeCharacter K) (z v f I : Ext) (ξ : Sector)
    (hz : Squarefree z.val.val) (hv : v.val.val ∣ z.val.val) (hf : Squarefree f.val.val)
    (hlive : forwardCoefficient K S Γ D Λ ν v f I ξ ≠ 0) :
    Squarefree (exteriorMul K Sset f v).val.val := by
  have hsymbol : idealSymbol K Sset D v (D.generator f) ≠ 0 := by
    intro hh
    exact hlive (by simp only [forwardCoefficient, hh, zero_pow (by decide : (4 : ℕ) ≠ 0),
      zero_mul, mul_zero])
  have hfcon : sIntegerModulusContraction K Sset (D.generator f) = f.val.val := by
    simpa only [CanonicalIdealRow.generator_ofExterior, CanonicalIdealRow.ofExterior_val] using
      CanonicalIdealRow.generator_contraction K S D (CanonicalIdealRow.ofExterior K S f)
  have hmask : idealCoprimeMask f.val.val v.val.val ≠ 0 := by
    rw [← hfcon, ← symbol_self_pair]
    exact mul_ne_zero (star_ne_zero.mpr hsymbol) hsymbol
  have hc : IsCoprime v.val.val f.val.val := (idealCoprimeMask_ne_zero _ _).mp hmask
  exact squarefree_mul_iff.mpr ⟨hc.symm.isRelPrime, hf, hz.squarefree_of_dvd hv⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondOverlapColumns

end
