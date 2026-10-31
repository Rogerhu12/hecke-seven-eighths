import ActualAllowedGeneratorOrbitEnumeration
import ActualChoiceMaskedWholeAnnular
import Mathlib.Logic.Equiv.Prod

/-!
UNCOMPILED / native 0. One complete product-index reindexing of the actual
same-witness choice-masked annular sum. The mask is evaluated on d*m, so
its generator-orbit enumeration retains the LITERAL condition d | u*gen(I).
The quotient is constructed and is nonzero. No Fubini exchange, Summable
input, arbitrary ideal coefficient, or comparison of a subset with a whole
complex sum occurs.

This does not yet identify the finite residual-ideal weights in the
row-ball dual integrand with this sum. That separate consumer must retain
the actual generator-division units, annular norm powers and joint profile.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualDivisibleChoiceDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open ActualGeneratorChoiceDraft ActualChoiceMaskedAnnularDraft
open ActualProbeGaussFourierDraft
open ActualGramJointChartDraft ActualGramFamilyDraft ActualWholeAnnularAllScaleDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "E" => ExteriorIdeal K S
local notation "Γ" => sixthPowerUnits K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

local instance divisibleChoice_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K S 6 (by decide)

/-- Product columns in the existing chosen-generator orbits that are
literally divisible by the SAME supplied S-integer d. -/
def DivisibleChosenColumns (d : NZ) :=
  {p : E × Γ // d.val ∣
    (sIntegerOrbitTranslate K S Γ p.2 (probeGenerator K S w.D p.1)).val}

/-- The actual nonzero quotient of a selected product column by d. -/
def divisibleChosenQuotient (d : NZ) (p : DivisibleChosenColumns K w d) : NZ :=
  ⟨Classical.choose p.property, by
    intro hzero
    have h := Classical.choose_spec p.property
    rw [hzero, mul_zero] at h
    exact (sIntegerOrbitTranslate K S Γ p.val.2
      (probeGenerator K S w.D p.val.1)).property h⟩

theorem divisorColumn_divisibleChosenQuotient (d : NZ)
    (p : DivisibleChosenColumns K w d) :
    divisorColumn K S d (divisibleChosenQuotient K w d p) =
      sIntegerOrbitTranslate K S Γ p.val.2 (probeGenerator K S w.D p.val.1) := by
  apply Subtype.ext
  exact (Classical.choose_spec p.property).symm

@[simp] theorem choiceColumnMask_divisibleChosenQuotient (d : NZ)
    (p : DivisibleChosenColumns K w d) :
    choiceColumnMask K w d (divisibleChosenQuotient K w d p) = 1 := by
  unfold choiceColumnMask
  rw [divisorColumn_divisibleChosenQuotient]
  exact choiceFiniteMask_generator_translate K w p.val.1 p.val.2

/-- Quotient columns selected by the original product-column mask. -/
def divisorChoiceColumns (d : NZ) :=
  {m : NZ // choiceColumnMask K w d m = 1}

def divisibleChosenMaskedColumn (d : NZ) (p : DivisibleChosenColumns K w d) :
    divisorChoiceColumns K w d :=
  ⟨divisibleChosenQuotient K w d p, choiceColumnMask_divisibleChosenQuotient K w d p⟩

theorem divisibleChosenMaskedColumn_injective (d : NZ) :
    Function.Injective (divisibleChosenMaskedColumn K w d) := by
  intro p q hpq
  have hquot : divisibleChosenQuotient K w d p =
      divisibleChosenQuotient K w d q := congrArg Subtype.val hpq
  have hcol : choiceGeneratorOrbitColumn K w p.val =
      choiceGeneratorOrbitColumn K w q.val := by
    apply Subtype.ext
    calc
      _ = divisorColumn K S d (divisibleChosenQuotient K w d p) :=
        (divisorColumn_divisibleChosenQuotient K w d p).symm
      _ = divisorColumn K S d (divisibleChosenQuotient K w d q) := congrArg _ hquot
      _ = _ := divisorColumn_divisibleChosenQuotient K w d q
  exact Subtype.ext (choiceGeneratorOrbitColumn_injective K w hcol)

theorem divisibleChosenMaskedColumn_surjective (d : NZ) :
    Function.Surjective (divisibleChosenMaskedColumn K w d) := by
  intro m
  let t : choiceMaskedColumns K w := ⟨divisorColumn K S d m.val, m.property⟩
  let p₀ : E × Γ := (choiceGeneratorOrbitEquiv K w).symm t
  have ht : sIntegerOrbitTranslate K S Γ p₀.2 (probeGenerator K S w.D p₀.1) =
      divisorColumn K S d m.val :=
    congrArg Subtype.val ((choiceGeneratorOrbitEquiv K w).apply_symm_apply t)
  let p : DivisibleChosenColumns K w d :=
    ⟨p₀, ⟨m.val.val, congrArg Subtype.val ht⟩⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply divisorColumn_injective K S d
  exact (divisorColumn_divisibleChosenQuotient K w d p).trans ht

/-- The actual quotient map is a bijection, with no lifting input. -/
def divisibleChosenColumnEquiv (d : NZ) :
    DivisibleChosenColumns K w d ≃ divisorChoiceColumns K w d :=
  Equiv.ofBijective (divisibleChosenMaskedColumn K w d)
    ⟨divisibleChosenMaskedColumn_injective K w d,
      divisibleChosenMaskedColumn_surjective K w d⟩

/-- A SINGLE product equivalence, rather than a double-series exchange. -/
def divisibleChosenPairEquiv (d : NZ) :
    DivisibleChosenColumns K w d × DivisibleChosenColumns K w d ≃
      {m : NZ × NZ // choiceColumnMask K w d m.1 = 1 ∧
        choiceColumnMask K w d m.2 = 1} :=
  (Equiv.prodCongr (divisibleChosenColumnEquiv K w d)
    (divisibleChosenColumnEquiv K w d)).trans Equiv.subtypeProdEquivProd.symm

@[simp] theorem divisibleChosenPairEquiv_val (d : NZ)
    (p : DivisibleChosenColumns K w d × DivisibleChosenColumns K w d) :
    (divisibleChosenPairEquiv K w d p).val =
      (divisibleChosenQuotient K w d p.1, divisibleChosenQuotient K w d p.2) := rfl

private theorem choiceColumnMask_eq_zero_of_ne_one (d m : NZ)
    (h : choiceColumnMask K w d m ≠ 1) : choiceColumnMask K w d m = 0 := by
  unfold choiceColumnMask choiceFiniteMask at *
  split_ifs at * <;> simp_all

/-- An exact indicator restriction and one product-index bijection.
The identity is valid for totalized tsums and assumes no summability. -/
theorem tsum_choiceColumnMask_pair_eq_divisibleChosenPairs (d : NZ)
    (f : NZ × NZ → ℂ) :
    (∑' m : NZ × NZ, choiceColumnMask K w d m.1 *
      choiceColumnMask K w d m.2 * f m) =
      ∑' p : DivisibleChosenColumns K w d × DivisibleChosenColumns K w d,
        f (divisibleChosenQuotient K w d p.1, divisibleChosenQuotient K w d p.2) := by
  let A : Set (NZ × NZ) :=
    {m | choiceColumnMask K w d m.1 = 1 ∧ choiceColumnMask K w d m.2 = 1}
  have hind (m : NZ × NZ) : choiceColumnMask K w d m.1 *
      choiceColumnMask K w d m.2 * f m = A.indicator f m := by
    by_cases h₁ : choiceColumnMask K w d m.1 = 1
    · by_cases h₂ : choiceColumnMask K w d m.2 = 1
      · have hm : m ∈ A := ⟨h₁, h₂⟩
        simp only [Set.indicator_of_mem hm, h₁, h₂, one_mul]
      · have hz := choiceColumnMask_eq_zero_of_ne_one K w d m.2 h₂
        have hn : m ∉ A := fun hm => h₂ hm.2
        simp only [Set.indicator_of_notMem hn, hz, mul_zero, zero_mul]
    · have hz := choiceColumnMask_eq_zero_of_ne_one K w d m.1 h₁
      have hn : m ∉ A := fun hm => h₁ hm.1
      simp only [Set.indicator_of_notMem hn, hz, zero_mul]
  calc
    _ = ∑' m : NZ × NZ, A.indicator f m := tsum_congr hind
    _ = ∑' m : A, f m.val := (tsum_subtype A f).symm
    _ = _ := ((divisibleChosenPairEquiv K w d).tsum_eq (fun m => f m.val)).symm

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆
  (w.S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable (a : ℝ → ℝ)
  (ψ : ((v : (w.S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)

/-- The SAME actual masked whole sum, reindexed by genuinely divisible
chosen-generator product columns. All finite Mellin coordinates, the raw/R
coefficient, residual zeros and the unsplit joint kernel remain literal. -/
theorem tsum_choiceMaskedActualAnnular_eq_divisibleChosenPairs
    (c k d : NZ) (ν : ℝ) (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) (N : ℝ) :
    (∑' m : NZ × NZ, choiceMaskedActualAnnularJointSummand
      K w ζ hζ σ hS6 a ψ c k d ν φ R N m) =
      ∑' p : DivisibleChosenColumns K w d × DivisibleChosenColumns K w d,
        actualAnnularJointSummand K S (sixthPowerUnits K S) a ψ ζ hζ σ hS6
          c k d ν φ R N
          (divisibleChosenQuotient K w d p.1, divisibleChosenQuotient K w d p.2) := by
  change (∑' m : NZ × NZ, choiceColumnMask K w d m.1 *
    choiceColumnMask K w d m.2 *
      actualAnnularJointSummand K S (sixthPowerUnits K S) a ψ ζ hζ σ hS6
        c k d ν φ R N m) = _
  exact tsum_choiceColumnMask_pair_eq_divisibleChosenPairs K w d
    (actualAnnularJointSummand K S (sixthPowerUnits K S) a ψ ζ hζ σ hS6 c k d ν φ R N)

end HeckeGeneral.ThetaSkeleton.Physical.ActualDivisibleChoiceDraft
