import HeckeSkeleton.LowEnergy.ActualFrozenIndependence
import HeckeSkeleton.LowEnergy.ActualRawHybrid

/-!
# Exact entry of the actual reflected coefficient into the actual hybrid row

Both pair-dependent masks are present in `hybridAtom`.  On the original
reflection support they equal one by proved coprimality.  Their presence is
retained when forming the larger finite hybrid row to which the sieve applies.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualHybridEntry

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualSymbols
open HeckeSkeleton.LowEnergy.ActualFrozenCube HeckeSkeleton.LowEnergy.ActualFrozenMajorant
open HeckeSkeleton.LowEnergy.ActualFrozenIndependence
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem quadraticKernel_exterior_product (hD : AllowedGeneratorInput K S D)
    (k c b : ExteriorIdeal K S) :
    quadraticKernel K S D k.val.val (c.val.val * b.val.val) =
      idealSymbol K S D k (D.generator c * D.generator b) ^ 3 := by
  have hk : IsExterior K S k.val.val := ⟨nonZeroDivisors.coe_ne_zero k.val, k.property⟩
  have hcb : IsExterior K S (c.val.val * b.val.val) :=
    ⟨nonZeroDivisors.coe_ne_zero (exteriorMul K S c b).val, (exteriorMul K S c b).property⟩
  rw [quadraticKernel, sexticSymbol_of_exterior K S D _ _ hk hcb]
  change idealSymbol K S D k (D.generator (exteriorMul K S c b)) ^ 3 = _
  rw [actualSymbol_mul_right K S D hD]
  have hmul : idealSymbol K S D k (D.generator c * D.generator b) =
      idealSymbol K S D k (D.generator c) * idealSymbol K S D k (D.generator b) :=
    (elementSymbolHom K S D k).map_mul _ _
  rw [hmul]

theorem cubicKernel_exterior (P c : ExteriorIdeal K S) :
    cubicKernel K S D P.val.val c.val.val =
      idealSymbol K S D P (D.generator c) ^ (-2 : ℤ) := by
  exact HeckeSkeleton.LowEnergy.ActualSieveDictionary.cubicKernel_on_exterior K S D P c

theorem activeMarked_coprime_moving (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    IsCoprime d.moving.val.val (activeMarkedIdeal K S d i).val.val := by
  apply Ideal.coprime_of_no_prime_ge
  intro P hm hP hprime
  have hP0 : P ≠ ⊥ := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero d.moving.val (le_bot_iff.mp (hz ▸ hm))
  let p : HeightOneSpectrum (𝓞 K) := ⟨P, hprime, hP0⟩
  let ep : ExteriorPrime K S := ⟨p, d.moving.property p (Ideal.dvd_iff_le.mpr hm)⟩
  have hep : ep ∈ i.activeMarks := (prime_dvd_primeSetIdeal_iff K S i.activeMarks ep).mp
    (Ideal.dvd_iff_le.mpr hP)
  exact (d.marks_coprime ep (i.marks_subset hep)).1 (Ideal.dvd_iff_le.mpr hm)

/-- This is precisely one summand of HeckePort's `hybridRow`. -/
def hybridAtom (a β : ℂ) (k P c b : Ideal (𝓞 K)) : ℂ :=
  a / (Real.sqrt (P.absNorm : ℝ) : ℂ) *
    (if IsCoprime k P then 1 else 0) *
    (β * quadraticKernel K S D k (c * b) * cubicKernel K S D P c *
      (if IsCoprime P b then 1 else 0))

/-- Both masks survive in the exact actual coefficient identity. -/
theorem reflectedTerm_eq_hybridAtom (hD : AllowedGeneratorInput K S D)
    (d : MarkedDatum K S) (i : ReflectionIndex K S d)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D d i F θ V X =
      (∏ p ∈ d.marks \ i.activeMarks, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
      separatedRowCoefficient K S D θ d.rowUnit d.frozen (numeratorMinimum K S d i)
        i.activeFrozen (frequencyUnit K S d i) d.moving *
      hybridAtom K S D
        (separatedMarkCoefficient K S D θ d.rowUnit d.frozen (numeratorMinimum K S d i)
          i.activeFrozen i.activeMarks (frequencyUnit K S d i))
        (fullCubeCoefficient K S D (frozenOnlyDatum K S d) (frozenOnlyIndex K S d i) θ)
        d.moving.val.val (activeMarkedIdeal K S d i).val.val i.c.val.val
        (fullCubeIdeal K S d i).val.val *
      mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
        (frequencyClass K S D d i) V 0
        (X * exteriorNorm K S (numeratorMinimum K S d i) * exteriorNorm K S i.c *
          exteriorNorm K S (fullCubeIdeal K S d i) ^ 3 /
          (exteriorNorm K S d.moving * exteriorNorm K S (activeFrozenIdeal K S d i) *
            exteriorNorm K S (activeMarkedIdeal K S d i)) ^ 2) := by
  rw [reflectedTerm_eq_separatedFullCube K S D d i hD F θ V X]
  unfold hybridAtom
  rw [if_pos (activeMarked_coprime_moving K S d i),
    if_pos (fullCube_coprime_activeMarked K S d i).symm,
    quadraticKernel_exterior_product K S D hD,
    cubicKernel_exterior]
  simp only [exteriorNorm]
  ring

/-- The exact finite exterior row, with the original zeros and coefficients. -/
def exteriorHybridRow (Pset nset bset : Finset (ExteriorIdeal K S))
    (a : Ideal (𝓞 K) → ℂ) (β : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : ExteriorIdeal K S) : ℂ :=
  ∑ P ∈ Pset, ∑ n ∈ nset, ∑ b ∈ bset,
    hybridAtom K S D (a P.val.val) (β n.val.val b.val.val)
      k.val.val P.val.val n.val.val b.val.val

/-- Finite exact reindexing is the interface consumed by `actual_hybrid_energy`.
No support is replaced by a norm ball, and no coefficient is row-dependent. -/
theorem exteriorHybridRow_eq_hybridRow
    (Pset nset bset : Finset (ExteriorIdeal K S))
    (a : Ideal (𝓞 K) → ℂ) (β : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : ExteriorIdeal K S) :
    exteriorHybridRow K S D Pset nset bset a β k =
      hybridRow (cubicKernel K S D) (quadraticKernel K S D)
        (Pset.image (fun P => P.val.val)) (nset.image (fun n => n.val.val))
        (bset.image (fun b => b.val.val)) a β k.val.val := by
  have hinj : Function.Injective (fun I : ExteriorIdeal K S => I.val.val) := by
    intro I J h
    exact Subtype.ext (Subtype.ext h)
  unfold exteriorHybridRow hybridRow hybridInner hybridAtom
  rw [Finset.sum_image (fun I _ J _ h => hinj h)]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_image (fun I _ J _ h => hinj h)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_image (fun I _ J _ h => hinj h)]
  rw [Finset.mul_sum]

end HeckeSkeleton.LowEnergy.ActualHybridEntry
