import HeckeGeneral.Bridge.SIntegerAdelicPoisson
import HeckeGeneral.Bridge.SLocalIdeleAssembly
import HeckeGeneral.Arithmetic.SIntegerModulusCRT
import HeckeGeneral.Characters.LocalResidueCosetFourier

/-!
# The actual finite adelic test for an S-integer periodic coefficient

Only the additive exceptional set is enlarged by the support of the modulus.
At its new places the factors are actual integral residue coset indicators.
Consequently the finite test remains supported on the original S-integers
on the principal diagonal. Its value is the literal coefficient `f(d*a)`
times the original S-local test, including nonunit divisors and zero.

These constructions use the proved finiteness and CRT of the actual quotient.
Native compilation and declaration-audit status is recorded separately.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K

variable (c : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) (hc : c ≠ 0)


local notation "P" => sIntegerModulusPlaces K (S : Set (HeightOneSpectrum (𝓞 K))) c hc

theorem sIntegerModulusPlaces_disjoint : Disjoint S P := by
  apply Finset.disjoint_left.mpr
  intro v hvS hvP
  exact sIntegerModulusPlaces_not_mem K (S : Set (HeightOneSpectrum (𝓞 K)))
    c hc ⟨v, hvP⟩ hvS

/-- The new local centers are reductions of one actual global S-integer lift. -/
def sIntegerPeriodicLocalFactor
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K → ℂ :=
  if hvS : v ∈ S then h v else if hvP : v ∈ P then
    localIntegerResidueCosetIndicator K v
      (sIntegerModulusPrimeExponents K (S : Set (HeightOneSpectrum (𝓞 K))) c hc v)
      (sIntegerToLocalInteger K (S : Set (HeightOneSpectrum (𝓞 K))) v
        (sIntegerModulusPlaces_not_mem K _ c hc ⟨v, hvP⟩) (Quotient.out r))
  else fun _ => 1

@[simp] theorem sIntegerPeriodicLocalFactor_of_mem
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    sIntegerPeriodicLocalFactor K S c hc h r v = h v := by
  simp only [sIntegerPeriodicLocalFactor, dif_pos hv]

theorem sIntegerPeriodicLocalFactor_at_modulus
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) (v : P) :
    sIntegerPeriodicLocalFactor K S c hc h r v.val =
      localIntegerResidueCosetIndicator K v.val
        (sIntegerModulusPrimeExponents K (S : Set (HeightOneSpectrum (𝓞 K))) c hc v.val)
        (sIntegerToLocalInteger K (S : Set (HeightOneSpectrum (𝓞 K))) v.val
          (sIntegerModulusPlaces_not_mem K _ c hc v) (Quotient.out r)) := by
  have hvS : v.val ∉ S := sIntegerModulusPlaces_not_mem K _ c hc v
  simp only [sIntegerPeriodicLocalFactor,
    dif_neg hvS, dif_pos v.property]

theorem sIntegerPeriodicLocalFactor_locallyConstant_compactSupport
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S ∪ P) :
    IsLocallyConstant (sIntegerPeriodicLocalFactor K S c hc h r v) ∧
      HasCompactSupport (sIntegerPeriodicLocalFactor K S c hc h r v) := by
  by_cases hvS : v ∈ S
  · rw [sIntegerPeriodicLocalFactor_of_mem K S c hc h r v hvS]
    exact ⟨hlc v hvS, hcs v hvS⟩
  · have hvP : v ∈ P := (Finset.mem_union.mp hv).resolve_left hvS
    rw [sIntegerPeriodicLocalFactor_at_modulus K S c hc h r ⟨v, hvP⟩]
    exact localIntegerResidueCosetIndicator_locallyConstant_compactSupport K v _ _

/-- One residue class with the unchanged original local factors. -/
def sIntegerPeriodicCosetMask
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) : FiniteAdeleRing (𝓞 K) K → ℂ :=
  sIntegerFiniteMask K (S ∪ P) (sIntegerPeriodicLocalFactor K S c hc h r)

theorem sIntegerPeriodicCosetMask_locallyConstant_compactSupport
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (r : (OS ⧸ Ideal.span ({c} : Set OS))) :
    IsLocallyConstant (sIntegerPeriodicCosetMask K S c hc h r) ∧
      HasCompactSupport (sIntegerPeriodicCosetMask K S c hc h r) :=
  sIntegerFiniteMask_locallyConstant_compactSupport K (S ∪ P) _
    (fun v hv => (sIntegerPeriodicLocalFactor_locallyConstant_compactSupport
      K S c hc h hlc hcs r v hv).1)
    (fun v hv => (sIntegerPeriodicLocalFactor_locallyConstant_compactSupport
      K S c hc h hlc hcs r v hv).2)

theorem sIntegerPeriodicLocalFactor_principal_at_modulus
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) (a : OS) (v : P) :
    sIntegerPeriodicLocalFactor K S c hc h r v.val
        (algebraMap K (v.val.adicCompletion K) a.val) =
      if sIntegerModulusCRT K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
          (Ideal.Quotient.mk _ a) v =
        sIntegerModulusCRT K (S : Set (HeightOneSpectrum (𝓞 K))) c hc r v
      then 1 else 0 := by
  rw [sIntegerPeriodicLocalFactor_at_modulus]
  change localIntegerResidueCosetIndicator K v.val _ _
      (sIntegerToLocalInteger K (S : Set (HeightOneSpectrum (𝓞 K))) v.val
        (sIntegerModulusPlaces_not_mem K _ c hc v) a : v.val.adicCompletion K) = _
  rw [localIntegerResidueCosetIndicator_integer]
  change (if sIntegerToLocalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) v.val
      (sIntegerModulusPlaces_not_mem K _ c hc v) _ a =
    sIntegerToLocalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) v.val
      (sIntegerModulusPlaces_not_mem K _ c hc v) _ (Quotient.out r) then 1 else 0) = _
  simp only [← sIntegerModulusCRT_mk, Ideal.Quotient.mk_out]

/-- All local residue constraints together select exactly one actual global class. -/
theorem sIntegerPeriodicLocalFactor_prod_principal
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) (a : OS) :
    (∏ v : P, sIntegerPeriodicLocalFactor K S c hc h r v.val
      (algebraMap K (v.val.adicCompletion K) a.val)) =
      if Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) a = r then 1 else 0 := by
  simp only [sIntegerPeriodicLocalFactor_principal_at_modulus, Fintype.prod_ite_zero,
    Finset.prod_const_one]
  have heq : (∀ v : P,
      sIntegerModulusCRT K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
          (Ideal.Quotient.mk _ a) v =
        sIntegerModulusCRT K (S : Set (HeightOneSpectrum (𝓞 K))) c hc r v) ↔
      Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) a = r :=
    ⟨fun hv => (sIntegerModulusCRT K _ c hc).injective (funext hv),
      fun ha v => congrArg (fun b => sIntegerModulusCRT K _ c hc b v) ha⟩
  simp only [heq]

theorem sIntegerPeriodicCosetMask_apply
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) (a : OS) (z : FiniteAdeleRing (𝓞 K) K)
    (hout : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ P →
      z v ∈ v.adicCompletionIntegers K)
    (hcoord : ∀ v : P, z v.val = algebraMap K (v.val.adicCompletion K) a.val) :
    sIntegerPeriodicCosetMask K S c hc h r z =
      (∏ v ∈ S, h v (z v)) *
        (if Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) a = r then 1 else 0) := by
  unfold sIntegerPeriodicCosetMask sIntegerFiniteMask
  rw [if_pos hout, mul_one,
    Finset.prod_union (sIntegerModulusPlaces_disjoint K S c hc)]
  congr 1
  · apply Finset.prod_congr rfl
    intro v hv
    rw [sIntegerPeriodicLocalFactor_of_mem K S c hc h r v hv]
  · rw [← Finset.prod_finset_coe]
    simp_rw [hcoord]
    exact sIntegerPeriodicLocalFactor_prod_principal K S c hc h r a

/-- Every nonzero coset mask value is integral away from the original S. -/
theorem sIntegerPeriodicCosetMask_nonzero_integral
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : (OS ⧸ Ideal.span ({c} : Set OS))) (z : FiniteAdeleRing (𝓞 K) K)
    (hz : sIntegerPeriodicCosetMask K S c hc h r z ≠ 0) :
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → z v ∈ v.adicCompletionIntegers K := by
  have hp := mul_ne_zero_iff.mp hz
  have hout : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ P →
      z v ∈ v.adicCompletionIntegers K := by
    by_contra hnot
    exact hp.2 (if_neg hnot)
  intro v hvS
  by_cases hvP : v ∈ P
  · have hlocal := Finset.prod_ne_zero_iff.mp hp.1 v (Finset.mem_union_right S hvP)
    rw [sIntegerPeriodicLocalFactor_at_modulus K S c hc h r ⟨v, hvP⟩] at hlocal
    exact localIntegerResidueCosetIndicator_nonzero_integral K v _ _ _ hlocal
  · exact hout v (by simp only [Finset.mem_union, not_or]; exact ⟨hvS, hvP⟩)

/-- The actual arbitrary periodic coefficient, with its literal nonunit dilation. -/
def sIntegerPeriodicFiniteTest
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (z : FiniteAdeleRing (𝓞 K) K) : ℂ :=
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
  ∑ r : (OS ⧸ Ideal.span ({c} : Set OS)), f (Ideal.Quotient.mk _ d * r) * sIntegerPeriodicCosetMask K S c hc h r z

theorem sIntegerPeriodicFiniteTest_locallyConstant_compactSupport
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) :
    IsLocallyConstant (sIntegerPeriodicFiniteTest K S c hc h f d) ∧
      HasCompactSupport (sIntegerPeriodicFiniteTest K S c hc h f d) := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
  have hsum : ∀ A : Finset (OS ⧸ Ideal.span ({c} : Set OS)),
      IsLocallyConstant (fun z => ∑ r ∈ A,
        f (Ideal.Quotient.mk _ d * r) * sIntegerPeriodicCosetMask K S c hc h r z) ∧
      HasCompactSupport (fun z => ∑ r ∈ A,
        f (Ideal.Quotient.mk _ d * r) * sIntegerPeriodicCosetMask K S c hc h r z) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        constructor
        · exact IsLocallyConstant.const 0
        · change HasCompactSupport (0 : FiniteAdeleRing (𝓞 K) K → ℂ)
          exact HasCompactSupport.zero
    | @insert r A hr ih =>
        have hmask := sIntegerPeriodicCosetMask_locallyConstant_compactSupport
          K S c hc h hlc hcs r
        simpa only [Finset.sum_insert hr] using
          (show IsLocallyConstant (fun z =>
              f (Ideal.Quotient.mk _ d * r) * sIntegerPeriodicCosetMask K S c hc h r z +
                ∑ b ∈ A, f (Ideal.Quotient.mk _ d * b) *
                  sIntegerPeriodicCosetMask K S c hc h b z) ∧ HasCompactSupport (fun z =>
              f (Ideal.Quotient.mk _ d * r) * sIntegerPeriodicCosetMask K S c hc h r z +
                ∑ b ∈ A, f (Ideal.Quotient.mk _ d * b) *
                  sIntegerPeriodicCosetMask K S c hc h b z) from
            ⟨((IsLocallyConstant.const _).mul hmask.1).add ih.1,
              hmask.2.mul_left.add ih.2⟩)
  exact hsum Finset.univ

theorem sIntegerPeriodicFiniteTest_apply
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d a : OS) (z : FiniteAdeleRing (𝓞 K) K)
    (hout : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ P →
      z v ∈ v.adicCompletionIntegers K)
    (hcoord : ∀ v : P, z v.val = algebraMap K (v.val.adicCompletion K) a.val) :
    sIntegerPeriodicFiniteTest K S c hc h f d z =
      f (Ideal.Quotient.mk (Ideal.span ({c} : Set OS)) (d * a)) * ∏ v ∈ S, h v (z v) := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
  unfold sIntegerPeriodicFiniteTest
  simp_rw [sIntegerPeriodicCosetMask_apply K S c hc h _ a z hout hcoord]
  simp [mul_ite, ← map_mul]

theorem sIntegerPeriodicFiniteTest_zero_of_not_integral
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (f : (OS ⧸ Ideal.span ({c} : Set OS)) → ℂ) (d : OS) (z : FiniteAdeleRing (𝓞 K) K)
    (hz : ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → z v ∈ v.adicCompletionIntegers K) :
    sIntegerPeriodicFiniteTest K S c hc h f d z = 0 := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) c hc
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
  apply Finset.sum_eq_zero
  intro r _
  have hmask : sIntegerPeriodicCosetMask K S c hc h r z = 0 := by
    by_contra hne
    exact hz (sIntegerPeriodicCosetMask_nonzero_integral K S c hc h r z hne)
  rw [hmask, mul_zero]

end HeckeGeneral.Bridge

