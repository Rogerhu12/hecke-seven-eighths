import HeckeSkeleton.HighBinSupport.ActualInitialMultiplicative
import HeckeSkeleton.HighBinSupport.LocalBlockSummation
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# The four original exterior ideals as finite prime-exponent blocks

This is an actual equivalence of the original index types. Its inverse
uses the repository's `idealOfPrimeExponents`; the exterior condition is
proved from the support, with no chosen factorization or extra ideal data.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinActualInitial

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.HighBinActualGenerators
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def exteriorPrimeExponents (I : ExteriorIdeal K S) : ExteriorPrime K S →₀ ℕ :=
  (primeExponents I.val).subtypeDomain (fun p => p ∉ S)

@[simp] theorem exteriorPrimeExponents_apply (I : ExteriorIdeal K S)
    (p : ExteriorPrime K S) : exteriorPrimeExponents K S I p = primeExponents I.val p.val := rfl

def exteriorIdealOfPrimeExponents (e : ExteriorPrime K S →₀ ℕ) : ExteriorIdeal K S :=
  ⟨idealOfPrimeExponents e.extendDomain, by
    intro p hp
    have hmem := (mem_idealPrimeSupport_iff K (idealOfPrimeExponents e.extendDomain) p).mpr hp
    change p ∈ (primeExponents (idealOfPrimeExponents e.extendDomain)).support at hmem
    rw [primeExponents_idealOfPrimeExponents] at hmem
    exact Finsupp.support_extendDomain_subset e hmem⟩

@[simp] theorem exteriorPrimeExponents_of_exponents (e : ExteriorPrime K S →₀ ℕ) :
    exteriorPrimeExponents K S (exteriorIdealOfPrimeExponents K S e) = e := by
  simp only [exteriorPrimeExponents, exteriorIdealOfPrimeExponents,
    primeExponents_idealOfPrimeExponents, Finsupp.subtypeDomain_extendDomain]

@[simp] theorem exteriorIdealOfPrimeExponents_exponents (I : ExteriorIdeal K S) :
    exteriorIdealOfPrimeExponents K S (exteriorPrimeExponents K S I) = I := by
  apply Subtype.ext
  change idealOfPrimeExponents ((primeExponents I.val).subtypeDomain
    (fun p => p ∉ S)).extendDomain = I.val
  rw [Finsupp.extendDomain_subtypeDomain]
  · exact idealOfPrimeExponents_primeExponents I.val
  · intro p hp
    exact I.property p ((mem_idealPrimeSupport_iff K I.val p).mp hp)

def exteriorPrimeExponentEquiv : ExteriorIdeal K S ≃ (ExteriorPrime K S →₀ ℕ) where
  toFun := exteriorPrimeExponents K S
  invFun := exteriorIdealOfPrimeExponents K S
  left_inv := exteriorIdealOfPrimeExponents_exponents K S
  right_inv := exteriorPrimeExponents_of_exponents K S

@[simp] theorem primeExponents_exteriorIdealOfPrimeExponents
    (e : ExteriorPrime K S →₀ ℕ) (p : ExteriorPrime K S) :
    primeExponents (exteriorIdealOfPrimeExponents K S e).val p.val = e p :=
  congrArg (fun f : ExteriorPrime K S →₀ ℕ => f p)
    (exteriorPrimeExponents_of_exponents K S e)

@[simp] theorem exteriorIdealOfPrimeExponents_zero :
    exteriorIdealOfPrimeExponents K S 0 = primeSetIdeal K S ∅ := by
  have h0 : (0 : ExteriorPrime K S →₀ ℕ).extendDomain = 0 := by
    ext p
    by_cases hp : p ∉ S <;> simp [Finsupp.extendDomain_apply, hp]
  apply Subtype.ext
  apply Subtype.ext
  change (idealOfPrimeExponents (0 : ExteriorPrime K S →₀ ℕ).extendDomain).val = _
  simp only [h0, idealOfPrimeExponents_zero, primeSetIdeal_empty_val, Submonoid.coe_one]

theorem exteriorIdealOfPrimeExponents_add (e f : ExteriorPrime K S →₀ ℕ) :
    exteriorIdealOfPrimeExponents K S (e + f) =
      exteriorMul K S (exteriorIdealOfPrimeExponents K S e)
        (exteriorIdealOfPrimeExponents K S f) := by
  have hext : (e + f).extendDomain = e.extendDomain + f.extendDomain := by
    ext p
    by_cases hp : p ∉ S <;> simp [Finsupp.extendDomain_apply, hp]
  apply Subtype.ext
  change idealOfPrimeExponents (e + f).extendDomain =
    idealOfPrimeExponents e.extendDomain * idealOfPrimeExponents f.extendDomain
  rw [hext, idealOfPrimeExponents_add]

@[simp] theorem exteriorIdealOfPrimeExponents_single (p : ExteriorPrime K S) (n : ℕ) :
    exteriorIdealOfPrimeExponents K S (Finsupp.single p n) =
      exteriorPower K S (exteriorPrimeIdeal K S p) n := by
  apply Subtype.ext
  apply Subtype.ext
  change (idealOfPrimeExponents (Finsupp.single p n).extendDomain).val = p.val.asIdeal ^ n
  rw [Finsupp.extendDomain_single, idealOfPrimeExponents_single]

def fourPrimeExponents (I : FourIdealIndex K S) : ExteriorPrime K S →₀ FourExponent :=
  Finsupp.zipWith Prod.mk rfl
    (Finsupp.zipWith Prod.mk rfl (exteriorPrimeExponents K S I.1.1)
      (exteriorPrimeExponents K S I.1.2))
    (Finsupp.zipWith Prod.mk rfl (exteriorPrimeExponents K S I.2.1)
      (exteriorPrimeExponents K S I.2.2))

def fourIdealOfPrimeExponents (e : ExteriorPrime K S →₀ FourExponent) : FourIdealIndex K S :=
  ((exteriorIdealOfPrimeExponents K S (e.mapRange (fun n => n.1.1) rfl),
    exteriorIdealOfPrimeExponents K S (e.mapRange (fun n => n.1.2) rfl)),
    (exteriorIdealOfPrimeExponents K S (e.mapRange (fun n => n.2.1) rfl),
    exteriorIdealOfPrimeExponents K S (e.mapRange (fun n => n.2.2) rfl)))

@[simp] theorem fourPrimeExponents_of_exponents (e : ExteriorPrime K S →₀ FourExponent) :
    fourPrimeExponents K S (fourIdealOfPrimeExponents K S e) = e := by
  ext p <;>
    simp only [fourPrimeExponents, fourIdealOfPrimeExponents, Finsupp.zipWith_apply,
    exteriorPrimeExponents_of_exponents, Finsupp.mapRange_apply]

@[simp] theorem fourIdealOfPrimeExponents_exponents (I : FourIdealIndex K S) :
    fourIdealOfPrimeExponents K S (fourPrimeExponents K S I) = I := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    apply (exteriorPrimeExponentEquiv K S).injective
    change exteriorPrimeExponents K S _ = exteriorPrimeExponents K S _
    ext p
    simp only [fourIdealOfPrimeExponents, exteriorPrimeExponents_of_exponents,
      Finsupp.mapRange_apply, fourPrimeExponents, Finsupp.zipWith_apply]

def fourPrimeExponentEquiv : FourIdealIndex K S ≃ (ExteriorPrime K S →₀ FourExponent) where
  toFun := fourPrimeExponents K S
  invFun := fourIdealOfPrimeExponents K S
  left_inv := fourIdealOfPrimeExponents_exponents K S
  right_inv := fourPrimeExponents_of_exponents K S

theorem fourIdealOfPrimeExponents_injective :
    Function.Injective (fourIdealOfPrimeExponents K S) :=
  (fourPrimeExponentEquiv K S).symm.injective

@[simp] theorem fourIdealOfPrimeExponents_zero :
    fourIdealOfPrimeExponents K S 0 = fourIdealOne K S := by
  simp only [fourIdealOfPrimeExponents, Finsupp.mapRange_zero,
    exteriorIdealOfPrimeExponents_zero, fourIdealOne]

def primeFourIdealIndex (p : ExteriorPrime K S) (n : FourExponent) : FourIdealIndex K S :=
  ((exteriorPower K S (exteriorPrimeIdeal K S p) n.1.1,
    exteriorPower K S (exteriorPrimeIdeal K S p) n.1.2),
    (exteriorPower K S (exteriorPrimeIdeal K S p) n.2.1,
    exteriorPower K S (exteriorPrimeIdeal K S p) n.2.2))

@[simp] theorem fourIdealOfPrimeExponents_single (p : ExteriorPrime K S) (n : FourExponent) :
    fourIdealOfPrimeExponents K S (Finsupp.single p n) = primeFourIdealIndex K S p n := by
  simp only [fourIdealOfPrimeExponents, Finsupp.mapRange_single,
    exteriorIdealOfPrimeExponents_single, primeFourIdealIndex]

theorem fourIdealOfPrimeExponents_add (e f : ExteriorPrime K S →₀ FourExponent) :
    fourIdealOfPrimeExponents K S (e + f) =
      fourIdealMul K S (fourIdealOfPrimeExponents K S e) (fourIdealOfPrimeExponents K S f) := by
  have h₁₁ := Finsupp.mapRange_add (f := fun n : FourExponent => n.1.1)
    (hf := rfl) (fun _ _ => rfl) e f
  have h₁₂ := Finsupp.mapRange_add (f := fun n : FourExponent => n.1.2)
    (hf := rfl) (fun _ _ => rfl) e f
  have h₂₁ := Finsupp.mapRange_add (f := fun n : FourExponent => n.2.1)
    (hf := rfl) (fun _ _ => rfl) e f
  have h₂₂ := Finsupp.mapRange_add (f := fun n : FourExponent => n.2.2)
    (hf := rfl) (fun _ _ => rfl) e f
  simp only [fourIdealOfPrimeExponents, fourIdealMul, h₁₁, h₁₂, h₂₁, h₂₂,
    exteriorIdealOfPrimeExponents_add]

theorem fourIdealSupport_primeExponents (e : ExteriorPrime K S →₀ FourExponent)
    (p : ExteriorPrime K S) :
    primeExponents (fourIdealSupportIdeal K S (fourIdealOfPrimeExponents K S e)).val p.val =
      (e p).2.1 + ((e p).1.1 + 3 * (e p).1.2) + (e p).2.2 := by
  change primeExponents
    ((fourIdealOfPrimeExponents K S e).2.1.val *
      (completedIdeal K S (fourIdealOfPrimeExponents K S e).1.1
        (fourIdealOfPrimeExponents K S e).1.2).val *
      (fourIdealOfPrimeExponents K S e).2.2.val) p.val = _
  simp only [primeExponents_mul, Finsupp.add_apply, completedIdeal_primeExponents,
    fourIdealOfPrimeExponents, primeExponents_exteriorIdealOfPrimeExponents,
    Finsupp.mapRange_apply]

/-- A single prime block is coprime to the remaining finite support. -/
theorem fourIdealSupport_single_coprime (p : ExteriorPrime K S) (n : FourExponent)
    (e : ExteriorPrime K S →₀ FourExponent) (hp : p ∉ e.support) :
    IsCoprime (fourIdealSupportIdeal K S
      (fourIdealOfPrimeExponents K S (Finsupp.single p n))).val.val
      (fourIdealSupportIdeal K S (fourIdealOfPrimeExponents K S e)).val.val := by
  let J := fourIdealSupportIdeal K S (fourIdealOfPrimeExponents K S e)
  have hnot : ¬p.val.asIdeal ∣ J.val.val := by
    intro hdiv
    have hne : primeExponents J.val p.val ≠ 0 := Finsupp.mem_support_iff.mp
      ((mem_idealPrimeSupport_iff K J.val p.val).mpr hdiv)
    change primeExponents (fourIdealSupportIdeal K S
      (fourIdealOfPrimeExponents K S e)).val p.val ≠ 0 at hne
    rw [fourIdealSupport_primeExponents, Finsupp.notMem_support_iff.mp hp] at hne
    norm_num at hne
  have hcop : IsCoprime p.val.asIdeal J.val.val := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := p.val.isMaximal.eq_of_le h le_sup_left
    exact hnot (Ideal.dvd_iff_le.mpr (le_sup_right.trans_eq heq.symm))
  have hpow : (fourIdealSupportIdeal K S
      (fourIdealOfPrimeExponents K S (Finsupp.single p n))).val.val =
      p.val.asIdeal ^ (n.2.1 + (n.1.1 + 3 * n.1.2) + n.2.2) := by
    rw [fourIdealOfPrimeExponents_single]
    change (p.val.asIdeal ^ n.2.1 *
      (p.val.asIdeal ^ n.1.1 * (p.val.asIdeal ^ n.1.2 *
        (p.val.asIdeal ^ n.1.2 * p.val.asIdeal ^ n.1.2)))) *
      p.val.asIdeal ^ n.2.2 = _
    simp only [← pow_add]
    congr 1
    omega
  rw [hpow]
  exact hcop.pow_left

#print axioms fourPrimeExponentEquiv
#print axioms fourIdealSupport_single_coprime

end HeckeSkeleton.HighBinActualInitial
