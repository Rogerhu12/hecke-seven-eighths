import HeckeSkeleton.LowEnergy.ActualReflectionReindex
import HeckeSkeleton.LowEnergy.FrozenChargeCore

/-!
# The actual minimum ideals and the low conductor charges

The three charged ideals are built from the literal frozen state.  The
numerator identity and the inverse norm charge are proved from actual prime
products, rather than supplied as numerical ledger assumptions.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualFrozenCharges

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSymbolProducts HeckeSkeleton.LowEnergy.ActualFrozenCube
open HeckeSkeleton.LowEnergy.ActualLocalWeylTable
open HeckeSkeleton.LowEnergy.ActualFrozenIndependence
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def minimumLinearPrimes {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) : Finset (ExteriorPrime K S) :=
  FrozenChargeCore.linearPrimes s.active (fun p => primeExponents s.minimum.val p.val)

def minimumCubePrimes {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) : Finset (ExteriorPrime K S) :=
  FrozenChargeCore.cubePrimes s.active (fun p => primeExponents s.minimum.val p.val)

def minimumSmallPrimes {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) : Finset (ExteriorPrime K S) :=
  FrozenChargeCore.smallPrimes s.active (fun p => (frozenDigit K S frozen p).val)
    (fun p => primeExponents s.minimum.val p.val)

/-- The primes with minimum numerator exponent one. -/
def minimumLinearIdeal {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) : ExteriorIdeal K S :=
  primeSetIdeal K S (minimumLinearPrimes K S s)

/-- The primes with minimum numerator exponent three, each taken once. -/
def minimumCubeIdeal {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) : ExteriorIdeal K S :=
  primeSetIdeal K S (minimumCubePrimes K S s)

/-- The zero-exponent primes whose local digit is zero or four. -/
def minimumSmallIdeal {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) : ExteriorIdeal K S :=
  primeSetIdeal K S (minimumSmallPrimes K S s)

theorem primeSetIdeal_norm (T : Finset (ExteriorPrime K S)) :
    exteriorNorm K S (primeSetIdeal K S T) =
      ∏ p ∈ T, (p.val.asIdeal.absNorm : ℝ) := by
  unfold exteriorNorm
  rw [primeSetIdeal_val, map_prod, Nat.cast_prod]

theorem prime_norm_pos (p : ExteriorPrime K S) : 0 < (p.val.asIdeal.absNorm : ℝ) := by
  exact exteriorNorm_pos K S (exteriorPrimeIdeal K S p)

theorem prime_norm_one_le (p : ExteriorPrime K S) : 1 ≤ (p.val.asIdeal.absNorm : ℝ) := by
  have h := Ideal.absNorm_pos_of_nonZeroDivisors (exteriorPrimeIdeal K S p).val
  have h1 : 1 ≤ p.val.asIdeal.absNorm := h
  exact_mod_cast h1

theorem minimum_norm_prime_product {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) :
    exteriorNorm K S s.minimum =
      ∏ p ∈ s.active, (p.val.asIdeal.absNorm : ℝ) ^ primeExponents s.minimum.val p.val := by
  have hF : (primeExponents s.minimum.val).support ⊆ s.active.image Subtype.val := by
    intro p hp
    have hd := (exponent_ne_zero_iff_dvd s.minimum.val p).mp (Finsupp.mem_support_iff.mp hp)
    let ep : ExteriorPrime K S := ⟨p, s.minimum.property p hd⟩
    have he : ep ∈ s.active := s.minimum_support
      ((mem_exteriorSupport_iff K S s.minimum ep).mpr hd)
    exact Finset.mem_image.mpr ⟨ep, he, rfl⟩
  let f : Ideal (𝓞 K) →* ℝ :=
    (Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom
  have h := map_idealOfPrimeExponents f (primeExponents s.minimum.val)
  rw [idealOfPrimeExponents_primeExponents] at h
  rw [Finsupp.prod_of_support_subset _ hF _ (fun _ _ => pow_zero _)] at h
  change exteriorNorm K S s.minimum =
    ∏ p ∈ s.active.image Subtype.val, (p.asIdeal.absNorm : ℝ) ^ primeExponents s.minimum.val p at h
  rw [Finset.prod_image] at h
  · exact h
  · intro p _ q _ hpq
    exact Subtype.ext hpq

/-- `N(a_min)=N(N_min) N(B_min)^3`, for every actual frozen state. -/
theorem minimum_norm_decomposition {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) :
    exteriorNorm K S s.minimum = exteriorNorm K S (minimumLinearIdeal K S s) *
      exteriorNorm K S (minimumCubeIdeal K S s) ^ 3 := by
  rw [minimum_norm_prime_product]
  unfold minimumLinearIdeal minimumCubeIdeal
  rw [primeSetIdeal_norm, primeSetIdeal_norm]
  exact FrozenChargeCore.minimum_norm_identity s.active
    (fun p => (p.val.asIdeal.absNorm : ℝ)) (fun p => primeExponents s.minimum.val p.val)
    (fun p _ => s.minimum_values p.val)

/-- The exponent-one minimum ideal lies inside the active frozen radical. -/
theorem minimum_linear_norm_le_active {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) :
    exteriorNorm K S (minimumLinearIdeal K S s) ≤
      exteriorNorm K S (primeSetIdeal K S s.active) := by
  unfold minimumLinearIdeal
  rw [primeSetIdeal_norm, primeSetIdeal_norm]
  exact FrozenChargeCore.linear_norm_le_active s.active
    (fun p => (p.val.asIdeal.absNorm : ℝ)) (fun p => primeExponents s.minimum.val p.val)
    (fun p _ => prime_norm_one_le K S p)

/-- Squared local charges retain both the small zero branch and the minimum
cube branch.  A forbidden positive local digit only improves this inequality. -/
theorem stateMajorant_sq_le_inverse_charge {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) :
    stateMajorant K S s ^ 2 ≤
      (exteriorNorm K S (minimumSmallIdeal K S s) *
        exteriorNorm K S (minimumCubeIdeal K S s))⁻¹ := by
  unfold minimumSmallIdeal minimumCubeIdeal
  rw [primeSetIdeal_norm, primeSetIdeal_norm]
  exact FrozenChargeCore.frozen_majorant_square_le s.active
    (fun p => (p.val.asIdeal.absNorm : ℝ)) (fun p => (frozenDigit K S frozen p).val)
    (fun p => primeExponents s.minimum.val p.val)
    (fun p _ => prime_norm_pos K S p) (fun p _ => s.minimum_values p.val)

/-- The fourth low-ledger relation holds for every possible frozen state,
not only for states occurring in a particular reflection term. -/
theorem state_active_norm_sq_le_powerful (I : ExteriorIdeal K S)
    (s : FrozenState K S (exteriorPowerfulPart K S I) (primeSetIdeal K S ∅)) :
    exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 ≤
      exteriorNorm K S (exteriorPowerfulPart K S I) := by
  apply norm_radical_sq_le_powerful
  · exact HeckeGeneral.Arithmetic.IdealMobiusMask.squarefree_primeProduct _
  · exact powerfulPart_powerful I.val
  · intro p hp
    let ep : ExteriorPrime K S := ⟨p, (primeSetIdeal K S s.active).property p hp⟩
    have he : ep ∈ s.active := (prime_dvd_primeSetIdeal_iff K S s.active ep).mp hp
    have hs := s.active_subset he
    rw [exteriorSupport_emptyPrimeIdeal, Finset.union_empty] at hs
    exact (mem_exteriorSupport_iff K S (exteriorPowerfulPart K S I) ep).mp hs

/-- The conductor charge also holds on a fixed powerful fibre, so the
block estimate need not retain a representative of the original row. -/
theorem state_active_norm_sq_le_of_powerful {frozen puncture : ExteriorIdeal K S}
    (hfrozen : Powerful frozen.val) (hpuncture : puncture = primeSetIdeal K S ∅)
    (s : FrozenState K S frozen puncture) :
    exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 ≤ exteriorNorm K S frozen := by
  apply norm_radical_sq_le_powerful
  · exact HeckeGeneral.Arithmetic.IdealMobiusMask.squarefree_primeProduct _
  · exact hfrozen
  · intro p hp
    let ep : ExteriorPrime K S := ⟨p, (primeSetIdeal K S s.active).property p hp⟩
    have he : ep ∈ s.active := (prime_dvd_primeSetIdeal_iff K S s.active ep).mp hp
    have hs := s.active_subset he
    rw [hpuncture, exteriorSupport_emptyPrimeIdeal, Finset.union_empty] at hs
    exact (mem_exteriorSupport_iff K S frozen ep).mp hs

/-- These are exactly the four arithmetic inputs used by the low numerical
closure.  No conductor ledger is postulated. -/
theorem actual_low_charges (I : ExteriorIdeal K S)
    (s : FrozenState K S (exteriorPowerfulPart K S I) (primeSetIdeal K S ∅)) :
    exteriorNorm K S s.minimum = exteriorNorm K S (minimumLinearIdeal K S s) *
        exteriorNorm K S (minimumCubeIdeal K S s) ^ 3 ∧
    exteriorNorm K S (minimumLinearIdeal K S s) ≤ exteriorNorm K S (primeSetIdeal K S s.active) ∧
    stateMajorant K S s ^ 2 ≤
      (exteriorNorm K S (minimumSmallIdeal K S s) *
        exteriorNorm K S (minimumCubeIdeal K S s))⁻¹ ∧
    exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 ≤
      exteriorNorm K S (exteriorPowerfulPart K S I) :=
  ⟨minimum_norm_decomposition K S s, minimum_linear_norm_le_active K S s,
    stateMajorant_sq_le_inverse_charge K S s, state_active_norm_sq_le_powerful K S I s⟩

#print axioms minimum_norm_decomposition
#print axioms stateMajorant_sq_le_inverse_charge
#print axioms actual_low_charges

end HeckeSkeleton.LowEnergy.ActualFrozenCharges
