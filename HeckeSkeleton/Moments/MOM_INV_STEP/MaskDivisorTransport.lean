import HeckeSkeleton.Moments.MOM_INV_STEP.ActualDivisorSectors

/-!
# The reconstruction sector map comes from the actual mask generators

The principal generator used by Poisson is a function of its localized
ideal. Consequently its computed unit-sector translation is a function
of the contracted exterior ideal. This supplies the fixed two-ideal
sector equivalence required by the reconstruction fiber count, while
retaining the literal generators used in both Poisson transforms.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.MaskDivisorTransport

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ActualDivisorSectors CanonicalChildren
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

/-- The same principal-generator operation used by the actual mask,
now indexed by its full exterior ideal. -/
def idealGenerator (I : Ext) : NonzeroRingElements OS :=
  ⟨Submodule.IsPrincipal.generator (I.val.val.map (algebraMap (𝓞 K) OS)), by
    apply (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).not.mp
    intro hI
    exact D.generator_ne_zero I
      (Ideal.span_singleton_eq_bot.mp ((D.generator_span I).trans hI))⟩

theorem idealGenerator_span (I : Ext) :
    Ideal.span ({(idealGenerator K S D I).val} : Set OS) =
      I.val.val.map (algebraMap (𝓞 K) OS) :=
  Ideal.span_singleton_generator _

theorem divisorIdeal_idealGenerator (I : Ext) :
    divisorIdeal K S (idealGenerator K S D I) = I := by
  apply Subtype.ext
  apply Subtype.ext
  rw [divisorIdeal_val, sIntegerModulusContraction, idealGenerator_span]
  exact under_map_coprime_sIntegerIdeal K Sset I.val.val
    (sexticIdeal_coprime_S K Sset I.val.val I.property)

/-- No unit discrepancy is discarded: the actual mask generator is
literally the principal generator indexed by its contracted ideal. -/
theorem maskGenerator_eq_idealGenerator (M : Finset (HeightOneSpectrum OS)) :
    sIntegerMaskGenerator K Sset M =
      idealGenerator K S D (divisorIdeal K S (sIntegerMaskGenerator K Sset M)) := by
  have hmap : (divisorIdeal K S (sIntegerMaskGenerator K Sset M)).val.val.map
      (algebraMap (𝓞 K) OS) = IdealMobiusMask.primeProduct M := by
    rw [divisorIdeal_val, map_sIntegerModulusContraction]
    change Ideal.span ({IdealMobiusMask.maskGenerator M} : Set OS) = _
    exact Ideal.span_singleton_generator _
  apply Subtype.ext
  change IdealMobiusMask.maskGenerator M =
    Submodule.IsPrincipal.generator
      ((divisorIdeal K S (sIntegerMaskGenerator K Sset M)).val.val.map (algebraMap (𝓞 K) OS))
  rw [hmap]
  rfl

/-- Outside the exterior locus the identity extension is harmless;
every actual mask divisor lies on the proved exterior branch. -/
def idealTransport (I : Ideal (𝓞 K)) : Sector ≃ Sector :=
  if hI : IsExterior K Sset I then
    divisorTransport K S Γ D (idealGenerator K S D (exteriorOf K Sset I hI))
  else Equiv.refl _

theorem idealTransport_exterior (I : Ext) :
    idealTransport K S Γ D I.val.val =
      divisorTransport K S Γ D (idealGenerator K S D I) := by
  rw [idealTransport, dif_pos (exterior_isExterior K Sset I)]
  rfl

theorem idealTransport_mask_generator (M : Finset (HeightOneSpectrum OS)) :
    idealTransport K S Γ D (divisorIdeal K S (sIntegerMaskGenerator K Sset M)).val.val =
      divisorTransport K S Γ D (sIntegerMaskGenerator K Sset M) := by
  rw [idealTransport_exterior, ← maskGenerator_eq_idealGenerator K S D M]

def directIdealTransport (I : Ideal (𝓞 K)) : Sector ≃ Sector :=
  if hI : IsExterior K Sset I then
    directDivisorTransport K S Γ D (idealGenerator K S D (exteriorOf K Sset I hI))
  else Equiv.refl _

theorem directIdealTransport_exterior (I : Ext) :
    directIdealTransport K S Γ D I.val.val =
      directDivisorTransport K S Γ D (idealGenerator K S D I) := by
  rw [directIdealTransport, dif_pos (exterior_isExterior K Sset I)]
  rfl

theorem directIdealTransport_mask_generator (M : Finset (HeightOneSpectrum OS)) :
    directIdealTransport K S Γ D (divisorIdeal K S (sIntegerMaskGenerator K Sset M)).val.val =
      directDivisorTransport K S Γ D (sIntegerMaskGenerator K Sset M) := by
  rw [directIdealTransport_exterior, ← maskGenerator_eq_idealGenerator K S D M]

/-- The retained first divisor enters directly. The second divisor,
which also enters the fourth-power label, uses the inverse unit. This
is the actual two-ideal equivalence used by the reconstruction count. -/
def reconstructionTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector) :=
  fun I J => (directIdealTransport K S Γ D I).trans (idealTransport K S Γ D J)

theorem reconstructionTransport_actual (M N : Finset (HeightOneSpectrum OS)) (ξ : Sector) :
    reconstructionTransport K S Γ D
        (divisorIdeal K S (sIntegerMaskGenerator K Sset M)).val.val
        (divisorIdeal K S (sIntegerMaskGenerator K Sset N)).val.val ξ =
      divisorTransport K S Γ D (sIntegerMaskGenerator K Sset N)
        (directDivisorTransport K S Γ D (sIntegerMaskGenerator K Sset M) ξ) := by
  simp only [reconstructionTransport, Equiv.trans_apply,
    directIdealTransport_mask_generator, idealTransport_mask_generator]

end HeckeSkeleton.Moments.MOM_INV_STEP.MaskDivisorTransport

end
