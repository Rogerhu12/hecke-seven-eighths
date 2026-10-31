import Expansion.ActualRecipeData
import Expansion.PhysicalRecipeFiniteSums
import Expansion.PhysicalOuterRowPartition

/-!
# The actual global expansion identity

The actual normalized physical probe is expanded on its original initial
contours.  Its unique principal row and every nonprincipal row are then
transported by their proved integral identities.  Exact finite reindexing
identifies the resulting shell/bin/sector sum with the active blocks of
the same actual recipe.

The six tail terms are precisely `actualPhysicalExpansionTail`.  In
particular the principal initial complement occurs once in the principal
tail, and every other initial complement occurs once in the nonprincipal
tail.  The statement has only the original arithmetic, measure and common
boundary inputs; the expansion identity is its conclusion.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open Expansion.PhysicalInitialMellin
open ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

local instance actualIdentity_sectorFintype : Fintype (SixthUnitClasses K Sset) :=
  Fintype.ofFinite _

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)]
variable [BorelSpace (AdeleRing (𝓞 K) K)]
variable (muA : Measure (AdeleRing (𝓞 K) K)) [muA.IsAddHaarMeasure]

variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (omega psi : HeckeCharacter K) (g : PrimeWindowGeometry)
variable {B : ℝ} (hpsi : psi ∈ HeckePacket K omega)
variable (hB0 : 51 / 100 ≤ B) (hB1 : B ≤ 1)
variable (hboundary : ∀ chi : HeckePacketIndex K omega,
  ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
local notation "E" => arithmeticHighEulerData K Sset P psi
local notation "muS" => (fun p : Sset => mu p.val)
variable (lam zeta eCap : ℝ)
variable (q : PhysicalRecipeParameters K (S : Set (HeightOneSpectrum (𝓞 K))) P omega psi g
  (arithmeticHighEulerData K (S : Set (HeightOneSpectrum (𝓞 K))) P psi) hpsi hB0 hB1 hboundary
  (fun p : (S : Set (HeightOneSpectrum (𝓞 K))) => mu p.val) ∅ lam zeta eCap)
local notation "X" => actualPhysicalRecipe K S mu P omega psi g hpsi hB0 hB1 hboundary
  lam zeta eCap q

/-- The active high blocks of the actual parameter choice equal the
original scheduled contour values, with no additional labels or weights. -/
theorem actualPhysicalRecipe_block_sum (Z H : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    (∑ b, (((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).block b).value) =
      ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K Sset B q.e,
          physicalRecipeBlockValue K Sset P E omega psi hpsi hB0 hB1 q.e_pos hboundary
            muS g ∅ zeta Z H j c := by
  exact physicalRecipeExpansion_toHigh_block_sum K Sset P omega psi g E hpsi hB0 hB1
    q.e_pos hboundary muS ∅ lam zeta q.width q.k q.width_pos
    (fun Z H => actualPrincipalRetained K S mu P psi g Z H B q.e)
    (fun Z H => actualSmallRetained K S mu P psi g Z H B q.e)
    (fun Z H => actualLargeRetained K S mu P psi g Z H zeta)
    (actualPhysicalExpansionTail K S mu P omega psi g hpsi hB0 hB1 hboundary q.e_pos zeta)
    Z H hZ hH

include nu muA in
/-- The complete actual expansion identity for the same all-scale raw
recipe, on precisely its original active scale and height guard. -/
theorem actualPhysicalRecipe_identity
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (hzero : additiveFourierAtZero K Sset muS P.additive = 0)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (hN : physicalResidueNormalizer K Sset muS P ≠ 0)
    (hB : 7 / 8 < B) (he1 : q.e ≤ 1 / 10000) (hzeta : 0 < zeta)
    (Z H : ℝ) (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    normalizedProbe K Sset muS P psi g ∅ Z - principalLineProbe K Sset P psi Z =
      ((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).principal +
      ((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).small +
      ((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).large +
      (∑ b, (((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).block b).value) +
      ((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).tail := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  have hZ1 : 1 < Z := (by norm_num : (1 : ℝ) < 2 ^ (16 : ℕ)).trans_le hZ
  have hZpos : 0 < Z := zero_lt_one.trans hZ1
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hinitial := normalizedProbe_eq_principal_add_nonprincipal K S mu nu muA P hzero
    hAllowed psi hcal hunram g ∅ hZpos
  have hprincipal := actualPrincipal_initial_integral_expansion K S mu nu P omega psi
    hpsi hAllowed hcal hunram hN g hB hB1 q.e_pos q.e_small hZpos hH0 hboundary
  have hnonprincipal := actual_nonprincipal_initial_recipe_expansion K S mu nu hcomplex
    P omega psi hpsi hAllowed hcal hunram g hB0 hB hB1 q.e_pos he1 hzeta hZ1 hH hboundary
  rw [actualPhysicalRecipe_block_sum K S mu P omega psi g hpsi hB0 hB1 hboundary
    lam zeta eCap q Z H hZ hH]
  change normalizedProbe K Sset muS P psi g ∅ Z - principalLineProbe K Sset P psi Z =
    actualPrincipalRetained K S mu P psi g Z H B q.e +
    actualSmallRetained K S mu P psi g Z H B q.e +
    actualLargeRetained K S mu P psi g Z H zeta +
    (∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
      ∑ c : PhysicalRecipeChoice K Sset B q.e,
        physicalRecipeBlockValue K Sset P E omega psi hpsi hB0 hB1 q.e_pos hboundary
          muS g ∅ zeta Z H j c) +
    actualPhysicalExpansionTail K S mu P omega psi g hpsi hB0 hB1 hboundary q.e_pos zeta Z H
  unfold actualPhysicalExpansionTail
  rw [hinitial, hnonprincipal]
  linear_combination hprincipal

end Expansion.Project

#print axioms Expansion.Project.actualPhysicalRecipe_block_sum
#print axioms Expansion.Project.actualPhysicalRecipe_identity
