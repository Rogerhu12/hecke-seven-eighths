import Expansion.PhysicalRecipeParameters
import Expansion.PhysicalRecipeRemainders
import Expansion.ActualPrincipalExpansion
import Expansion.ActualRetainedComponents

/-!
# One actual recipe with literal retained components and contour tails

The detector parameters are chosen once before the height exponent.  The
four components below are then the actual principal remainders, small
finite sum, large summable tail, and six explicit error contributions.
The moderate whole-bin difference is taken before any amplitude labels;
the presentation consumer identifies this same sum with its boundary.

No component is defined by subtracting the requested expansion identity,
and the constructor accepts no estimate for a retained component.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP HeckeSkeleton.HighBinActualEuler

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K)))) (omega psi : HeckeCharacter K)
variable (g : PrimeWindowGeometry)
variable {B e : ℝ} (hpsi : psi ∈ HeckePacket K omega)
variable (hB0 : 51 / 100 ≤ B) (hB : B ≤ 1)
variable (hbound : ∀ chi r, r ∈ heckePacketZeros K omega chi →
  1 / 2 ≤ r → r ≤ 1 → r ≤ B)
local notation "E" => arithmeticHighEulerData K Sset P psi
local notation "muS" => (fun p : Sset => mu p.val)

/-- The principal initial complement occurs only in `actualPrincipalTail`;
the second term contains precisely the nonprincipal complements. -/
def actualPhysicalExpansionTail (he : 0 < e) (zeta Z H : ℝ) : ℂ :=
  actualPrincipalTail K S mu P psi g Z H B e +
    actualNonprincipalInitialTailSum K S mu P psi g Z H +
    actualSmallRowHorizontalFaces K S mu P psi g ∅ Z H B e +
    actualLargeHorizontalFaces K S mu P psi g Z H zeta +
    physicalScheduledModerateFaces K S mu P E omega psi hpsi hB0 hB he hbound
      g zeta Z H +
    physicalScheduledWholeBoundary K S mu P E omega psi hpsi hB0 hB he hbound
      g zeta Z H

variable (lam zeta eCap : ℝ)
variable (q : PhysicalRecipeParameters K (S : Set (HeightOneSpectrum (𝓞 K))) P omega psi g
  (arithmeticHighEulerData K (S : Set (HeightOneSpectrum (𝓞 K))) P psi)
  hpsi hB0 hB hbound (fun p : (S : Set (HeightOneSpectrum (𝓞 K))) => mu p.val)
  ∅ lam zeta eCap)

/-- All scales use one fixed detector family and the original values of
every scheduled shifted block, including scales before detection. -/
def actualPhysicalRecipe : RecipeExpansion K Sset psi g zeta :=
  physicalRecipeExpansion K Sset P omega psi g E hpsi hB0 hB q.e_pos hbound muS ∅
    lam zeta q.width q.k q.width_pos
    (fun Z H => actualPrincipalRetained K S mu P psi g Z H B q.e)
    (fun Z H => actualSmallRetained K S mu P psi g Z H B q.e)
    (fun Z H => actualLargeRetained K S mu P psi g Z H zeta)
    (actualPhysicalExpansionTail K S mu P omega psi g hpsi hB0 hB hbound q.e_pos zeta)

/-- Geometry is proved for the chosen actual data, also on empty fibers. -/
theorem actualPhysicalRecipe_geometry :
    (actualPhysicalRecipe K S mu P omega psi g hpsi hB0 hB hbound lam zeta eCap q).MomentGeometry
      22 := by
  exact physicalRecipeExpansion_geometry K Sset P omega psi g E hpsi hB0 hB
    q.e_pos hbound muS ∅ lam zeta q.width q.k q.width_pos _ _ _ _

/-- The eventual source uses these same block values and witnesses; the
only input is the source choice already proved by the actual detector. -/
theorem actualPhysicalRecipe_source_at_power_height (tau : ℝ)
    (htau : 0 < tau) (hceiling : tau ≤ q.ceiling) :
    ∃ Z0 : ℝ, 2 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ b : Fin ((actualPhysicalRecipe K S mu P omega psi g hpsi hB0 hB hbound
        lam zeta eCap q).activeCount Z (Z ^ tau)),
        BlockSource g (((actualPhysicalRecipe K S mu P omega psi g hpsi hB0 hB hbound
          lam zeta eCap q).toHigh (P := P) (R := E.rows) (ω := omega) Z (Z ^ tau)).block b)
          B lam q.k Z := by
  obtain ⟨Z0, hZ0, hsource⟩ := q.source tau htau hceiling
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ b
  exact physicalRecipeSourceAtScale_block K Sset P omega psi g E hpsi hB0 hB
    q.e_pos hbound muS ∅ lam zeta q.width q.k q.width_pos _ _ _ _
    Z (Z ^ tau) (hsource Z hZ) b

end Expansion.Project

#print axioms Expansion.Project.actualPhysicalExpansionTail
#print axioms Expansion.Project.actualPhysicalRecipe
#print axioms Expansion.Project.actualPhysicalRecipe_geometry
#print axioms Expansion.Project.actualPhysicalRecipe_source_at_power_height
