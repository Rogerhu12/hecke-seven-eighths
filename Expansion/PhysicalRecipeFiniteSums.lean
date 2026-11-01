import Expansion.PhysicalRecipeAssembly
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact finite reindexing of the physical recipe

Above the original active guard, the raw active index is the same natural
number as the corresponding scheduled index.  Division and remainder
then identify the flat scheduled index with one shell and one buffered
sector choice.  These are finite sum identities for the original block
values; they introduce no cardinality multiplier or ignored padding.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance physicalFiniteSum_sectorFintype : Fintype (SixthUnitClasses K S) :=
  Fintype.ofFinite _

/-- The quotient/remainder decoder is an exact finite reindexing, also
when the shell type is empty. -/
theorem sum_physicalRecipeSchedule {M : Type*} [AddCommMonoid M]
    (B e zeta Z : ℝ)
    (value : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)) →
      PhysicalRecipeChoice K S B e → M) :
    (∑ b : Fin (shellCount Z (1 / 16) (13 / 16 + zeta) *
        physicalRecipeMultiplicity K S B e),
      value (physicalRecipeShellIndex K S B e zeta Z b)
        (physicalRecipeChoice K S B e zeta Z b)) =
      ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K S B e, value j c := by
  let decode : Fin (shellCount Z (1 / 16) (13 / 16 + zeta) *
      physicalRecipeMultiplicity K S B e) ≃
      Fin (shellCount Z (1 / 16) (13 / 16 + zeta)) × PhysicalRecipeChoice K S B e :=
    finProdFinEquiv.symm.trans
      (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin (PhysicalRecipeChoice K S B e)).symm)
  calc
    _ = ∑ p : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)) ×
        PhysicalRecipeChoice K S B e, value p.1 p.2 := by
      apply Fintype.sum_equiv decode
      intro b
      rfl
    _ = _ := Fintype.sum_prod_type _

/-- The active-index cast preserves the actual raw index value. -/
theorem recipeExpansion_sum_active_values {psi : HeckeCharacter K}
    {g : PrimeWindowGeometry} {zeta : ℝ} (X : RecipeExpansion K S psi g zeta)
    (Z H : ℝ) (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    (∑ b : Fin (X.activeCount Z H), (X.blocks Z H (X.rawBlockIndex Z H b)).value) =
      ∑ b : Fin (X.scheduledCount Z), (X.blocks Z H b).value := by
  have hcount : X.activeCount Z H = X.scheduledCount Z :=
    _root_.ExpansionRecipe.activeBlockCount_eq X.bufferMultiplicity zeta Z H hZ hH
  let castIndex : Fin (X.activeCount Z H) ≃ Fin (X.scheduledCount Z) := finCongr hcount
  have hraw (b : Fin (X.activeCount Z H)) : X.rawBlockIndex Z H b = castIndex b := by
    apply Fin.ext
    rfl
  exact Fintype.sum_equiv castIndex _ _ (fun b => by rw [hraw b])

/-- The same raw-index reindexing for arbitrary values, including whole
fixed-bin contour differences before any amplitude label is introduced. -/
theorem recipeExpansion_sum_active_map {M : Type*} [AddCommMonoid M]
    {psi : HeckeCharacter K} {g : PrimeWindowGeometry} {zeta : ℝ}
    (X : RecipeExpansion K S psi g zeta) (Z H : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H)
    (value : Fin (X.scheduledCount Z) → M) :
    (∑ b : Fin (X.activeCount Z H), value (X.rawBlockIndex Z H b)) =
      ∑ b : Fin (X.scheduledCount Z), value b := by
  have hcount : X.activeCount Z H = X.scheduledCount Z :=
    _root_.ExpansionRecipe.activeBlockCount_eq X.bufferMultiplicity zeta Z H hZ hH
  let castIndex : Fin (X.activeCount Z H) ≃ Fin (X.scheduledCount Z) := finCongr hcount
  have hraw (b : Fin (X.activeCount Z H)) : X.rawBlockIndex Z H b = castIndex b := by
    apply Fin.ext
    rfl
  exact Fintype.sum_equiv castIndex _ _ (fun b => by rw [hraw b])

variable (P : ProbeData K S) (omega psi : HeckeCharacter K) (g : PrimeWindowGeometry)
variable (E : RowEulerData K S P)
variable {B e : ℝ} (hpsi : psi ∈ HeckePacket K omega)
variable (hB0 : 51 / 100 ≤ B) (hB1 : B ≤ 1) (he : 0 < e)
variable (hboundary : ∀ chi : HeckePacketIndex K omega,
  ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (mu : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (mu p).IsAddHaarMeasure]
variable (windowCharacters : Finset (HeckeCharacter K))
variable (lam zeta width k : ℝ) (hw : 0 < width)
variable (principal small large tail : ℝ → ℝ → ℂ)
local notation "X" => physicalRecipeExpansion K S P omega psi g E hpsi hB0 hB1 he hboundary
  mu windowCharacters lam zeta width k hw principal small large tail

/-- Arbitrary whole-bin values use the same active-to-shell reindexing. -/
theorem physicalRecipeExpansion_sum_active_schedule {M : Type*} [AddCommMonoid M]
    (Z H : ℝ) (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H)
    (value : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)) →
      PhysicalRecipeChoice K S B e → M) :
    (∑ b : Fin ((X).activeCount Z H),
      value (physicalRecipeShellIndex K S B e zeta Z ((X).rawBlockIndex Z H b))
        (physicalRecipeChoice K S B e zeta Z ((X).rawBlockIndex Z H b))) =
      ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K S B e, value j c := by
  calc
    _ = ∑ b : Fin ((X).scheduledCount Z),
        value (physicalRecipeShellIndex K S B e zeta Z b)
          (physicalRecipeChoice K S B e zeta Z b) :=
      recipeExpansion_sum_active_map K S (X) Z H hZ hH _
    _ = _ := sum_physicalRecipeSchedule K S B e zeta Z value

/-- The public high expansion sums precisely the original double
schedule of actual contour block values once its original guard holds. -/
theorem physicalRecipeExpansion_toHigh_block_sum (Z H : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hH : 1 ≤ H) :
    (∑ b, (((X).toHigh (P := P) (R := E.rows) (ω := omega) Z H).block b).value) =
      ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
        ∑ c : PhysicalRecipeChoice K S B e,
          physicalRecipeBlockValue K S P E omega psi hpsi hB0 hB1 he hboundary
            mu g windowCharacters zeta Z H j c := by
  change (∑ b : Fin ((X).activeCount Z H),
    ((X).blocks Z H ((X).rawBlockIndex Z H b)).value) = _
  calc
    _ = ∑ b : Fin ((X).scheduledCount Z), ((X).blocks Z H b).value :=
      recipeExpansion_sum_active_values K S (X) Z H hZ hH
    _ = ∑ b : Fin (shellCount Z (1 / 16) (13 / 16 + zeta) *
        physicalRecipeMultiplicity K S B e),
        physicalRecipeBlockValue K S P E omega psi hpsi hB0 hB1 he hboundary
          mu g windowCharacters zeta Z H
          (physicalRecipeShellIndex K S B e zeta Z b)
          (physicalRecipeChoice K S B e zeta Z b) := by
      apply Finset.sum_congr rfl
      intro b _
      exact physicalRecipeExpansion_block_value K S P omega psi g E hpsi hB0 hB1 he hboundary
        mu windowCharacters lam zeta width k hw principal small large tail Z H b
    _ = _ := sum_physicalRecipeSchedule K S B e zeta Z _

end Expansion.Project

#print axioms Expansion.Project.sum_physicalRecipeSchedule
#print axioms Expansion.Project.recipeExpansion_sum_active_values
#print axioms Expansion.Project.recipeExpansion_sum_active_map
#print axioms Expansion.Project.physicalRecipeExpansion_sum_active_schedule
#print axioms Expansion.Project.physicalRecipeExpansion_toHigh_block_sum
