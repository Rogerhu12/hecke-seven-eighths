import DedekindZetaZeroFree.Theta.Periods.ArchimedeanTensorProduct
import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.GlobalProduct

/-!
# Full archimedean matrix products for arbitrary actual pure tensors

The upstream `fullMatrix_product` is exposed only for the selected digit
source.  Its more primitive completed-period machinery already works for
every pure tensor in the actual canonical residue map.  This adapter makes
that stronger statement directly usable after replacing the archimedean
vectors by high K-types.

No matrix-coefficient factorization is assumed.  The one-dimensional local
Whittaker comparison and the completed local projective action give the
product.  Nonvanishing is needed only at the original vector's value at one
to define normalized ratios.  The value of that same vector at the finite
background is retained explicitly, including its normalization scalar.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.FiniteArchProduct

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.FourierContinuation
open DedekindZetaZeroFree.FourierContinuation.LiteralSource
open DedekindZetaZeroFree.FourierContinuation.ComplexLines
open DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open DedekindZetaZeroFree.KPGlobalTorusFiniteStages
open DedekindZetaZeroFree.KPLiteralScalarHCCompactOrbit
open DedekindZetaZeroFree.KPCplxCharacterHaar
open DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
variable (N : TraceHaarTransport R)

local notation "H" => actualImageData R P C μ hμ
local notation "E" => bad R.A P C

/-- A local ratio of the same arbitrary pure tensor's actual Fourier
period.  It is determined by that tensor's archimedean vector, regardless
of which finite background is later inserted. -/
def archRatio (s : RestrictedTensorSimple.Level E)
    (x : ∀ j : s.val, actualLocal R H j.val)
    (w : InfinitePlace F) (a : ComplexPGL2) : ℂ :=
  actualStagePeriod R P C μ hμ N s x (projectiveSlot R w a) /
    actualStagePeriod R P C μ hμ N s x 1

/-- Arbitrary high K-type pure tensors, with their actual scalar at one
preserved: no selected-Gaussian hypothesis is present. -/
theorem full_arch_product
    (s : RestrictedTensorSimple.Level E)
    (x : ∀ j : s.val, actualLocal R H j.val)
    (hw : ∀ w : InfinitePlace F, Sum.inl w ∈ s.val)
    (hx : actualStagePeriod R P C μ hμ N s x 1 ≠ 0)
    (a : InfinitePlace F → ComplexPGL2) (g : Group R)
    (hg : ∀ w, PGLComplex.AdelicSlicesRaw.archProjection F
      R.A.zeta12 R.A.primitive_zeta12 g w = 1) :
    actualStagePeriod R P C μ hμ N s x
        (g * KPSmoothActualFlowData.archimedeanInsertion F
          R.A.zeta12 R.A.primitive_zeta12 a) =
      actualStagePeriod R P C μ hμ N s x g *
        ∏ w, archRatio R P C μ hμ N s x w (a w) := by
  choose M hM hMx using fun w =>
    actualStage_detector R P C μ hμ N s x hx w (hw w)
  have hr (w : InfinitePlace F) :
      archRatio R P C μ hμ N s x w (a w) =
        M w (KPCplxActualImage.imageAction traceFrequency (a w)
          (harmonicInclusion (x ⟨Sum.inl w, hw w⟩))) /
        M w (harmonicInclusion (x ⟨Sum.inl w, hw w⟩)) := by
    have h := actualStage_period_ratio R P C μ hμ N s x w (hw w) 1
      (by simp) (M w) (hM w) (hMx w) (a w)
    simp only [one_mul] at h
    rw [archRatio, h, mul_div_cancel_right₀ _ hx]
  rw [show (∏ w, archRatio R P C μ hμ N s x w (a w)) =
      ∏ w, M w (KPCplxActualImage.imageAction traceFrequency (a w)
        (harmonicInclusion (x ⟨Sum.inl w, hw w⟩))) /
        M w (harmonicInclusion (x ⟨Sum.inl w, hw w⟩)) from
      Finset.prod_congr rfl (fun w _ => hr w)]
  simpa only [archPartial_univ, mul_comm] using
    actualStage_arch_product R P C μ hμ N s x hw M hM hMx a Finset.univ g hg

/-- The actual finite matrix insertion has trivial projection at every
archimedean place; this is a group identity, independent of the vector. -/
theorem finiteBase_arch_projection
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (w : InfinitePlace F) :
    PGLComplex.AdelicSlicesRaw.archProjection F R.A.zeta12 R.A.primitive_zeta12
      (finiteBase (R := R) a).val w = 1 := by
  rw [finiteBase_val]
  exact raw_arch_projection_one R (finiteTuple (R := R) a) w
    (finiteTuple_off a (Sum.inl w) (fun _ => Sum.inl_ne_inr))

/-- The selected-source restriction in upstream `fullMatrix_product` is
removed for canonical actual tensors.  Local finite matrices are arbitrary,
and the complex matrices may be diagonal-Weyl matrices for the reflected
Mellin calculation. -/
theorem full_matrix_product
    (s : RestrictedTensorSimple.Level E)
    (x : ∀ j : s.val, actualLocal R H j.val)
    (hw : ∀ w : InfinitePlace F, Sum.inl w ∈ s.val)
    (hx : actualStagePeriod R P C μ hμ N s x 1 ≠ 0)
    (a : ∀ q : KPFinitePlace F,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (b : InfinitePlace F → ComplexGL2) :
    actualStagePeriod R P C μ hμ N s x
        ((finiteBase (R := R) a).val *
          archMatrixInsertion F R.A.zeta12 R.A.primitive_zeta12 b) =
      actualStagePeriod R P C μ hμ N s x (finiteBase (R := R) a).val *
        ∏ w, archRatio R P C μ hμ N s x w (Matrix.ProjGenLinGroup.mk (b w)) := by
  rw [SheetRescaling.literal_archMatrixInsertion]
  exact full_arch_product R P C μ hμ N s x hw hx
    (fun w => Matrix.ProjGenLinGroup.mk (b w)) (finiteBase (R := R) a).val
    (finiteBase_arch_projection R a)

end ThetaGlobal.FiniteArchProduct

#print axioms ThetaGlobal.FiniteArchProduct.full_arch_product
#print axioms ThetaGlobal.FiniteArchProduct.full_matrix_product
