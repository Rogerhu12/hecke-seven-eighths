import DedekindZetaZeroFree.Theta.Digits.Exterior.AdditiveFrequencies

/-!
# Actual nonzero exterior digits for the fixed finite source

This is the local Bruhat calculation already proved in
`DedekindZetaZeroFree.Theta.Digits.Exterior`. Its source parameter is
restricted here to `JointExteriorCoefficientSources`: the proof uses the
actual representation and Whittaker functional, the compact-invariant
reference, its rational spherical values, and root alignment. It does
not require a packet, either global orbit identity, Mellin data, global
absolute convergence, or upper-unipotent vanishing.

The concluding formula evaluates the literal local matrix coefficient.
A separate integration module identifies this expression with the
coefficient used by the global marked finite average.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

namespace ThetaGlobal.LocalDigitEvaluation

open DedekindZetaZeroFree
open MomentSources NumberField IsDedekindDomain ThetaExpansion ValuativeRel
open DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointExteriorCoefficientSources R N)

/-- The actual reference coefficient at the literal local digit word. -/
def localDigitValue (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) (s : 𝓞 F) : ℂ :=
  C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
      KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
      KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (-algebraMap (𝓞 F) (p.val.adicCompletion F) s /
          algebraMap F (p.val.adicCompletion F)
            (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)))
    (C.factorization.references (Sum.inr p.val)))

/-- Compact lower-root translations fix the actual exterior reference. -/
theorem lower_fixed (p : ThetaBranch.ExteriorPrime R.A) (o : KPTameCompact.O F p.val) :
    exteriorImageAction R C.toJointHaarFactorizedSources p
      (KPPGLLocalCover.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) o.val)
      (C.factorization.references (Sum.inr p.val)) = C.factorization.references (Sum.inr p.val) :=
  (C.factorization.spherical_reference p.val p.property).2 _ (lower_compact R p o)

theorem bruhat_value (p : ThetaBranch.ExteriorPrime R.A)
    (y H : (p.val.adicCompletion F)ˣ)
    (hH : ((H⁻¹ : (p.val.adicCompletion F)ˣ) : p.val.adicCompletion F) ∈ KPTameCompact.O F p.val) :
    C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y *
       KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) H.val)
      (C.factorization.references (Sum.inr p.val))) =
    (ResidueTrace.localTraceCharacter p.val (y.val * (H⁻¹).val) : ℂ) *
      KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y (-(H⁻¹ ^ 2)) *
      exteriorWhittakerValue R C.toJointHaarFactorizedSources p (y * (-(H⁻¹ ^ 2))) := by
  let A := KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
  let NN := KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
  have hn : A y * NN (H⁻¹).val = NN (y.val * (H⁻¹).val) * A y := by
    dsimp [A, NN]
    rw [KPCorrectedBruhatLifts.quotient_upper_diagonal]
    rw [mul_div_cancel_left₀ _ y.ne_zero]
  have hword : A y * KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) * NN H.val =
      NN (y.val * (H⁻¹).val) * (A y * A (-(H⁻¹ ^ 2))) *
        KPPGLLocalCover.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (H⁻¹).val := by
    rw [mul_assoc, KPCorrectedBruhatLifts.quotient_weyl_upper]
    rw [← mul_assoc, ← mul_assoc, hn]
    simp only [mul_assoc]
    rfl
  have hh := representation_bruhat (exteriorImageAction R C.toJointHaarFactorizedSources p)
    (C.factorization.ell (Sum.inr p.val)) (C.factorization.references (Sum.inr p.val))
    (A y) (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) (NN H.val)
    (NN (y.val * (H⁻¹).val)) (A (-(H⁻¹ ^ 2)))
    (KPPGLLocalCover.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) (H⁻¹).val)
    (KPPGLLocalCover.centralInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
      (KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y (-(H⁻¹ ^ 2)) ^ 2))
    (A (y * (-(H⁻¹ ^ 2))))
    (ResidueTrace.localTraceCharacter p.val (y.val * (H⁻¹).val) : ℂ)
    (KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y (-(H⁻¹ ^ 2)))
    hword (lower_fixed R C p ⟨_, hH⟩)
    (exterior_whittaker_equivariance R C.toJointHaarFactorizedSources p (y.val * (H⁻¹).val))
    (KPPGLLocalCover.A_mul F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y (-(H⁻¹ ^ 2)))
    (KPRankOneShellRepair.actualCanonicalImage_ordinary_genuine F R.A.zeta12
      R.A.primitive_zeta12 p.val (C.factorization.finiteData p.val).inducing
      (C.factorization.finiteData p.val).inducing.polarization
      (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer _)
  rw [hh]
  unfold exteriorWhittakerValue
  rw [exterior_diagonal_eq_standard_lift]

theorem rational_word_value (p : ThetaBranch.ExteriorPrime R.A) (x H : Fˣ)
    (hH : ThetaBranch.order p.val H < 0) :
    C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
       KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (algebraMap F (p.val.adicCompletion F) H.val))
      (C.factorization.references (Sum.inr p.val))) =
    (ResidueTrace.localTraceCharacter p.val (algebraMap F (p.val.adicCompletion F) (x.val * H.val⁻¹)) : ℂ) *
      KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
        (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x)
        (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom (-(H⁻¹ ^ 2))) *
      ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p (x * (-(H⁻¹ ^ 2))) := by
  let M := Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom
  have hi : ((M H)⁻¹).val ∈ KPTameCompact.O F p.val := by
    rw [← map_inv]
    exact integral_of_order_nonneg p.val H⁻¹ (by rw [order_inv]; omega)
  have hb := bruhat_value R C p (M x) (M H) hi
  have he : -( (M H)⁻¹ ^ 2) = M (-(H⁻¹ ^ 2)) := by
    apply Units.ext
    simp [M]
  rw [he, ← map_mul] at hb
  have hw : exteriorWhittakerValue R C.toJointHaarFactorizedSources p (M (x * -(H⁻¹ ^ 2))) =
      ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p (x * -(H⁻¹ ^ 2)) :=
    C.exterior.rational_exact p _
  rw [hw] at hb
  have hp : (M x).val * ((M H)⁻¹).val =
      algebraMap F (p.val.adicCompletion F) (x.val * H.val⁻¹) := by
    simp [M]
  rw [hp] at hb
  exact hb

theorem nonzero_value (p : ThetaBranch.ExteriorPrime R.A) (x V : Fˣ)
    (hV : ThetaBranch.order p.val V = 0) :
    C.factorization.ell (Sum.inr p.val) (exteriorImageAction R C.toJointHaarFactorizedSources p
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) *
       KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) *
       KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
          (-algebraMap F (p.val.adicCompletion F) V.val /
            algebraMap F (p.val.adicCompletion F)
              (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)))
      (C.factorization.references (Sum.inr p.val))) =
    sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p)
      (ThetaBranch.order p.val x + 2) *
      ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p x) ^
        (4 + 2 * (ThetaBranch.order p.val x + 2)) *
      ThetaBranch.symbol R.A R.σ p V ^ (4 : ℕ) *
      (if ThetaBranch.order p.val x + 2 = 0 then
        Characters.psi R p
          (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x) /
            ThetaBranch.unitResidue p.val V) else 1) := by
  let g := R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)
  let H := -V / g
  have hc := digit_coordinates R p x V hV
  dsimp only at hc
  have hword := rational_word_value R C p x H (by rw [hc.1]; norm_num)
  have he : algebraMap F (p.val.adicCompletion F) H.val =
      -algebraMap F (p.val.adicCompletion F) V.val / algebraMap F (p.val.adicCompletion F) g.val := by
    simp [H]
  rw [he] at hword
  rw [hword, mul_assoc, nonzero_spherical R C.aligned p x V hV]
  by_cases hneg : ThetaBranch.order p.val x + 2 < 0
  · simp [sexticSphericalCoefficient, hneg]
  · rw [additive_digit R p x V hV (by omega)]
    ring

theorem nonzero_localDigit (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) (s : 𝓞 F)
    (hs : Ideal.Quotient.mk p.val.asIdeal s ≠ 0) :
    localDigitValue R C p x s =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p) (Characters.psi R p)
        (ThetaBranch.order p.val x + 2) *
      ThetaBranch.symbol R.A R.σ p (ThetaBranch.localUnit R.A R.probe.allowed p x) ^
        (4 + 2 * (ThetaBranch.order p.val x + 2)) *
      ThetaBranch.residueCharacter R.A R.σ p (Ideal.Quotient.mk p.val.asIdeal s) ^ (4 : ℕ) *
      (if ThetaBranch.order p.val x + 2 = 0 then
        Characters.psi R p
          (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x) /
            Ideal.Quotient.mk p.val.asIdeal s) else 1) := by
  have hm : s ∉ p.val.asIdeal := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hsn : (s : F) ≠ 0 := by
    exact_mod_cast (fun h => hm (h ▸ p.val.asIdeal.zero_mem) : s ≠ 0)
  let V := Units.mk0 (s : F) hsn
  have hv : ThetaBranch.order p.val V = 0 := by
    simp [ThetaBranch.order, V, p.val.valuation_eq_one_iff_notMem.mpr hm]
  have hr := reduction_integral p.val s hm
  have hh := nonzero_value R C p x V hv
  unfold ThetaBranch.symbol at hh
  rw [hr] at hh
  exact hh

end ThetaGlobal.LocalDigitEvaluation

#print axioms ThetaGlobal.LocalDigitEvaluation.bruhat_value
#print axioms ThetaGlobal.LocalDigitEvaluation.rational_word_value
#print axioms ThetaGlobal.LocalDigitEvaluation.nonzero_value
#print axioms ThetaGlobal.LocalDigitEvaluation.nonzero_localDigit
