import HeckeAxiom.GaussDictionary
import HeckeAxiom.SignalAdapter
import HeckeGeneral.Characters.PrimeCoefficients
import HeckeGeneral.Analysis.HeckeSeries
import DedekindZetaZeroFree.Adeles.Characters.RayCharacterCorrectionFactors
import DedekindZetaZeroFree.CharacterSums.Gauss.FiniteSupportReciprocityCancellation

/-!
# The cube and mixed Gauss calibrations

For the data of an arithmetic choice and every squarefree exterior ideal `I`,

* `thetaGamma I 2 ^ 3 = μ(I) · Λ(I)`;
* `conj Λ(I) · thetaGamma I 2 · thetaGamma I 1 = μ(I) · G(I)`,

the `cube_calibration` and `mixed_calibration` fields of the skeleton's
`ThetaCalibrationInput` (AR-CUBE-CALIBRATION, AR-MIXED-CALIBRATION).

At a prime these are the context's `gammaTwo_cube` and `gammaOne_gammaTwo`,
evaluated at the idele of a local uniformizer, which represents the prime; its
class is the uniformizer's local component, so the context's values of `Λ` and
`G` are the skeleton's prime coefficients. A coprime product multiplies the
Gauss sums up to the phases `σ(I, b)ʲ σ(J, a)ʲ` of the Chinese remainder
theorem. Sextic reciprocity for the allowed generators makes the two phases
equal, and the calibrations only see their sixth power.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open scoped ComplexConjugate

variable {F : Type} [Field F] [NumberField F]

/-- The local uniformizer at `v`, as an idele. -/
def uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) : NumberField.IdeleGroup (𝓞 F) F :=
  NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v (localUniformizerUnit F v)

theorem uniformizerIdele_infinite (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) :
    (uniformizerIdele v).val.1 w = 1 :=
  rfl

theorem uniformizerIdele_finite_self (v : HeightOneSpectrum (𝓞 F)) :
    (uniformizerIdele v).val.2 v = localUniformizer F v := by
  classical
  exact RestrictedProduct.mulSingle_eq_same _ _ _

theorem uniformizerIdele_finite_of_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) :
    (uniformizerIdele v).val.2 w = 1 := by
  classical
  exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

theorem idealPrimeExponent_self (v : HeightOneSpectrum (𝓞 F)) :
    idealPrimeExponent v.asIdeal v.asIdeal = 1 := by
  unfold idealPrimeExponent
  rw [normalizedFactors_irreducible v.irreducible, normalize_eq, Multiset.count_singleton_self]

theorem idealPrimeExponent_of_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) :
    idealPrimeExponent w.asIdeal v.asIdeal = 0 := by
  unfold idealPrimeExponent
  rw [normalizedFactors_irreducible v.irreducible, normalize_eq]
  exact Multiset.count_eq_zero.mpr fun hm => h (HeightOneSpectrum.ext (Multiset.mem_singleton.mp hm))

/-- The uniformizer idele represents the prime. -/
theorem represents_uniformizerIdele (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    A.RepresentsExteriorIdeal (primeExterior A v hv) (uniformizerIdele v) := by
  refine ⟨uniformizerIdele_infinite v, fun w hw => ?_, fun w _ => ?_⟩
  · exact uniformizerIdele_finite_of_ne v w (fun h => hv (h ▸ hw))
  · rw [primeExterior_val]
    by_cases h : w = v
    · subst h
      rw [uniformizerIdele_finite_self, localUniformizer_valuation, idealPrimeExponent_self]
      rfl
    · rw [uniformizerIdele_finite_of_ne v w h, idealPrimeExponent_of_ne v w h, map_one]
      rfl

/-- On the uniformizer idele, a continuous character unramified at `v` takes
the skeleton's prime coefficient. -/
theorem toHeckeCharacter_uniformizerIdele (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle) (hΦ : Continuous Φ) (v : HeightOneSpectrum (𝓞 F))
    (hunr : UnramifiedAt F (toHeckeCharacter A Φ hΦ) v) :
    (Φ (QuotientGroup.mk (uniformizerIdele v)) : ℂ) =
      primeCoefficient F (toHeckeCharacter A Φ hΦ) v := by
  rw [primeCoefficient_of_unramified F _ v hunr, localComponent_apply]
  rfl

theorem conj_mul_self_circle (z : Circle) : conj (z : ℂ) * (z : ℂ) = 1 := by
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]

/-- A nonzero ideal containing an exterior ideal is exterior. -/
def exteriorOfLe (A : SArithmeticData F) (I : A.Exterior) (x : Ideal (𝓞 F)) (hx : x ≠ ⊥)
    (hle : I.val ≤ x) : A.Exterior :=
  ⟨x, hx, top_unique (I.property.2 ▸ sup_le_sup_right hle A.cS)⟩

theorem sup_eq_top_of_isRelPrime {x y : Ideal (𝓞 F)} (h : IsRelPrime x y) : x ⊔ y = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  exact hM.ne_top (Ideal.isUnit_iff.mp (h (Ideal.dvd_iff_le.mpr (le_sup_left.trans hle))
    (Ideal.dvd_iff_le.mpr (le_sup_right.trans hle))))

namespace ArithmeticChoice

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {root12 : F} {τ : F →+* ℂ}
variable (X : ArithmeticChoice F S₀ root12 τ)

/-- The recipe generator of an Axiom exterior ideal. -/
def gen (I : X.A.Exterior) : X.A.R :=
  Classical.choose ((recipeOfContext X.A X.C).generates I)

theorem gen_spec (I : X.A.Exterior) :
    X.A.Generates I (X.gen I) ∧
      (((recipeOfContext X.A X.C).generator I : Fˣ) : F) = (X.gen I : F) :=
  Classical.choose_spec ((recipeOfContext X.A X.C).generates I)

theorem gen_allowed (I : X.A.Exterior) :
    X.A.IsAllowed X.C.correction.B ((recipeOfContext X.A X.C).generator I) :=
  (recipeOfContext X.A X.C).allowed I

/-- Axiom's ideal Gauss sum with the recipe generator. -/
def Γ (I : X.A.Exterior) (j : ℤ) : ℂ :=
  X.A.idealGauss τ X.hS I (X.gen I) (X.gen_spec I).1 j

theorem gauss_eq_Γ (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) (j : ℤ) :
    X.gauss J j = X.Γ (X.axiomIdeal J) j :=
  rfl

/-- The cube calibration at a prime. -/
theorem Γ_prime_cube (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (X.places : Set (HeightOneSpectrum (𝓞 F)))) :
    X.Γ (primeExterior X.A v hv) 2 ^ 3 = -primeCoefficient F X.Lambda v := by
  have hcube := X.C.correction.gammaTwo_cube (primeExterior X.A v hv) v rfl (X.gen _)
    (X.gen_spec _).1 _ (X.gen_allowed _) (X.gen_spec _).2
  have hΛ := X.C.correction.Λ_ideal (primeExterior X.A v hv) (uniformizerIdele v)
    (represents_uniformizerIdele X.A v hv)
  rw [Γ, hcube, ← hΛ]
  rw [toHeckeCharacter_uniformizerIdele X.A _ _ v (X.Lambda_unramified v hv)]
  rfl

/-- The mixed product at a prime. -/
theorem Γ_prime_mixed (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (X.places : Set (HeightOneSpectrum (𝓞 F)))) :
    X.Γ (primeExterior X.A v hv) 1 * X.Γ (primeExterior X.A v hv) 2 =
      -primeCoefficient F X.Lambda v * primeCoefficient F X.G v := by
  have hrep := represents_uniformizerIdele X.A v hv
  have hmix := X.C.correction.gammaOne_gammaTwo (primeExterior X.A v hv) v rfl (X.gen _)
    (X.gen_spec _).1 _ (X.gen_allowed _) (X.gen_spec _).2 (uniformizerIdele v) hrep
  have hΛ := X.C.correction.Λ_ideal (primeExterior X.A v hv) (uniformizerIdele v) hrep
  rw [Γ, Γ, hmix, ← hΛ, toHeckeCharacter_uniformizerIdele X.A _ _ v (X.Lambda_unramified v hv),
    toHeckeCharacter_uniformizerIdele X.A _ _ v (X.G_unramified v hv)]
  rfl

/-- Both calibrations of an Axiom exterior ideal, with ideal coefficients. -/
def Calibrated (I : X.A.Exterior) : Prop :=
  X.Γ I 2 ^ 3 = (moebius I.val : ℂ) * idealCoefficient (primeCoefficient F X.Lambda) I.val ∧
    conj (idealCoefficient (primeCoefficient F X.Lambda) I.val) * X.Γ I 2 * X.Γ I 1 =
      (moebius I.val : ℂ) * idealCoefficient (primeCoefficient F X.G) I.val

theorem calibrated_top (I : X.A.Exterior) (hI : I.val = ⊤) : X.Calibrated I := by
  have hΓ (j : ℤ) : X.Γ I j = 1 := X.A.idealGauss_top τ X.hS I hI _ _ j
  have hμ : moebius I.val = 1 := (Ideal.isUnit_iff.mpr hI).moebius_eq
  have hc (a : HeightOneSpectrum (𝓞 F) → ℂ) : idealCoefficient a I.val = 1 := by
    rw [hI, ← Ideal.one_eq_top, idealCoefficient_one]
  refine ⟨?_, ?_⟩ <;> simp only [hΓ, hμ, hc, map_one, Int.cast_one] <;> ring

theorem calibrated_prime (I : X.A.Exterior) (p : Ideal (𝓞 F)) (hp : Prime p) (hI : I.val = p) :
    X.Calibrated I := by
  have hp0 : p ≠ ⊥ := hI ▸ I.property.1
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
  have hv : v ∉ (X.places : Set (HeightOneSpectrum (𝓞 F))) :=
    (sup_cS_eq_top_iff X.A I.val I.property.1).mp I.property.2 v (by rw [hI])
  obtain rfl : I = primeExterior X.A v hv := Subtype.ext hI
  have hμ : moebius (primeExterior X.A v hv).val = -1 := hp.irreducible.moebius_eq
  have hc (a : HeightOneSpectrum (𝓞 F) → ℂ) :
      idealCoefficient a (primeExterior X.A v hv).val = a v := idealCoefficient_prime a v
  have hcube := X.Γ_prime_cube v hv
  have hmix := X.Γ_prime_mixed v hv
  have hunit : conj (primeCoefficient F X.Lambda v) * primeCoefficient F X.Lambda v = 1 := by
    rw [primeCoefficient_of_unramified F _ v (X.Lambda_unramified v hv)]
    exact conj_mul_self_circle _
  refine ⟨?_, ?_⟩
  · rw [hcube, hμ, hc]
    push_cast
    ring
  · rw [hμ, hc, hc]
    linear_combination (conj (primeCoefficient F X.Lambda v)) * hmix -
      primeCoefficient F X.G v * hunit

/-- Coprime products of calibrated ideals are calibrated. -/
theorem calibrated_mul (I Ix Iy : X.A.Exterior) (hK : I.val = Ix.val * Iy.val)
    (hxy : IsRelPrime Ix.val Iy.val) (hsqx : Squarefree Ix.val) (hsqy : Squarefree Iy.val)
    (hx : X.Calibrated Ix) (hy : X.Calibrated Iy) : X.Calibrated I := by
  have hcop : Ix.val ⊔ Iy.val = ⊤ := sup_eq_top_of_isRelPrime hxy
  set a := X.gen Ix
  set b := X.gen Iy
  have ha := (X.gen_spec Ix).1
  have hb := (X.gen_spec Iy).1
  have hab : X.A.Generates I (a * b) := by
    refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
    rw [← Ideal.span_singleton_mul_span_singleton, ha.2, hb.2]
    simp only [SArithmeticData.extendIdeal, hK, Ideal.map_mul]
  have hcrt (j : ℤ) := X.A.idealGauss_squarefree_crt τ X.hS Ix Iy I hsqx hsqy hcop hK a b ha hb
    hab j
  have hallowed : X.A.IsAllowed X.C.correction.B
      ((recipeOfContext X.A X.C).generator Ix * (recipeOfContext X.A X.C).generator Iy) := by
    unfold IsAllowed
    rw [map_mul]
    exact X.C.correction.B.mul_mem (X.gen_allowed Ix) (X.gen_allowed Iy)
  have hgen (j : ℤ) : X.Γ I j = X.A.idealGauss τ X.hS I (a * b) hab j :=
    X.A.idealGauss_allowed_generator_independent τ X.hS X.C.classGroup_trivial
      X.C.correction.H X.C.correction.B X.C.correction.B_complement I (a * b) (X.gen I) hab
      (X.gen_spec I).1 _ _ (by push_cast; rw [(X.gen_spec Ix).2, (X.gen_spec Iy).2])
      (X.gen_spec I).2 hallowed (X.gen_allowed I) j
  have hrec : X.A.sexticResidue Ix b = X.A.sexticResidue Iy a :=
    X.C.reciprocity.1 Ix Iy a b _ _ ha hb (X.gen_spec Ix).2 (X.gen_spec Iy).2
      (X.gen_allowed Ix) (X.gen_allowed Iy) hcop
  have hcopR : IsCoprime a b := by
    apply (Ideal.sup_eq_top_iff_isCoprime a b).mp
    rw [ha.2, hb.2]
    change Ideal.map (algebraMap (𝓞 F) X.A.R) Ix.val ⊔
      Ideal.map (algebraMap (𝓞 F) X.A.R) Iy.val = ⊤
    rw [← Ideal.map_sup, hcop, Ideal.map_top]
  have hbu : IsUnit (Ideal.Quotient.mk (X.A.extendIdeal Ix) b) := by
    obtain ⟨r, s, hrs⟩ := hcopR
    have haz : Ideal.Quotient.mk (X.A.extendIdeal Ix) a = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← ha.2]
      exact Ideal.subset_span (Set.mem_singleton a)
    apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (X.A.extendIdeal Ix) s)
    have hh := congrArg (Ideal.Quotient.mk (X.A.extendIdeal Ix)) hrs
    simpa only [map_add, map_mul, map_one, haz, zero_mul, zero_add, mul_comm] using hh
  have h6 : τ (X.A.sexticResidue Ix b) ^ 6 = 1 :=
    (GlobalPairCancel.frequencyTheta_unit X.A τ Ix b hbu).2
  have hμ : (moebius I.val : ℂ) = (moebius Ix.val : ℂ) * (moebius Iy.val : ℂ) := by
    rw [hK, hxy.moebius_mul, Int.cast_mul]
  have hc (c : HeightOneSpectrum (𝓞 F) → ℂ) :
      idealCoefficient c I.val = idealCoefficient c Ix.val * idealCoefficient c Iy.val := by
    rw [hK, idealCoefficient_mul]
  have h2 : X.Γ I 2 = τ (X.A.sexticResidue Ix b) ^ 2 * τ (X.A.sexticResidue Ix b) ^ 2 *
      X.Γ Ix 2 * X.Γ Iy 2 := by
    rw [hgen, hcrt, ← hrec]
    rfl
  have h1 : X.Γ I 1 = τ (X.A.sexticResidue Ix b) * τ (X.A.sexticResidue Ix b) *
      X.Γ Ix 1 * X.Γ Iy 1 := by
    rw [hgen, hcrt, ← hrec]
    simp only [show sexticExponent (1 : ℤ) = 1 from rfl, pow_one]
    rfl
  obtain ⟨hx3, hxm⟩ := hx
  obtain ⟨hy3, hym⟩ := hy
  set ζ := τ (X.A.sexticResidue Ix b)
  refine ⟨?_, ?_⟩
  · rw [h2, hμ, hc]
    linear_combination (ζ ^ 12 * X.Γ Iy 2 ^ 3) * hx3 +
      (ζ ^ 12 * (moebius Ix.val : ℂ) * idealCoefficient (primeCoefficient F X.Lambda) Ix.val) * hy3 +
      ((moebius Ix.val : ℂ) * idealCoefficient (primeCoefficient F X.Lambda) Ix.val *
        (moebius Iy.val : ℂ) * idealCoefficient (primeCoefficient F X.Lambda) Iy.val * (ζ ^ 6 + 1)) * h6
  · rw [h2, h1, hμ, hc, hc, map_mul]
    linear_combination (ζ ^ 6 * conj (idealCoefficient (primeCoefficient F X.Lambda) Iy.val) *
        X.Γ Iy 2 * X.Γ Iy 1) * hxm +
      (ζ ^ 6 * (moebius Ix.val : ℂ) * idealCoefficient (primeCoefficient F X.G) Ix.val) * hym +
      ((moebius Ix.val : ℂ) * idealCoefficient (primeCoefficient F X.G) Ix.val *
        (moebius Iy.val : ℂ) * idealCoefficient (primeCoefficient F X.G) Iy.val) * h6

/-- Every squarefree Axiom exterior ideal is calibrated. -/
theorem calibrated_of_squarefree (I : X.A.Exterior) (hI : Squarefree I.val) : X.Calibrated I := by
  suffices h : ∀ a : Ideal (𝓞 F), ∀ I : X.A.Exterior, I.val = a → Squarefree a → X.Calibrated I from
    h _ I rfl hI
  intro a
  induction a using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact fun I hI _ => absurd hI I.property.1
  | h1 hu => exact fun I hI _ => X.calibrated_top I (hI.trans (Ideal.isUnit_iff.mp hu))
  | hpr i hp =>
    intro I hI hsq
    rcases hsq.eq_zero_or_one_of_pow_of_not_isUnit hp.not_isUnit with h | h
    · subst h
      exact X.calibrated_top I (by rw [hI, pow_zero, Ideal.one_eq_top])
    · subst h
      exact X.calibrated_prime I _ hp (by rw [hI, pow_one])
  | hcp hxy hx hy =>
    rename_i x y
    intro I hI hsq
    have hx0 : x ≠ ⊥ := fun h => I.property.1 (by rw [hI, h, Ideal.bot_mul])
    have hy0 : y ≠ ⊥ := fun h => I.property.1 (by rw [hI, h, Ideal.mul_bot])
    let Ix := exteriorOfLe X.A I x hx0 (by rw [hI]; exact Ideal.mul_le_left)
    let Iy := exteriorOfLe X.A I y hy0 (by rw [hI]; exact Ideal.mul_le_right)
    exact X.calibrated_mul I Ix Iy hI hxy hsq.of_mul_left hsq.of_mul_right
      (hx Ix rfl hsq.of_mul_left) (hy Iy rfl hsq.of_mul_right)

/-- AR-CUBE-CALIBRATION for the chosen data. -/
theorem cube_calibration (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F))))
    (hJ : Squarefree J.val.val) :
    thetaGamma F (X.places : Set (HeightOneSpectrum (𝓞 F))) X.thetaData J 2 ^ 3 =
      (moebius J.val.val : ℂ) * HeckeGeneral.Analysis.heckeIdealCoefficient F X.Lambda J.val := by
  rw [X.thetaGamma_eq_gauss J 2 (by norm_num) (by norm_num), Nat.cast_ofNat, gauss_eq_Γ]
  exact (X.calibrated_of_squarefree (X.axiomIdeal J) hJ).1

/-- AR-MIXED-CALIBRATION for the chosen data. -/
theorem mixed_calibration (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F))))
    (hJ : Squarefree J.val.val) :
    conj (HeckeGeneral.Analysis.heckeIdealCoefficient F X.Lambda J.val) *
        thetaGamma F (X.places : Set (HeightOneSpectrum (𝓞 F))) X.thetaData J 2 *
        thetaGamma F (X.places : Set (HeightOneSpectrum (𝓞 F))) X.thetaData J 1 =
      (moebius J.val.val : ℂ) * HeckeGeneral.Analysis.heckeIdealCoefficient F X.G J.val := by
  rw [X.thetaGamma_eq_gauss J 2 (by norm_num) (by norm_num),
    X.thetaGamma_eq_gauss J 1 (by norm_num) (by norm_num), Nat.cast_ofNat, Nat.cast_one,
    gauss_eq_Γ, gauss_eq_Γ]
  exact (X.calibrated_of_squarefree (X.axiomIdeal J) hJ).2

end ArithmeticChoice

end HeckeAxiom
