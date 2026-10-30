import HeckeAxiom.SexticSymbolDictionary
import DedekindZetaZeroFree.Arithmetic.Kummer.QuadraticCharacterFamilyAndConductorShape
import DedekindZetaZeroFree.LargeSieve.CharacterBounds.OrientedHeckeRows

/-!
# The quadratic large sieve for the chosen generators (MI-M-QUADRATIC-SIEVE)

For one Axiom arithmetic choice `X`, the cubes of the skeleton's sextic symbols
`idealSymbol J (gen I) ^ 3` are the values `(ℱ.χ J) I` of Axiom's actual Kummer
quadratic family built from the SAME arithmetic context `X.C`. The skeleton's
generators are the context's chosen representatives, so no unit translation is
needed; sextic reciprocity for allowed generators swaps the two arguments.
The Goldmakher–Louvel bound `rm_hgl_oriented_masked` then gives the sieve.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {root12 : F} {τ : F →+* ℂ}
variable (X : ArithmeticChoice F S₀ root12 τ)

local notation "SS" => (X.places : Set (HeightOneSpectrum (𝓞 F)))

/-- The skeleton generator is the context's chosen allowed representative. -/
theorem thetaData_generator_eq_representative (J : ExteriorIdeal F SS) :
    X.thetaData.generator J =
      (KummerSquarefreeMembers.chooseRepresentative X.A τ X.η X.hS X.C
        ((exteriorEquiv X.A).symm J)).integral := by
  apply Subtype.ext
  have h := (recipeGenerator_spec X.A (recipeOfContext X.A X.C) J).2
  have hr := (KummerSquarefreeMembers.chooseRepresentative X.A τ X.η X.hS X.C
    ((exteriorEquiv X.A).symm J)).radical_eq
  exact h.symm.trans hr

theorem exterior_cop (J : ExteriorIdeal F SS) :
    J.val.val ⊔ uniformSquareUnitModulus X.A.Sf = ⊤ :=
  (KummerSquarefreeMembers.exterior_iff X.A J.val.val).mpr
    ((exteriorEquiv X.A).symm J).property.2

theorem exterior_ne_bot (J : ExteriorIdeal F SS) : J.val.val ≠ ⊥ :=
  ((exteriorEquiv X.A).symm J).property.1

/-- The cubed sextic symbol is the actual Kummer quadratic family. -/
theorem exists_quadraticFamily_eq_symbol :
    ∃ ℱ : QuadraticHeckeFamily F (uniformSquareUnitModulus X.A.Sf),
      ∀ I J : ExteriorIdeal F SS, Squarefree J.val.val →
        (ℱ.χ J.val.val) I.val.val =
          idealSymbol F SS X.thetaData J (X.thetaData.generator I) ^ 3 := by
  have h12 : (primitiveRoots 12 F).Nonempty :=
    ⟨X.A.zeta12, (mem_primitiveRoots (by norm_num)).mpr X.A.primitive_zeta12⟩
  obtain ⟨_, _, ℱ, hℱ⟩ :=
    RMKummerFamily.exists_actualKummerFamily h12 X.A τ X.η X.hS X.C
  refine ⟨ℱ, fun I J hJ => ?_⟩
  have hval := hℱ.2.2.2.2.2.2.2.1 J.val.val hJ (exterior_cop X J)
    I.val.val (exterior_ne_bot X I) (exterior_cop X I)
  rw [hval, ← X.idealSymbol_reciprocity I J, X.idealSymbol_eq I,
    thetaData_generator_eq_representative X J]
  have hc : KummerSquarefreeMembers.exteriorIndex X.A J.val.val hJ (exterior_cop X J) =
      (exteriorEquiv X.A).symm J := Subtype.ext rfl
  have hd : KummerExteriorValues.exteriorIndex X.A I.val.val (exterior_ne_bot X I)
      (exterior_cop X I) = (exteriorEquiv X.A).symm I := Subtype.ext rfl
  rw [hc, hd]
  rfl

/-- MI-M-QUADRATIC-SIEVE for one arithmetic choice. -/
theorem quadratic_sieve_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ Xb Yb : ℝ, 1 ≤ Xb → 1 ≤ Yb →
      ∀ A B : Finset (ExteriorIdeal F SS),
        (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm F SS I ≤ Xb) →
        (∀ J ∈ B, Squarefree J.val.val ∧ exteriorNorm F SS J ≤ Yb) →
        ∀ z : ExteriorIdeal F SS → ℂ,
          ∑ I ∈ A, ‖∑ J ∈ B, z J *
            idealSymbol F SS X.thetaData J (X.thetaData.generator I) ^ 3‖ ^ 2 ≤
            C * (Xb * Yb) ^ ε * (Xb + Yb) * ∑ J ∈ B, ‖z J‖ ^ 2 := by
  intro ε hε
  obtain ⟨ℱ, hℱ⟩ := exists_quadraticFamily_eq_symbol X
  obtain ⟨L, hL, hbound⟩ := rm_hgl_oriented_masked F X.A.zeta12 X.A.primitive_zeta12
    (uniformSquareUnitModulus X.A.Sf) ℱ ε hε
  refine ⟨L, hL, fun Xb Yb hX hY A B hA hB z => ?_⟩
  -- ideal-level data
  let v : ExteriorIdeal F SS → Ideal (𝓞 F) := fun J => J.val.val
  have hv : Function.Injective v := fun I J h => Subtype.ext (Subtype.ext h)
  let w : Ideal (𝓞 F) → ℂ := fun c => if h : ∃ J ∈ B, v J = c then z h.choose else 0
  have hw : ∀ J ∈ B, w (v J) = z J := by
    intro J hJ
    have hex : ∃ J' ∈ B, v J' = v J := ⟨J, hJ, rfl⟩
    simp only [w, dite_eq_left_of_eq_true (eq_true hex)]
    exact congrArg z (hv hex.choose_spec.2)
  let zf : Ideal (𝓞 F) →₀ ℂ :=
    Finsupp.onFinset (B.image v) w (fun c hc => by
      by_contra hcB
      apply hc
      simp only [w]
      have hne : ¬ ∃ J ∈ B, v J = c := by
        rintro ⟨J, hJ, rfl⟩
        exact hcB (Finset.mem_image_of_mem v hJ)
      rw [dite_eq_right_of_eq_false (eq_false hne)])
  have hsum : ∀ f : Ideal (𝓞 F) → ℂ,
      ∑ c ∈ zf.support, zf c * f c = ∑ J ∈ B, z J * f (v J) := by
    intro f
    have hsub : zf.support ⊆ B.image v := Finsupp.support_onFinset_subset
    rw [Finset.sum_subset hsub (fun c _ hc => by
      rw [Finsupp.notMem_support_iff.mp hc, zero_mul]), Finset.sum_image (fun a _ b _ h => hv h)]
    exact Finset.sum_congr rfl (fun J hJ => by
      simp only [zf, Finsupp.onFinset_apply, hw J hJ])
  have hsq : ∑ c ∈ zf.support, ‖zf c‖ ^ 2 = ∑ J ∈ B, ‖z J‖ ^ 2 := by
    have hsub : zf.support ⊆ B.image v := Finsupp.support_onFinset_subset
    rw [Finset.sum_subset hsub (fun c _ hc => by
      rw [Finsupp.notMem_support_iff.mp hc, norm_zero]; norm_num),
      Finset.sum_image (fun a _ b _ h => hv h)]
    exact Finset.sum_congr rfl (fun J hJ => by
      simp only [zf, Finsupp.onFinset_apply, hw J hJ])
  have hz : ∀ c ∈ zf.support, Squarefree c ∧ c ⊔ uniformSquareUnitModulus X.A.Sf = ⊤ ∧
      (Ideal.absNorm c : ℝ) ≤ Yb := by
    intro c hc
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp (Finsupp.support_onFinset_subset hc)
    exact ⟨(hB J hJ).1, exterior_cop X J, (hB J hJ).2⟩
  have hmain := hbound Xb Yb zf (fun d => ∃ I ∈ A, v I = d) (fun _ => 1) hX hY hz
    (fun _ => by simp)
  rw [hsq] at hmain
  refine le_trans ?_ hmain
  -- the skeleton sum is a sub-sum of the finsum
  have hrow : ∀ I ∈ A, ‖∑ J ∈ B, z J *
      idealSymbol F SS X.thetaData J (X.thetaData.generator I) ^ 3‖ ^ 2 =
      ‖(1 : ℂ) * ∑ c ∈ zf.support, zf c * (ℱ.χ c) (v I)‖ ^ 2 := by
    intro I _
    rw [one_mul, hsum]
    congr 2
    exact Finset.sum_congr rfl (fun J hJ => by rw [hℱ I J (hB J hJ).1])
  rw [Finset.sum_congr rfl hrow]
  let g : Ideal (𝓞 F) → ℝ := fun d =>
    if Squarefree d ∧ d ⊔ uniformSquareUnitModulus X.A.Sf = ⊤ ∧ (Ideal.absNorm d : ℝ) ≤ Xb ∧
        (∃ I ∈ A, v I = d) then
      ‖(fun _ => (1 : ℂ)) d * ∑ c ∈ zf.support, zf c * (ℱ.χ c) d‖ ^ 2 else 0
  have hgA : ∀ I ∈ A, ‖(1 : ℂ) * ∑ c ∈ zf.support, zf c * (ℱ.χ c) (v I)‖ ^ 2 = g (v I) := by
    intro I hI
    simp only [g]
    symm
    exact ite_eq_left_iff.mpr (fun h => absurd ⟨(hA I hI).1, exterior_cop X I, (hA I hI).2, I, hI, rfl⟩ h)
  rw [Finset.sum_congr rfl hgA, ← Finset.sum_image (fun a _ b _ h => hv h)]
  refine le_of_eq ?_
  rw [finsum_eq_sum_of_support_subset _ (s := A.image v) ?_]
  · refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [g]
    congr 1
  · intro d hd
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hd
    obtain ⟨⟨_, _, _, I, hI, rfl⟩, _⟩ := hd
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem v hI)

end HeckeAxiom
