import HeckeGeneral.Arithmetic.FiniteIndexUnitBalancing
import HeckeGeneral.Arithmetic.FiniteIndexSUnitValuationReduction
import HeckeGeneral.Characters.LocalUnitDecomposition
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Joint finite-place and archimedean reduction by actual S-units

The local group includes the units of the mixed archimedean algebra and the
units of every actual completion in S. Ordinary units in the pullback of Γ
balance the archimedean coordinate without changing any finite valuation.
This can be done after the finite-box reduction by elements of Γ.

The archimedean coordinate is explicitly normalized by its arithmetic norm
root. No compactness of the unnormalized local group modulo Γ is asserted:
its positive radial norm parameter has not been quotiented out. The actual
S-unit product formula is proved below. Compactness of the finite local
annuli and the resulting norm-one representatives remain separate steps.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum HeckeGeneral.Characters
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- Genuine archimedean and finite local multiplication groups. -/
abbrev sLocalMultiplicativeGroup :=
  (mixedSpace K)ˣ × ((v : S) → (v.val.adicCompletion K)ˣ)

def sLocalDiagonal : S.unit K →* sLocalMultiplicativeGroup K S where
  toFun u :=
    (Units.map (mixedEmbedding K).toMonoidHom (u : Kˣ),
      fun v => Units.map (algebraMap K (v.val.adicCompletion K)).toMonoidHom (u : Kˣ))
  map_one' := by ext <;> simp
  map_mul' u w := by ext <;> simp

/-- The exponent of the valuation, rather than the opposite uniformizer order. -/
def sLocalValuation (x : sLocalMultiplicativeGroup K S) (v : S) : ℤ :=
  -(localOrderHom K v.val (x.2 v)).toAdd

theorem sLocalValuation_mul (x y : sLocalMultiplicativeGroup K S) (v : S) :
    sLocalValuation K S (x * y) v =
      sLocalValuation K S x v + sLocalValuation K S y v := by
  change -(localOrderHom K v.val (x.2 v * y.2 v)).toAdd = _
  rw [map_mul, toAdd_mul, neg_add]
  rfl

theorem sLocalValuation_diagonal (u : S.unit K) (v : S) :
    sLocalValuation K S (sLocalDiagonal K S u) v =
      (sUnitValuations K S u v).toAdd := by
  change -(-WithZero.log (Valued.v
    (algebraMap K (v.val.adicCompletion K) ((u : Kˣ) : K)))) = _
  rw [neg_neg]
  change WithZero.log (Valued.v (((u : Kˣ) : K) : v.val.adicCompletion K)) = _
  rw [adicCompletion.valued_coe, ← valuationOfNeZero_eq]
  rfl

/-- An ordinary unit has valuation one at every finite place. -/
theorem ordinaryUnit_valuation_eq_one (u : (𝓞 K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1 := by
  have hmul : v.valuation K (algebraMap (𝓞 K) K (u : 𝓞 K)) *
      v.valuation K (algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  exact eq_one_of_one_le_mul_left (v.valuation_le_one (u : 𝓞 K))
    (v.valuation_le_one ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) hmul.symm.le

/-- The actual inclusion of ordinary units into Mathlib's S-unit subgroup. -/
def ordinaryUnitToSUnit : (𝓞 K)ˣ →* S.unit K where
  toFun u := ⟨Units.map (algebraMap (𝓞 K) K).toMonoidHom u,
    fun v _ => ordinaryUnit_valuation_eq_one K u v⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' u w := by apply Subtype.ext; exact map_mul _ u w

@[simp] theorem sUnitValuations_ordinaryUnit (u : (𝓞 K)ˣ) (v : S) :
    sUnitValuations K S (ordinaryUnitToSUnit K S u) v = 1 := by
  apply WithZero.coe_injective
  change (v.val.valuationOfNeZero
    (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) :
      WithZero (Multiplicative ℤ)) = 1
  rw [valuationOfNeZero_eq]
  exact ordinaryUnit_valuation_eq_one K u v.val

/-- Its finite index follows by comap, with no S-unit rank theorem. -/
def ordinaryUnitPullback (Γ : Subgroup (S.unit K)) : Subgroup (𝓞 K)ˣ :=
  Γ.comap (ordinaryUnitToSUnit K S)

instance ordinaryUnitPullback_finiteIndex (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    (ordinaryUnitPullback K S Γ).FiniteIndex := by
  unfold ordinaryUnitPullback
  infer_instance

theorem sLocal_archNorm_ne_zero (x : sLocalMultiplicativeGroup K S) :
    mixedEmbedding.norm (x.1 : mixedSpace K) ≠ 0 := by
  have h := congrArg mixedEmbedding.norm x.1.val_inv
  rw [map_mul, map_one] at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- A second reduction in Γ balances the archimedean coordinate while leaving
every actual local valuation unchanged. -/
theorem exists_subgroup_ordinaryUnit_balance
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (x : sLocalMultiplicativeGroup K S) :
    ∃ u : Γ,
      (arithmeticNormRoot K (x.1 : mixedSpace K))⁻¹ •
        ((sLocalDiagonal K S (u : S.unit K) * x).1 : mixedSpace K) ∈
          finiteIndexBalancedShape K (ordinaryUnitPullback K S Γ) ∧
      ∀ v : S, sLocalValuation K S (sLocalDiagonal K S (u : S.unit K) * x) v =
        sLocalValuation K S x v := by
  obtain ⟨u, hu⟩ := exists_subgroup_unit_normalize_mem K
    (ordinaryUnitPullback K S Γ) (sLocal_archNorm_ne_zero K S x)
  let g : Γ := ⟨ordinaryUnitToSUnit K S (u : (𝓞 K)ˣ), u.property⟩
  refine ⟨g, ?_, fun v => ?_⟩
  · change (arithmeticNormRoot K (x.1 : mixedSpace K))⁻¹ •
      (mixedEmbedding K (algebraMap (𝓞 K) K (u : (𝓞 K)ˣ)) *
        (x.1 : mixedSpace K)) ∈ _
    simpa only [unitSMul_smul, RingOfIntegers.coe_eq_algebraMap] using hu
  · rw [sLocalValuation_mul, sLocalValuation_diagonal]
    change (sUnitValuations K S (ordinaryUnitToSUnit K S (u : (𝓞 K)ˣ)) v).toAdd +
      sLocalValuation K S x v = _
    rw [sUnitValuations_ordinaryUnit]
    simp

variable [Fintype S]

/-- The normalized archimedean norm and the actual finite-completion norms. -/
def sLocalProductNorm (x : sLocalMultiplicativeGroup K S) : ℝ :=
  mixedEmbedding.norm (x.1 : mixedSpace K) * ∏ v : S, ‖(x.2 v).val‖

theorem sLocalProductNorm_mul (x y : sLocalMultiplicativeGroup K S) :
    sLocalProductNorm K S (x * y) =
      sLocalProductNorm K S x * sLocalProductNorm K S y := by
  change mixedEmbedding.norm ((x.1 : mixedSpace K) * (y.1 : mixedSpace K)) *
    (∏ v : S, ‖(x.2 v).val * (y.2 v).val‖) = _
  rw [map_mul]
  simp only [norm_mul, Finset.prod_mul_distrib, sLocalProductNorm]
  ring

omit [Fintype S] in
/-- Away from S, the actual local norm of a principal S-unit is one. -/
theorem sUnit_finiteNorm_eq_one_outside (u : S.unit K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    ‖FinitePlace.embedding v ((u : Kˣ) : K)‖ = 1 := by
  rw [FinitePlace.norm_embedding', Set.unit_valuation_eq_one S K u hv]
  simp

/-- Thus the product over S is the complete finite-place product, rather than
a truncated product with an assumed omitted factor. -/
theorem sUnit_finiteNorm_finprod_eq_prod (u : S.unit K) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      ‖FinitePlace.embedding v ((u : Kˣ) : K)‖) =
        ∏ v : S, ‖FinitePlace.embedding v.val ((u : Kˣ) : K)‖ := by
  rw [finprod_eq_prod_of_mulSupport_subset
    (fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v ((u : Kˣ) : K)‖)
    (s := S.toFinset) (by
      intro v hv
      apply Set.mem_toFinset.mpr
      by_contra hnot
      exact hv (sUnit_finiteNorm_eq_one_outside K S u v hnot))]
  exact Finset.prod_subtype S.toFinset (fun _ => Set.mem_toFinset) _

/-- The genuine number-field product formula on the local diagonal S-units. -/
theorem sLocalProductNorm_diagonal (u : S.unit K) :
    sLocalProductNorm K S (sLocalDiagonal K S u) = 1 := by
  have hfin := FinitePlace.prod_eq_inv_abs_norm (K := K) (x := ((u : Kˣ) : K))
    (u : Kˣ).ne_zero
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm] at hfin
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply] at hfin
  rw [sUnit_finiteNorm_finprod_eq_prod K S u] at hfin
  change mixedEmbedding.norm (mixedEmbedding K ((u : Kˣ) : K)) *
    (∏ v : S, ‖FinitePlace.embedding v.val ((u : Kˣ) : K)‖) = 1
  rw [norm_eq_norm, hfin]
  have hn : Algebra.norm ℚ ((u : Kˣ) : K) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr (u : Kˣ).ne_zero
  exact_mod_cast (mul_inv_cancel₀ (abs_ne_zero.mpr hn))

/-- The diagonal action preserves the actual product norm, so it acts on its
norm-one level set without any new product-formula assumption. -/
theorem sLocalProductNorm_diagonal_mul (u : S.unit K)
    (x : sLocalMultiplicativeGroup K S) :
    sLocalProductNorm K S (sLocalDiagonal K S u * x) =
      sLocalProductNorm K S x := by
  rw [sLocalProductNorm_mul, sLocalProductNorm_diagonal, one_mul]

/-- Both reductions act on the same actual local point by a genuine element
of Γ. The scale is measured after the first, finite-valuation reduction. -/
theorem exists_subgroup_joint_local_reduction
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (x : sLocalMultiplicativeGroup K S) :
    ∃ u v : Γ,
      let y := sLocalDiagonal K S (u : S.unit K) * x
      (arithmeticNormRoot K (y.1 : mixedSpace K))⁻¹ •
        ((sLocalDiagonal K S ((v * u : Γ) : S.unit K) * x).1 : mixedSpace K) ∈
          finiteIndexBalancedShape K (ordinaryUnitPullback K S Γ) ∧
      ∀ w : S,
        0 ≤ sLocalValuation K S (sLocalDiagonal K S ((v * u : Γ) : S.unit K) * x) w ∧
        sLocalValuation K S (sLocalDiagonal K S ((v * u : Γ) : S.unit K) * x) w <
          (finiteIndexSUnitBoxWidth K S Γ : ℤ) := by
  obtain ⟨u, hu⟩ := exists_subgroup_sUnit_valuation_in_box K S Γ
    (sLocalValuation K S x)
  let y := sLocalDiagonal K S (u : S.unit K) * x
  obtain ⟨v, hv, hval⟩ := exists_subgroup_ordinaryUnit_balance K S Γ y
  have hpoint : sLocalDiagonal K S ((v * u : Γ) : S.unit K) * x =
      sLocalDiagonal K S (v : S.unit K) * y := by
    change sLocalDiagonal K S ((v : S.unit K) * (u : S.unit K)) * x = _
    rw [map_mul, mul_assoc]
  refine ⟨u, v, ?_⟩
  change (arithmeticNormRoot K (y.1 : mixedSpace K))⁻¹ • _ ∈ _ ∧ _
  rw [hpoint]
  refine ⟨hv, fun w => ?_⟩
  rw [hval w]
  change 0 ≤ sLocalValuation K S (sLocalDiagonal K S (u : S.unit K) * x) w ∧ _
  rw [sLocalValuation_mul, sLocalValuation_diagonal]
  simpa only [add_comm] using hu w

end HeckeGeneral.Arithmetic
