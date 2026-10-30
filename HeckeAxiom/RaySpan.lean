import HeckeAxiom.RayCharacter
import HeckeGeneral.Characters.SIntegerUnitRelation
import HeckeGeneral.Characters.InfinityType
import HeckeGeneral.Characters.ConductorFrequencyMembership
import HeckeGeneral.Characters.PrincipalUnitFiltration

/-!
# The principal law for finite-order Hecke characters

Let `χ` be an actual continuous unitary Hecke character of finite order, and let
`α` be a nonzero totally positive integer with `α ≡ 1` modulo the finite
conductor of `χ`. Then the ideal coefficient of `(α)` is one.

The principal idèle of `α` is split into its archimedean part, its coordinates
at the finitely many primes dividing `α` or the conductor, and an integral unit
idèle. Finite order kills the archimedean part on totally positive elements,
the conductor depth kills the ramified coordinates, and the integral unit idèle
is trivial at every ramified place.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Arithmetic
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

/-! ### Archimedean part -/

theorem infiniteComponent_eq_one_of_isComplex (χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (v : InfinitePlace K) (hv : v.IsComplex) (w : v.Completionˣ) :
    infiniteComponent K v χ w = 1 := by
  have hw : infiniteComponent K v χ w =
      complexHeckeComponent K v hv χ (completionUnitsToComplex hv w) := by
    change _ = infiniteComponent K v χ
      (complexUnitsToCompletion hv (completionUnitsToComplex hv w))
    rw [complexUnitsToCompletion_inverse]
  rw [hw, finiteOrder_complexHeckeComponent K v hv hχ]
  rfl

theorem infiniteComponent_eq_one_of_isReal (χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (v : InfinitePlace K) (hv : v.IsReal) (w : v.Completionˣ)
    (hw : 0 < (completionUnitsToReal hv w).val) :
    infiniteComponent K v χ w = 1 := by
  have hw' : infiniteComponent K v χ w =
      realHeckeComponent K v hv χ (completionUnitsToReal hv w) := by
    change _ = infiniteComponent K v χ
      (realUnitsToCompletion hv (completionUnitsToReal hv w))
    rw [realUnitsToCompletion_inverse]
  rw [hw', heckeRealComponent_formula, heckeRealParameter_finiteOrder K v hv hχ]
  simp [hw]

omit [NumberField K] in
/-- The real coordinate of a global element at a real place is its real embedding. -/
theorem completionUnitsToReal_map_val (v : InfinitePlace K) (hv : v.IsReal) (x : Kˣ) :
    (completionUnitsToReal hv (Units.map (algebraMap K v.Completion).toMonoidHom x)).val =
      InfinitePlace.embedding_of_isReal hv (x : K) := by
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
    (algebraMap K v.Completion (x : K)) = _
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv _

/-- A finite-order character is trivial at infinity on totally positive S-units. -/
theorem sUnitInfinityCharacter_eq_one (χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (u : S.unit K)
    (hpos : ∀ φ : K →+* ℝ, 0 < φ ((u : Kˣ) : K)) :
    sUnitInfinityCharacter K S χ u = 1 := by
  change ∏ v, infiniteComponent K v χ (sUnitArchimedean K S u v) = 1
  refine Finset.prod_eq_one fun v _ => ?_
  by_cases hv : v.IsReal
  · apply infiniteComponent_eq_one_of_isReal K χ hχ v hv
    change 0 < (completionUnitsToReal hv
      (Units.map (algebraMap K v.Completion).toMonoidHom (u : Kˣ))).val
    rw [completionUnitsToReal_map_val]
    exact hpos _
  · exact infiniteComponent_eq_one_of_isComplex K χ hχ v
      (InfinitePlace.not_isReal_iff_isComplex.mp hv) _

/-! ### Finite part -/

section FinitePart

/-- The archimedean coordinate of an idèle, as a monoid homomorphism. -/
def ideleInfinitePart : IdeleGroup (𝓞 K) K →* InfiniteAdeleRing K where
  toFun x := x.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The finite coordinate of an idèle, as a monoid homomorphism. -/
def ideleFinitePart : IdeleGroup (𝓞 K) K →* IsDedekindDomain.FiniteAdeleRing (𝓞 K) K where
  toFun x := x.val.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Evaluation of a finite adèle at one finite place. -/
abbrev finiteEval (w : HeightOneSpectrum (𝓞 K)) :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K →* w.adicCompletion K :=
  RestrictedProduct.evalMonoidHom (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) w

theorem finiteEval_localIdeleEmbedding (v w : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    finiteEval K w (ideleFinitePart K (localIdeleEmbedding K v x)) =
      IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v x.val w := rfl

theorem finiteEval_globalIntegralIdele (u : GlobalIntegralUnits K)
    (w : HeightOneSpectrum (𝓞 K)) :
    finiteEval K w (ideleFinitePart K (globalIntegralIdele K u)) =
      (localIntegerUnitsEmbedding K w (u w)).val := rfl

theorem finiteEval_sUnitFiniteIdele (S : Set (HeightOneSpectrum (𝓞 K))) (u : S.unit K)
    (w : HeightOneSpectrum (𝓞 K)) :
    finiteEval K w (ideleFinitePart K (sUnitFiniteIdele K S u)) =
      (sUnitLocal K S w u).val := rfl

theorem ideleInfinitePart_localIdeleEmbedding (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : ideleInfinitePart K (localIdeleEmbedding K v x) = 1 := rfl

theorem ideleInfinitePart_globalIntegralIdele (u : GlobalIntegralUnits K) :
    ideleInfinitePart K (globalIntegralIdele K u) = 1 := rfl

theorem ideleInfinitePart_sUnitFiniteIdele (S : Set (HeightOneSpectrum (𝓞 K))) (u : S.unit K) :
    ideleInfinitePart K (sUnitFiniteIdele K S u) = 1 := rfl

variable (T : Finset (HeightOneSpectrum (𝓞 K)))

/-- The integral unit coordinates of an S-unit outside `T`, and one inside `T`. -/
def outsideUnits (u : (T : Set (HeightOneSpectrum (𝓞 K))).unit K) : GlobalIntegralUnits K :=
  fun v => if hv : v ∈ T then 1 else
    sUnitLocalInteger K (T : Set (HeightOneSpectrum (𝓞 K))) u v
      (fun h => hv (Finset.mem_coe.mp h))

theorem outsideUnits_of_mem (u : (T : Set (HeightOneSpectrum (𝓞 K))).unit K)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ∈ T) : outsideUnits K T u w = 1 := by
  simp [outsideUnits, hw]

theorem localIntegerUnitsEmbedding_outsideUnits_of_not_mem
    (u : (T : Set (HeightOneSpectrum (𝓞 K))).unit K) {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ∉ T) :
    localIntegerUnitsEmbedding K w (outsideUnits K T u w) =
      sUnitLocal K (T : Set (HeightOneSpectrum (𝓞 K))) w u := by
  simp [outsideUnits, hw]

/-- The finite principal part of an S-unit is the product of its coordinates on
`T` and the integral unit idèle of its coordinates outside `T`. -/
theorem sUnitFiniteIdele_eq (u : (T : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    sUnitFiniteIdele K (T : Set (HeightOneSpectrum (𝓞 K))) u =
      (∏ v ∈ T, localIdeleEmbedding K v
        (sUnitLocal K (T : Set (HeightOneSpectrum (𝓞 K))) v u)) *
        globalIntegralIdele K (outsideUnits K T u) := by
  apply Units.ext
  apply Prod.ext
  · change ideleInfinitePart K (sUnitFiniteIdele K (T : Set (HeightOneSpectrum (𝓞 K))) u) =
      ideleInfinitePart K ((∏ v ∈ T, localIdeleEmbedding K v
        (sUnitLocal K (T : Set (HeightOneSpectrum (𝓞 K))) v u)) *
          globalIntegralIdele K (outsideUnits K T u))
    simp only [map_mul, map_prod, ideleInfinitePart_sUnitFiniteIdele,
      ideleInfinitePart_globalIntegralIdele, ideleInfinitePart_localIdeleEmbedding,
      Finset.prod_const_one, one_mul]
  · change ideleFinitePart K (sUnitFiniteIdele K (T : Set (HeightOneSpectrum (𝓞 K))) u) =
      ideleFinitePart K ((∏ v ∈ T, localIdeleEmbedding K v
        (sUnitLocal K (T : Set (HeightOneSpectrum (𝓞 K))) v u)) *
          globalIntegralIdele K (outsideUnits K T u))
    apply RestrictedProduct.ext
    intro w
    change finiteEval K w (ideleFinitePart K
        (sUnitFiniteIdele K (T : Set (HeightOneSpectrum (𝓞 K))) u)) =
      finiteEval K w (ideleFinitePart K ((∏ v ∈ T, localIdeleEmbedding K v
        (sUnitLocal K (T : Set (HeightOneSpectrum (𝓞 K))) v u)) *
          globalIntegralIdele K (outsideUnits K T u)))
    simp only [map_mul, map_prod, finiteEval_sUnitFiniteIdele, finiteEval_globalIntegralIdele,
      finiteEval_localIdeleEmbedding]
    by_cases hw : w ∈ T
    · rw [Finset.prod_eq_single w
        (fun v _ hvw => finiteOfAdicCompletion_ne K v w _ (Ne.symm hvw))
        (fun hn => absurd hw hn), finiteOfAdicCompletion_same, outsideUnits_of_mem K T u hw]
      simp
    · rw [Finset.prod_eq_one
        (fun v hv => finiteOfAdicCompletion_ne K v w _ (fun h => hw (h ▸ hv))), one_mul,
        localIntegerUnitsEmbedding_outsideUnits_of_not_mem K T u hw]

/-- If `T` contains every ramified place, the finite part of an S-unit is
evaluated by the local components on `T` alone. -/
theorem sUnitFiniteCharacter_eq_prod (χ : HeckeCharacter K)
    (hT : conductorPlaces K χ ⊆ T) (u : (T : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    sUnitFiniteCharacter K (T : Set (HeightOneSpectrum (𝓞 K))) χ u =
      ∏ v ∈ T, localComponent K v χ (sUnitLocal K (T : Set (HeightOneSpectrum (𝓞 K))) v u) := by
  change toIdeleCharacter K χ (sUnitFiniteIdele K (T : Set (HeightOneSpectrum (𝓞 K))) u) = _
  rw [sUnitFiniteIdele_eq K T u, map_mul, map_prod]
  have hg : toIdeleCharacter K χ (globalIntegralIdele K (outsideUnits K T u)) = 1 := by
    change globalIntegralComponent K χ (outsideUnits K T u) = 1
    rw [globalIntegralComponent_eq_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    simp [outsideUnits, hT hv]
  rw [hg, mul_one]
  rfl

end FinitePart

/-! ### Local coordinates of a principal generator -/

/-- The nonzero principal ideal of a nonzero integer. -/
def principalNonzero (α : 𝓞 K) (hα : α ≠ 0) : (Ideal (𝓞 K))⁰ :=
  ⟨Ideal.span {α}, mem_nonZeroDivisors_of_ne_zero (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hα)⟩

omit [NumberField K] in
theorem coe_ne_zero_of_ne_zero (α : 𝓞 K) (hα : α ≠ 0) : (α : K) ≠ 0 := by
  exact_mod_cast hα

/-- The valuation of a nonzero integer is read off from its principal ideal. -/
theorem valuation_coe_eq (α : 𝓞 K) (hα : α ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (α : K) =
      WithZero.exp (-(primeExponents (principalNonzero K α hα) v : ℤ)) := by
  rw [valuation_eq_exp_neg_principal_count K v (α : K) (coe_ne_zero_of_ne_zero K α hα)]
  have hne : Ideal.span {α} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hα
  have hspan : (FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) : FractionalIdeal (𝓞 K)⁰ K) =
      ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_span_singleton (S := (𝓞 K)⁰) (P := K) α).symm
  rw [hspan, FractionalIdeal.count_coe K v hne,
    Ideal.count_associates_factors_eq hne v.isPrime v.ne_bot, primeExponents_apply]
  rfl

/-- A nonzero integer is an S-unit for any finite set containing its prime support. -/
theorem mem_unit_of_support_subset (α : 𝓞 K) (hα : α ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : (primeExponents (principalNonzero K α hα)).support ⊆ T) :
    Units.mk0 (α : K) (coe_ne_zero_of_ne_zero K α hα) ∈
      (T : Set (HeightOneSpectrum (𝓞 K))).unit K := by
  intro v hv
  change v.valuation K (α : K) = 1
  rw [valuation_coe_eq K α hα v]
  have hzero : primeExponents (principalNonzero K α hα) v = 0 := by
    by_contra h
    exact hv (Finset.mem_coe.mpr (hT (Finsupp.mem_support_iff.mpr h)))
  rw [hzero]
  rfl

/-- An integer congruent to one modulo the conductor is prime to every ramified place. -/
theorem primeExponents_eq_zero_of_ramified (χ : HeckeCharacter K) (α : 𝓞 K) (hα : α ≠ 0)
    (hα1 : α - 1 ∈ conductorIdeal K χ) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ UnramifiedAt K χ v) :
    primeExponents (principalNonzero K α hα) v = 0 := by
  have hle : conductorIdeal K χ ≤ v.asIdeal := (conductorIdeal_le_iff K χ v).mpr hv
  have hnot : α ∉ v.asIdeal := by
    intro hmem
    have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem hmem (hle hα1)
      simpa using this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  rw [primeExponents_apply, Multiset.count_eq_zero]
  intro hmem
  have hdiv := (Ideal.mem_normalizedFactors_iff
    (nonZeroDivisors.coe_ne_zero (principalNonzero K α hα))).mp hmem
  exact hnot (Ideal.span_singleton_le_iff_mem _ |>.mp hdiv.2)

/-- The local component at a place, evaluated at a principal generator, is the
corresponding power of the prime coefficient. At ramified places both sides are one. -/
theorem localComponent_coe_eq (χ : HeckeCharacter K) (α : 𝓞 K) (hα : α ≠ 0)
    (hα1 : α - 1 ∈ conductorIdeal K χ) (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) (hx : x.val = ((α : K) : v.adicCompletion K)) :
    (localComponent K v χ x : ℂ) =
      primeCoefficient K χ v ^ primeExponents (principalNonzero K α hα) v := by
  by_cases hv : UnramifiedAt K χ v
  · -- Unramified: divide by the matching power of the uniformizer.
    set e := primeExponents (principalNonzero K α hα) v
    let π := localUniformizerUnit K v
    let y : (v.adicCompletion K)ˣ := x * π ^ (-(e : ℤ))
    have hyv : (Valued.v y.val : WithZero (Multiplicative ℤ)) = 1 := by
      change Valued.v (x.val * (π ^ (-(e : ℤ)) : (v.adicCompletion K)ˣ).val) = 1
      rw [Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, adicCompletion.valued_coe,
        valuation_coe_eq K α hα v, localUniformizerUnit_val, localUniformizer_valuation,
        ← WithZero.exp_zsmul, ← WithZero.exp_add]
      have hzero : (-(primeExponents (principalNonzero K α hα) v : ℤ) +
          (-(e : ℤ)) • (-1 : ℤ)) = 0 := by
        simp [e]
      rw [hzero]
      rfl
    have hy : ‖y.val‖ = 1 :=
      (Valued.toNormedField.norm_eq_one_iff (L := v.adicCompletion K)
        (Γ₀ := WithZero (Multiplicative ℤ))).mpr hyv
    have hχy : localComponent K v χ y = 1 := hv y hy
    have hxy : x = y * π ^ e := by
      change x = x * π ^ (-(e : ℤ)) * π ^ e
      rw [mul_assoc, ← zpow_natCast, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [hxy, map_mul, hχy, one_mul, map_pow, primeCoefficient_of_unramified K χ v hv]
    simp [π]
  · -- Ramified: the conductor depth makes the component trivial.
    rw [primeExponents_eq_zero_of_ramified K χ α hα hα1 v hv, pow_zero]
    have hne : localConductorExponent K χ v ≠ 0 := by
      rwa [Ne, localConductorExponent_eq_zero_iff]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have hdepth := trivialAtDepth_localConductorExponent K χ v
    rw [hn] at hdepth
    have hval : (Valued.v (x.val - 1) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
      have hmem : ((α : K) - 1) ∈
          ((finiteConductor K χ).val : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [FractionalIdeal.mem_coeIdeal]
        exact ⟨α - 1, hα1, by simp⟩
      have hle := valuation_le_exp_neg_count_of_mem K v _ _ hmem
      rw [count_finiteConductor, hn] at hle
      have hsub : x.val - 1 = (((α : K) - 1 : K) : v.adicCompletion K) := by
        rw [hx]
        have h := map_sub (algebraMap K (v.adicCompletion K)) (α : K) 1
        rw [map_one] at h
        exact h.symm
      rw [hsub, adicCompletion.valued_coe]
      exact hle
    have hnorm : ‖x.val - 1‖ ≤ (residueCard K v : ℝ)⁻¹ ^ (n + 1) :=
      (localNorm_le_inv_residueCard_pow_iff K v _ (n + 1)).mpr hval
    rw [hdepth x hnorm]
    rfl

/-! ### The principal law -/

/-- For a finite-order character, a totally positive generator congruent to one
modulo the finite conductor has ideal coefficient one. -/
theorem idealCoefficient_span_eq_one (χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (α : 𝓞 K) (hα : α ≠ 0) (hα1 : α - 1 ∈ conductorIdeal K χ)
    (hpos : ∀ φ : K →+* ℝ, 0 < φ (α : K)) :
    idealCoefficient (primeCoefficient K χ) (Ideal.span {α}) = 1 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      T = (primeExponents (principalNonzero K α hα)).support ∪ conductorPlaces K χ :=
    ⟨_, rfl⟩
  have hsuppT : (primeExponents (principalNonzero K α hα)).support ⊆ T := by
    rw [hT]
    exact Finset.subset_union_left
  have hcondT : conductorPlaces K χ ⊆ T := by
    rw [hT]
    exact Finset.subset_union_right
  obtain ⟨u, hu⟩ : ∃ u : (T : Set (HeightOneSpectrum (𝓞 K))).unit K,
      ((u : Kˣ) : K) = (α : K) :=
    ⟨⟨Units.mk0 (α : K) (coe_ne_zero_of_ne_zero K α hα),
      mem_unit_of_support_subset K α hα T hsuppT⟩, rfl⟩
  have hpos' : ∀ φ : K →+* ℝ, 0 < φ ((u : Kˣ) : K) := by
    intro φ
    rw [hu]
    exact hpos φ
  have hfin : sUnitFiniteCharacter K (T : Set (HeightOneSpectrum (𝓞 K))) χ u = 1 := by
    have h := sUnitFinite_mul_infinity_eq_one K (T : Set (HeightOneSpectrum (𝓞 K))) χ u
    rwa [sUnitInfinityCharacter_eq_one K χ hχ _ u hpos', mul_one] at h
  rw [sUnitFiniteCharacter_eq_prod K T χ hcondT u] at hfin
  have hcoef : idealCoefficient (primeCoefficient K χ) (Ideal.span {α}) =
      ∏ v ∈ T, primeCoefficient K χ v ^ primeExponents (principalNonzero K α hα) v := by
    have h1 : Ideal.span {α} =
        (idealOfPrimeExponents (primeExponents (principalNonzero K α hα))).val :=
      (congrArg Subtype.val
        (idealOfPrimeExponents_primeExponents (principalNonzero K α hα))).symm
    rw [h1]
    change (idealCoefficientHom (primeCoefficient K χ)).toMonoidHom
      (idealOfPrimeExponents (primeExponents (principalNonzero K α hα))).val = _
    rw [map_idealOfPrimeExponents,
      Finsupp.prod_of_support_subset _ hsuppT _ (fun v _ => pow_zero _)]
    refine Finset.prod_congr rfl fun v _ => ?_
    change idealCoefficient (primeCoefficient K χ) v.asIdeal ^ _ = _
    rw [idealCoefficient_prime]
  rw [hcoef]
  calc ∏ v ∈ T, primeCoefficient K χ v ^ primeExponents (principalNonzero K α hα) v
      = ∏ v ∈ T, (localComponent K v χ (sUnitLocal K (T : Set (HeightOneSpectrum (𝓞 K))) v u) : ℂ) := by
        refine Finset.prod_congr rfl fun v _ => ?_
        refine (localComponent_coe_eq K χ α hα hα1 v _ ?_).symm
        change (((u : Kˣ) : K) : v.adicCompletion K) = _
        rw [hu]
    _ = Circle.coeHom (∏ v ∈ T, localComponent K v χ (sUnitLocal K (T : Set (HeightOneSpectrum (𝓞 K))) v u)) := by
        rw [map_prod]
        rfl
    _ = 1 := by
        rw [hfin, map_one]

/-- AxiomMath's ray class character attached to a finite-order Hecke character,
modulo its finite conductor. Its values are the actual Hecke ideal coefficients. -/
def toRayClassCharacter (χ : HeckeCharacter K) (hχ : FiniteOrder χ) :
    DedekindZetaZeroFree.RayClassCharacter K (conductorIdeal K χ) where
  toFun := idealCoefficient (primeCoefficient K χ)
  map_mul' := idealCoefficient_mul _
  map_top' := idealCoefficient_top K χ
  eq_zero_iff' := idealCoefficient_eq_zero_iff K χ
  map_span' := fun α hα hα1 hpos => idealCoefficient_span_eq_one K χ hχ α hα hα1 hpos

@[simp] theorem toRayClassCharacter_apply (χ : HeckeCharacter K) (hχ : FiniteOrder χ)
    (I : Ideal (𝓞 K)) :
    toRayClassCharacter K χ hχ I = idealCoefficient (primeCoefficient K χ) I := rfl

end HeckeAxiom
