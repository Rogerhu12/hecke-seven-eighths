module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceEqualityTransport
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroRowSizeBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOrbitFibre
public import HeckeGeneral.Arithmetic.SIntegerOrbitDilation

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual orbital multiplicities after the one pool

The original rows are the chosen representatives of distinct subgroup
orbits, with the common minus sign on the right Cauchy side. Multiplication
by one nonzero S-integer is injective on those same subgroup orbits.
Consequently a main orbital fibre injects into the actual pool primes
dividing its output ideal. The original large-prime count bounds it by
the pool's existing multiplicity. Error rows are subsets of the original
representative set and have multiplicity at most one.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis

variable {K : Type} [Field K] [NumberField K]

section OrbitArithmetic

variable {A : SArithmeticData K} {Γ : Subgroup A.U}

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

theorem element_orbit_out (q : Q) :
    engineElementOrbit (Γ := Γ) q.out.val = q := by
  rw [engineElementOrbit, dif_pos q.out.property]
  exact Quotient.out_eq q

theorem element_orbit_mul (a b : A.R) (ha : a ≠ 0) (hb : b ≠ 0) :
    engineElementOrbit (Γ := Γ) (a * b) =
      sIntegerOrbitDilation K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
        ⟨a, ha⟩ (engineElementOrbit (Γ := Γ) b) := by
  rw [engineElementOrbit, dif_pos (mul_ne_zero ha hb),
    engineElementOrbit, dif_pos hb, sIntegerOrbitDilation_mk]
  rfl

theorem element_orbit_mul_right_cancel (a b d : A.R)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (heq : engineElementOrbit (Γ := Γ) (a * d) =
      engineElementOrbit (Γ := Γ) (b * d)) :
    engineElementOrbit (Γ := Γ) a = engineElementOrbit (Γ := Γ) b := by
  have hda : engineElementOrbit (Γ := Γ) (a * d) =
      sIntegerOrbitDilation K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
        ⟨d, hd⟩ (engineElementOrbit (Γ := Γ) a) := by
    rw [mul_comm]
    exact element_orbit_mul d a hd ha
  have hdb : engineElementOrbit (Γ := Γ) (b * d) =
      sIntegerOrbitDilation K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
        ⟨d, hd⟩ (engineElementOrbit (Γ := Γ) b) := by
    rw [mul_comm]
    exact element_orbit_mul d b hd hb
  exact sIntegerOrbitDilation_injective K _ Γ ⟨d, hd⟩
    (hda.symm.trans (heq.trans hdb))

theorem element_orbit_out_image_injective (rows : Finset Q) :
    Set.InjOn (engineElementOrbit (Γ := Γ))
      ((rows.image (fun q => q.out.val) : Finset A.R) : Set A.R) := by
  intro a ha b hb hab
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q', _, rfl⟩ := Finset.mem_image.mp hb
  have hqq : q = q' := by simpa only [element_orbit_out] using hab
  exact congrArg (fun q : Q => q.out.val) hqq

theorem element_orbit_neg_out_image_injective (rows : Finset Q) :
    Set.InjOn (engineElementOrbit (Γ := Γ))
      ((rows.image (fun q => -q.out.val) : Finset A.R) : Set A.R) := by
  intro a ha b hb hab
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q', _, rfl⟩ := Finset.mem_image.mp hb
  have hmul : engineElementOrbit (Γ := Γ) (q.out.val * (-1)) =
      engineElementOrbit (Γ := Γ) (q'.out.val * (-1)) := by
    simpa only [mul_neg_one] using hab
  have hqq : q = q' := by
    simpa only [element_orbit_out] using
      element_orbit_mul_right_cancel q.out.val q'.out.val (-1)
        q.out.property q'.out.property (neg_ne_zero.mpr one_ne_zero) hmul
  exact congrArg (fun q : Q => -q.out.val) hqq

theorem generated_ideal_eq_of_element_orbit_eq
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (heq : engineElementOrbit (Γ := Γ) a = engineElementOrbit (Γ := Γ) b) : I = J := by
  have hspan (x : A.R) (hx : x ≠ 0) :
      Ideal.span {(engineElementOrbit (Γ := Γ) x).out.val} = Ideal.span {x} := by
    rw [engineElementOrbit, dif_pos hx]
    exact nonzero_orbit_out_span_mk
      (sIntegerUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) ⟨x, hx⟩
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  rw [A.exteriorIdealEquiv_apply, A.exteriorIdealEquiv_apply]
  calc
    A.extendIdeal I = Ideal.span {a} := ha.2.symm
    _ = Ideal.span {(engineElementOrbit (Γ := Γ) a).out.val} := (hspan a ha.1).symm
    _ = Ideal.span {(engineElementOrbit (Γ := Γ) b).out.val} := by rw [heq]
    _ = Ideal.span {b} := hspan b hb.1
    _ = A.extendIdeal J := hb.2

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}

theorem amplified_orbit_fiber_count (C : A.GeneralArithmeticContext σ η hS)
    (pairs : Finset (A.R × ExteriorPrime A)) (rows : Finset A.R)
    (rowIdeal : A.R → A.Exterior)
    (hrows : ∀ x ∈ pairs, x.1 ∈ rows ∧ A.Generates (rowIdeal x.1) x.1)
    (hinj : Set.InjOn (engineElementOrbit (Γ := Γ)) (rows : Set A.R))
    (I : A.Exterior) (y : A.R) (hy : A.Generates I y)
    (houtput : ∀ x ∈ pairs, engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) =
      engineElementOrbit (Γ := Γ) y)
    (Z ell B : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ x ∈ pairs, Z ^ ell ≤ (Ideal.absNorm x.2.val.asIdeal : ℝ))
    (hupper : (Ideal.absNorm I.val : ℝ) ≤ Z ^ B) :
    (pairs.card : ℝ) ≤ B / ell := by
  refine indexed_large_prime_ideal_count pairs (fun x => x.2.val.asIdeal) ?_
    (fun x _ => x.2.val.prime) I.val I.property.1 ?_ Z ell B hZ hell hlower hupper
  · intro x hx x' hx' heq
    have hp : x.2 = x'.2 := Subtype.ext (HeightOneSpectrum.asIdeal_injective heq)
    have hfreq : engineElementOrbit (Γ := Γ) (x.1 * generator C x.2 ^ 6) =
        engineElementOrbit (Γ := Γ) (x'.1 * generator C x.2 ^ 6) := by
      change engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x) = _
      rw [houtput x hx, hp]
      exact (houtput x' hx').symm
    have hrow := element_orbit_mul_right_cancel x.1 x'.1 (generator C x.2 ^ 6)
      (hrows x hx).2.1 (hrows x' hx').2.1
      (pow_ne_zero 6 (generator_generates C x.2).1) hfreq
    exact Prod.ext (hinj (hrows x hx).1 (hrows x' hx').1 hrow) hp
  · intro x hx
    have hg := amplifiedExterior_generates C (rowIdeal x.1) x.2 x.1 (hrows x hx).2
    have he := generated_ideal_eq_of_element_orbit_eq _ _ _ _ hg hy (houtput x hx)
    rw [← congrArg Subtype.val he, amplifiedExterior_val]
    exact (dvd_pow_self x.2.val.asIdeal (by decide : 6 ≠ 0)).trans (dvd_mul_right _ _)

theorem main_rows_orbit_fiber_count
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
    {C : A.GeneralArithmeticContext σ η hS}
    {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
    (d : FirstGaussPoolData C P ι)
    (hinj : Set.InjOn (engineElementOrbit (Γ := Γ)) (d.rows : Set A.R))
    (q : Q) (hq : q ∈ d.mainRows.image (engineElementOrbit (Γ := Γ))) :
    ((d.mainRows.filter (fun y => engineElementOrbit (Γ := Γ) y = q)).card : ℝ) ≤
      d.multiplicity := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  let fiber := d.eligible.filter (fun z =>
    engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C z) =
      engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x))
  have hmem (z : A.R × ExteriorPrime A) (hz : z ∈ d.eligible) :
      z.1 ∈ d.rows ∧ z.2 ∈ P.primes :=
    Finset.mem_product.mp (Finset.mem_filter.mp hz).1
  have himage : d.mainRows.filter (fun y => engineElementOrbit (Γ := Γ) y =
      engineElementOrbit (Γ := Γ) (actualFrequencyAmplify C x)) =
      fiber.image (actualFrequencyAmplify C) := by
    ext y
    simp only [FirstGaussPoolData.mainRows, fiber, Finset.mem_filter, Finset.mem_image]
    aesop
  rw [himage]
  refine (Nat.cast_le.mpr (Finset.card_image_le :
    (fiber.image (actualFrequencyAmplify C)).card ≤ fiber.card)).trans ?_
  apply amplified_orbit_fiber_count C fiber d.rows d.rowIdeal
    (fun z hz => ⟨(hmem z (Finset.mem_filter.mp hz).1).1,
      d.row_generates z.1 (hmem z (Finset.mem_filter.mp hz).1).1⟩)
    hinj (amplifiedExterior (d.rowIdeal x.1) x.2) (actualFrequencyAmplify C x)
    (amplifiedExterior_generates C (d.rowIdeal x.1) x.2 x.1
      (d.row_generates x.1 (hmem x hx).1))
    (fun z hz => (Finset.mem_filter.mp hz).2)
    Z (ell / 2) (d.rowExponent + 6 * ell) P.base_gt_one
    (div_pos P.exponent_pos (by norm_num))
    (fun z hz => P.norm_lower z.2 (hmem z (Finset.mem_filter.mp hz).1).2)
  have hn := idealAmplify_norm ((d.rowIdeal x.1).val, x.2.val.asIdeal)
    Z d.rowExponent ell (zero_lt_one.trans P.base_gt_one)
    (d.row_norm x.1 (hmem x hx).1) (P.norm_upper x.2 (hmem x hx).2)
  simpa only [idealAmplify, amplifiedExterior_val] using hn

end OrbitArithmetic

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem first_key_orbit_injective (hF : F.Realizes) (key : FirstCauchyKey F) :
    Set.InjOn (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
      ((FirstCauchyKey.data key).rows : Set (Arithmetic.data c).R) := by
  cases hside : FirstCauchyKey.side key
  · have hdata : FirstCauchyKey.data key = (FirstCauchyKey.piece key).leftData := by
      simp only [FirstCauchyKey.data, hside, Bool.false_eq_true, if_false]
    have hrows : (FirstCauchyKey.data key).rows =
        ((F.source.source key.1).divisorRows key.2.1.val).image (fun q => q.out.val) :=
      (congrArg (fun d : DirectGaussData (Arithmetic.context c) F.source.Column =>
        d.rows) hdata).trans (hF.leftRows key.1 key.2.1)
    exact Eq.mpr
      (congrArg (fun rows : Finset (Arithmetic.data c).R =>
        Set.InjOn (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
          (rows : Set (Arithmetic.data c).R)) hrows)
      (element_orbit_out_image_injective
        ((F.source.source key.1).divisorRows key.2.1.val))
  · have hdata : FirstCauchyKey.data key = (FirstCauchyKey.piece key).rightData := by
      simp only [FirstCauchyKey.data, hside, if_true]
    have hrows : (FirstCauchyKey.data key).rows =
        ((F.source.source key.1).divisorRows key.2.1.val).image (fun q => -q.out.val) :=
      (congrArg (fun d : DirectGaussData (Arithmetic.context c) F.source.Column =>
        d.rows) hdata).trans (hF.rightRows key.1 key.2.1)
    exact Eq.mpr
      (congrArg (fun rows : Finset (Arithmetic.data c).R =>
        Set.InjOn (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
          (rows : Set (Arithmetic.data c).R)) hrows)
      (element_orbit_neg_out_image_injective
        ((F.source.source key.1).divisorRows key.2.1.val))

theorem first_family_orbit_injective (hF : F.Realizes) (hfamily : family.Realizes)
    (i : Fin family.count) :
    Set.InjOn (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
      ((family.source i).source.rows : Set (Arithmetic.data c).R) := by
  rw [source_rows_of_heq (family.source i).source
    ((FirstCauchyKey.data (family.index i)).directSource
      (FirstCauchyKey.coefficient (family.index i))) (hfamily.column i) (hfamily.source i)]
  exact first_key_orbit_injective hF (family.index i)

theorem source_orbit_multiplicity_le_one (source : PhysicalSource call p)
    (hinj : Set.InjOn (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
      (source.source.rows : Set (Arithmetic.data c).R)) :
    source.orbitMultiplicity ≤ 1 := by
  apply Finset.sup_le
  intro q _
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  obtain ⟨ha, hqa⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hqb⟩ := Finset.mem_filter.mp hb
  exact hinj ha hb (hqa.trans hqb.symm)

theorem first_family_orbit_multiplicity_le_one (hF : F.Realizes)
    (hfamily : family.Realizes) (i : Fin family.count) :
    (family.source i).orbitMultiplicity ≤ 1 :=
  source_orbit_multiplicity_le_one _ (first_family_orbit_injective hF hfamily i)

private theorem nat_sup_cast_le {α : Type*} (s : Finset α) (f : α → ℕ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ a ∈ s, (f a : ℝ) ≤ B) :
    ((s.sup f : ℕ) : ℝ) ≤ B := by
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simpa using hB
  | @insert a s ha ih =>
    intro hf
    rw [Finset.sup_insert, Nat.cast_max]
    exact max_le (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem main_orbit_multiplicity_le (hF : F.Realizes) (hfamily : family.Realizes)
    (P : PoolPresentation family) (hP : P.Realizes) (i : Fin family.count)
    (source : PhysicalSource call p) (hsource : P.MainOrigin i source) :
    (source.orbitMultiplicity : ℝ) ≤ (P.data i).multiplicity := by
  have hrows : (P.data i).rows = (family.source i).source.rows :=
    congrArg ActualGaussSource.rows (hP.original i)
  have hinj : Set.InjOn (engineElementOrbit (Γ := Arithmetic.unitSubgroup c))
      ((P.data i).rows : Set (Arithmetic.data c).R) := by
    rw [hrows]
    exact first_family_orbit_injective hF hfamily i
  have hout : source.source.rows = (P.data i).mainRows :=
    source_rows_of_heq source.source
      ((P.data i).mainSource (family.source i).source.coefficient) hsource.1 hsource.2.1
  unfold PhysicalSource.orbitMultiplicity
  rw [hout]
  apply nat_sup_cast_le
  · unfold FirstGaussPoolData.multiplicity
    exact div_nonneg (add_nonneg (P.data i).rowExponent_nonneg
      (mul_nonneg (by norm_num) P.pool.exponent_pos.le))
      (div_nonneg P.pool.exponent_pos.le (by norm_num))
  · exact main_rows_orbit_fiber_count (P.data i) hinj

theorem error_orbit_multiplicity_le_one (hF : F.Realizes) (hfamily : family.Realizes)
    (P : PoolPresentation family) (hP : P.Realizes) (i : Fin family.count)
    (q : P.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (hsource : P.ErrorOrigin i q e source) :
    source.orbitMultiplicity ≤ 1 := by
  apply source_orbit_multiplicity_le_one
  have hrows : (P.data i).rows = (family.source i).source.rows :=
    congrArg ActualGaussSource.rows (hP.original i)
  have hout : source.source.rows = (P.data i).errorRows q.val :=
    source_rows_of_heq source.source
      ((P.data i).residualSource q.val e.multiplicity (family.source i).source.coefficient)
      hsource.1 hsource.2.1
  rw [hout]
  intro a ha b hb hab
  exact first_family_orbit_injective hF hfamily i
    (hrows ▸ (Finset.mem_filter.mp ha).1)
    (hrows ▸ (Finset.mem_filter.mp hb).1) hab

/-- This constant precedes the moving call, the actual row carrier
and the one pool. The direct and error branches are covered by one. -/
def secondOrbitBound (c : TargetContext K) : ℝ :=
  max 1 ((20 + 2 * recipeInductionSigma c) / (recipeInductionSigma c / 6))

theorem secondOrbitBound_one_le (c : TargetContext K) : 1 ≤ secondOrbitBound c :=
  le_max_left _ _

theorem secondOrbitBound_pos (c : TargetContext K) : 0 < secondOrbitBound c :=
  zero_lt_one.trans_le (secondOrbitBound_one_le c)

theorem pool_multiplicity_le_orbit_bound
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : FirstZeroProof.uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤
      call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hWindows : ∀ i, (family.source i).Windows)
    (P : PoolPresentation family) (hP : P.Realizes) (i : Fin family.count) :
    (P.data i).multiplicity ≤ secondOrbitBound c := by
  have hsigma : 0 < recipeInductionSigma c := (recipeInduction_budget (c := c)).1
  have hrow := pool_rowExponent_le frame input hframe hannulusZ F hF family hfamily
    hWindows P hP i
  unfold FirstGaussPoolData.multiplicity
  calc
    _ ≤ (20 + 6 * (recipeInductionSigma c / 3)) /
        ((recipeInductionSigma c / 3) / 2) :=
      div_le_div_of_nonneg_right (add_le_add hrow le_rfl) (by positivity)
    _ = (20 + 2 * recipeInductionSigma c) / (recipeInductionSigma c / 6) := by
      congr 1 <;> ring
    _ ≤ secondOrbitBound c := le_max_right _ _

theorem origin_orbit_multiplicity_le_bound
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : FirstZeroProof.uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤
      call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hWindows : ∀ i, (family.source i).Windows)
    (P : PoolPresentation family) (hP : P.Realizes)
    (index : P.Index) (source : PhysicalSource call p) (hsource : P.Origin index source) :
    (source.orbitMultiplicity : ℝ) ≤ secondOrbitBound c := by
  rcases index with ⟨i, tag⟩
  cases tag with
  | inl unit =>
    exact (main_orbit_multiplicity_le hF hfamily P hP i source hsource).trans
      (pool_multiplicity_le_orbit_bound frame input hframe hannulusZ F hF family hfamily
        hWindows P hP i)
  | inr qe =>
    have hle : (source.orbitMultiplicity : ℝ) ≤ 1 := by
      exact_mod_cast error_orbit_multiplicity_le_one hF hfamily P hP i qe.1 qe.2 source hsource
    exact hle.trans (secondOrbitBound_one_le c)

/-- Every member of the actual expansion uses the same fixed orbital
bound. The original source indexing equivalence is left untouched. -/
theorem expansion_orbit_multiplicity_le
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : FirstZeroProof.uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤
      call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hWindows : ∀ i, (family.source i).Windows)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes) :
    ∀ i, ((expansion.source i).orbitMultiplicity : ℝ) ≤ secondOrbitBound c := by
  cases expansion with
  | direct =>
    intro i
    have hle : ((family.source i).orbitMultiplicity : ℝ) ≤ 1 := by
      exact_mod_cast first_family_orbit_multiplicity_le_one hF hfamily i
    exact hle.trans (secondOrbitBound_one_le c)
  | pooled P count index source =>
    intro i
    exact origin_orbit_multiplicity_le_bound frame input hframe hannulusZ F hF family
      hfamily hWindows P hexpansion.2.1 (index i) (source i) (hexpansion.2.2 i)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
