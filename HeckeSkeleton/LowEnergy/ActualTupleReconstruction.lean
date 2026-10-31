import HeckeSkeleton.LowEnergy.ActualMarkedTupleEnergy
import HeckeSkeleton.LowEnergy.ActualFrozenReconstruction
import HeckeSkeleton.LowEnergy.TargetGaussian

/-!
# Reconstructing the literal marked row from its original slot tuples

The inactive and active supports are taken from the actual disjoint prime
windows.  Collision removal is exact: inactive collisions are row-only
guards, active frozen collisions are coefficient-only guards, and the
active moving-row collision stays in the original hybrid coprimality mask.
All equalities below are linear identities, before taking any row norm.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualTupleReconstruction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualRows
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualBlockReindex
open HeckeSkeleton.LowEnergy.ActualSourceReindex
open HeckeSkeleton.LowEnergy.ActualFrozenAggregation
open HeckeSkeleton.LowEnergy.ActualFrozenReconstruction
open HeckeSkeleton.LowEnergy.ActualMarkedTupleEnergy
open HeckeSkeleton.LowEnergy.WindowTuples HeckeSkeleton.LowEnergy.InactiveWindows
open scoped Classical BigOperators NumberField nonZeroDivisors ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def subsetsEquiv (Q : Finset (ExteriorPrime K S)) :
    {A : Finset (ExteriorPrime K S) // A ⊆ Q} ≃ Q.powerset where
  toFun A := ⟨A.val, Finset.mem_powerset.mpr A.property⟩
  invFun A := ⟨A.val, Finset.mem_powerset.mp A.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tsum_subsets_eq (Q : Finset (ExteriorPrime K S))
    (f : {A : Finset (ExteriorPrime K S) // A ⊆ Q} → ℂ) :
    (∑' A, f A) = ∑ A ∈ Q.powerset, if hA : A ⊆ Q then f ⟨A, hA⟩ else 0 := by
  let H : Finset (ExteriorPrime K S) → ℂ :=
    fun A => if hA : A ⊆ Q then f ⟨A, hA⟩ else 0
  calc
    _ = ∑' A : Q.powerset, f ((subsetsEquiv K S Q).symm A) :=
      ((subsetsEquiv K S Q).symm.tsum_eq f).symm
    _ = ∑' A : Q.powerset, H A := by
      apply tsum_congr
      intro A
      simp only [H, dif_pos (Finset.mem_powerset.mp A.property)]
      rfl
    _ = _ := Q.powerset.tsum_subtype H

theorem fixedPhysicalRow_zero_of_not_coprime (f : FixedData K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ)
    (Y : ℝ) (k P : ExteriorIdeal K S) (hbad : ¬IsCoprime k.val.val P.val.val) :
    fixedPhysicalRow K S D f F θ V Y k P = 0 := by
  unfold fixedPhysicalRow
  have hz : (∑' s : FrozenState K S f.frozen f.puncture,
      ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
        physicalAtom K S D f s F θ (fun _ => 1) V Y k P cb.1 cb.2) = 0 := by
    simp only [physicalAtom, ActualHybridEntry.hybridAtom, if_neg hbad,
      mul_zero, zero_mul, tsum_zero]
  rw [hz, mul_zero]

/-- Reorder the two finite reflection choices, keeping both complete dual
columns inside each physical row. -/
theorem completedThetaSum_eq_fixedPhysicalRows
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (V : SmoothAnnularTest) (Y : ℝ) (hY : 0 < Y) :
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun
        (Y * exteriorNorm K S (primeSetIdeal K S d.marks)) =
      ∑ A ∈ d.marks.powerset, if hA : A ⊆ d.marks then
        ActualSeparatedBlock.inactiveWeight K S (splitFixed K S d ⟨A, hA⟩) *
          fixedPhysicalRow K S D (splitFixed K S d ⟨A, hA⟩) F θ V.toFun Y
            d.moving (primeSetIdeal K S A) else 0 := by
  letI : Fintype (FrozenState K S d.frozen d.puncture) := Fintype.ofFinite _
  letI : Fintype (MarkChoice K S d) :=
    Fintype.ofEquiv d.marks.powerset (subsetsEquiv K S d.marks).symm
  rw [completedThetaSum_eq_physical_atoms K S D hD F θ hreflection d V Y hY]
  rw [← tsum_subsets_eq K S d.marks]
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  rw [fixedPhysicalRow, ← mul_assoc,
    mul_inv_cancel₀ (inactiveWeight_ne_zero K S (splitFixed K S d A)), one_mul,
    tsum_fintype]

def tuplePhysicalRow (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    {g : PrimeWindowGeometry} (I : Finset (Fin g.slots))
    (b : I → ExteriorPrime K S) (V : ℝ → ℂ) (Y : ℝ) (P : ExteriorIdeal K S) : ℂ :=
  if hb : InactiveGood K S (exteriorPowerfulPart K S x.1) I b then
    if InactiveRowGood K S I b (exteriorResidualPart K S x.1).val.val then
      if ActiveGood K S (exteriorPowerfulPart K S x.1) P then
        fixedPhysicalRow K S D
          (tupleDatum K S (exteriorPowerfulPart K S x.1) (Quotient.out x.2) I b hb)
          F θ V Y (exteriorResidualPart K S x.1) P
      else 0
    else 0
  else 0

theorem tuplePhysicalRow_zero_of_not_coprime
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    {g : PrimeWindowGeometry} (I : Finset (Fin g.slots))
    (b : I → ExteriorPrime K S) (V : ℝ → ℂ) (Y : ℝ) (P : ExteriorIdeal K S)
    (hbad : ¬IsCoprime (exteriorResidualPart K S x.1).val.val P.val.val) :
    tuplePhysicalRow K S D x F θ I b V Y P = 0 := by
  unfold tuplePhysicalRow
  split_ifs
  · exact fixedPhysicalRow_zero_of_not_coprime K S D _ F θ V Y _ P hbad
  all_goals rfl

theorem prime_dvd_actual_parts (I : ExteriorIdeal K S) (p : ExteriorPrime K S)
    (hp : p.val.asIdeal ∣ I.val.val) :
    p.val.asIdeal ∣ (exteriorResidualPart K S I).val.val ∨
      p.val.asIdeal ∣ (exteriorPowerfulPart K S I).val.val := by
  have hdec := congrArg (fun A : ExteriorIdeal K S => A.val.val)
    (exterior_residual_powerful_decomposition K S I)
  change (exteriorResidualPart K S I).val.val *
    (exteriorPowerfulPart K S I).val.val = I.val.val at hdec
  rw [← hdec] at hp
  exact p.val.prime.dvd_mul.mp hp

theorem tuplePhysicalRow_zero_of_collision
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (M A : Finset (Fin g.slots))
    (t : Fin g.slots → ExteriorPrime K S) (V : ℝ → ℂ) (Y : ℝ)
    (p : ExteriorPrime K S) (hp : p ∈ M.image t) (hpi : p.val.asIdeal ∣ x.1.val.val) :
    tuplePhysicalRow K S D x F θ (M \ A) (fun i => t i) V Y
      (activeIdeal K S A (fun i => t i)) = 0 := by
  obtain ⟨i, hiM, hit⟩ := Finset.mem_image.mp hp
  rcases prime_dvd_actual_parts K S x.1 p hpi with hpk | hpf
  · by_cases hiA : i ∈ A
    · apply tuplePhysicalRow_zero_of_not_coprime K S D x F θ
        (M \ A) (fun i => t i) V Y
      intro hcop
      have hpP : p.val.asIdeal ∣ (activeIdeal K S A (fun i => t i)).val.val := by
        apply (prime_dvd_primeSetIdeal_iff K S _ p).mpr
        exact Finset.mem_image.mpr ⟨⟨i, hiA⟩, Finset.mem_univ _, hit⟩
      exact p.val.prime.not_unit (hcop.isUnit_of_dvd' hpk hpP)
    · have hbad : ¬InactiveRowGood K S (M \ A) (fun i => t i)
          (exteriorResidualPart K S x.1).val.val := by
        intro h
        exact h ⟨i, Finset.mem_sdiff.mpr ⟨hiM, hiA⟩⟩ (hit.symm ▸ hpk)
      simp [tuplePhysicalRow, hbad]
  · by_cases hiA : i ∈ A
    · have hbad : ¬ActiveGood K S (exteriorPowerfulPart K S x.1)
          (activeIdeal K S A (fun i => t i)) := by
        intro h
        have hpP : p ∈ exteriorSupport K S (activeIdeal K S A (fun i => t i)) := by
          rw [activeIdeal, exteriorSupport_primeSetIdeal]
          exact Finset.mem_image.mpr ⟨⟨i, hiA⟩, Finset.mem_univ _, hit⟩
        exact h p hpP hpf
      simp [tuplePhysicalRow, hbad]
    · have hbad : ¬InactiveGood K S (exteriorPowerfulPart K S x.1)
          (M \ A) (fun i => t i) := by
        intro h
        exact h ⟨i, Finset.mem_sdiff.mpr ⟨hiM, hiA⟩⟩ (hit.symm ▸ hpf)
      simp [tuplePhysicalRow, hbad]

/-- Identifying the complete fixed-data record is what makes the extracted
physical row independent of the selected and active tuple coordinates. -/
theorem splitFixed_eq_tupleDatum
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (g : PrimeWindowGeometry) (M A : Finset (Fin g.slots)) (hA : A ⊆ M)
    (t : Fin g.slots → ExteriorPrime K S) (ht : Function.Injective t)
    (hQ : ∀ p ∈ M.image t, ¬p.val.asIdeal ∣ x.1.val.val)
    (hb : InactiveGood K S (exteriorPowerfulPart K S x.1) (M \ A) (fun i => t i)) :
    splitFixed K S (actualMarkedDatum K S x (M.image t) hQ)
        ⟨A.image t, Finset.image_subset_image hA⟩ =
      tupleDatum K S (exteriorPowerfulPart K S x.1) (Quotient.out x.2)
        (M \ A) (fun i => t i) hb := by
  apply fixedData_ext K S
    (f := splitFixed K S (actualMarkedDatum K S x (M.image t) hQ)
      ⟨A.image t, Finset.image_subset_image hA⟩)
    (g := tupleDatum K S (exteriorPowerfulPart K S x.1) (Quotient.out x.2)
      (M \ A) (fun i => t i) hb) rfl rfl rfl
  change M.image t \ A.image t = Finset.univ.image (fun i : ↥(M \ A) => t i)
  rw [← Finset.image_sdiff M A ht]
  exact (primeSetIdeal_injective K S (activeIdeal_restrict K S t (M \ A))).symm

theorem tuplePhysicalRow_eq_splitFixed
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (M A : Finset (Fin g.slots)) (hA : A ⊆ M)
    (t : Fin g.slots → ExteriorPrime K S) (ht : Function.Injective t)
    (hQ : ∀ p ∈ M.image t, ¬p.val.asIdeal ∣ x.1.val.val)
    (V : ℝ → ℂ) (Y : ℝ) :
    tuplePhysicalRow K S D x F θ (M \ A) (fun i => t i) V Y
      (activeIdeal K S A (fun i => t i)) =
    fixedPhysicalRow K S D
      (splitFixed K S (actualMarkedDatum K S x (M.image t) hQ)
        ⟨A.image t, Finset.image_subset_image hA⟩) F θ V Y
      (exteriorResidualPart K S x.1) (primeSetIdeal K S (A.image t)) := by
  have hi (i : ↥(M \ A)) : t i ∈ M.image t :=
    Finset.mem_image.mpr ⟨i, (Finset.mem_sdiff.mp i.property).1, rfl⟩
  have hb : InactiveGood K S (exteriorPowerfulPart K S x.1)
      (M \ A) (fun i => t i) := by
    intro i hd
    exact hQ (t i) (hi i) (dvd_trans hd (IdealRows.powerfulPart_dvd x.1.val))
  have hk : InactiveRowGood K S (M \ A) (fun i => t i)
      (exteriorResidualPart K S x.1).val.val := by
    intro i hd
    exact hQ (t i) (hi i) (dvd_trans hd (IdealRows.residualPart_dvd x.1.val))
  have hP : ActiveGood K S (exteriorPowerfulPart K S x.1)
      (activeIdeal K S A (fun i => t i)) := by
    intro p hp hd
    rw [activeIdeal_restrict, subsetPrimeIdeal, exteriorSupport_primeSetIdeal] at hp
    exact hQ p (Finset.image_subset_image hA hp)
      (dvd_trans hd (IdealRows.powerfulPart_dvd x.1.val))
  rw [tuplePhysicalRow, dif_pos hb, if_pos hk, if_pos hP,
    ← splitFixed_eq_tupleDatum K S x g M A hA t ht hQ hb, activeIdeal_restrict]
  rfl

/-- The original theta reflection for one complete window tuple, including
its zero case, is indexed by the actual active slot subsets. -/
theorem completedThetaSum_eq_slotPhysicalRows
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (t : Fin g.slots → ExteriorPrime K S)
    (ht : t ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (M : Finset (Fin g.slots)) (V : SmoothAnnularTest) (Y : ℝ) (hY : 0 < Y) :
    completedThetaSum K S D θ (idealSectorElement K S D x).val
        (primeSetIdeal K S ∅) (M.image t) V.toFun
        (Y * exteriorNorm K S (subsetPrimeIdeal K S t M)) =
      ∑ A ∈ M.powerset,
        (∏ p ∈ M.image t \ A.image t, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
          tuplePhysicalRow K S D x F θ (M \ A) (fun i => t i) V.toFun Y
            (activeIdeal K S A (fun i => t i)) := by
  by_cases hQ : ∀ p ∈ M.image t, ¬p.val.asIdeal ∣ x.1.val.val
  · let d := actualMarkedDatum K S x (M.image t) hQ
    rw [← actualMarkedDatum_rowElement K S D x (M.image t) hQ]
    erw [completedThetaSum_eq_fixedPhysicalRows K S D hD F θ hreflection d V Y hY]
    erw [active_prime_subsets_eq_slot_subsets K S g T Z t ht M]
    apply Finset.sum_congr rfl
    intro A hA
    have hAM := Finset.mem_powerset.mp hA
    erw [dif_pos (Finset.image_subset_image hAM),
      tuplePhysicalRow_eq_splitFixed K S D x F θ g M A hAM t
        (HeckeSkeleton.LowCauchy.lc_injective_of_mem_piFinset ht) hQ V.toFun Y] <;> rfl
  · push_neg at hQ
    obtain ⟨p, hp, hpi⟩ := hQ
    have hz := completedThetaSum_eq_zero_of_mark_overlap K S D θ
      (idealSectorElement K S D x).val (primeSetIdeal K S ∅) (M.image t)
      V.toFun (Y * exteriorNorm K S (subsetPrimeIdeal K S t M)) p hp
    rw [idealSectorOrbit_contraction K S D x] at hz
    rw [hz hpi]
    symm
    apply Finset.sum_eq_zero
    intro A _
    rw [tuplePhysicalRow_zero_of_collision K S D x F θ g M A t V.toFun Y p hp hpi,
      mul_zero]

/-- The target coefficients are kept at Z even when the theta height Y
is the shifted Gaussian annular height. -/
def weightedThetaRow (θ ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots))
    (V : ℝ → ℂ) (Y : ℝ) (x : ExteriorIdeal K S × SixthUnitClasses K S) : ℂ :=
  ∑ t ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    if ∀ i ∈ J, t i = p i then
      (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (t i)) *
        conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S t (Finset.univ \ J)).val) *
        completedThetaSum K S D θ (idealSectorElement K S D x).val
          (primeSetIdeal K S ∅) ((Finset.univ \ J).image t) V
          (Y * exteriorNorm K S (subsetPrimeIdeal K S t (Finset.univ \ J)))
    else 0

theorem weightedThetaRow_eq_activeInactive
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ ψ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (J : Finset (Fin g.slots)) (V : SmoothAnnularTest) (Y : ℝ) (hY : 0 < Y)
    (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    weightedThetaRow K S D θ ψ g T Z p J V.toFun Y x =
      ∑ A ∈ (Finset.univ \ J).powerset,
        ∑ b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A),
          inactiveTwistedWeight K S ψ g Z ((Finset.univ \ J) \ A) b *
            ∑ a ∈ activeTuples K S g T Z A,
              activeWeight K S ψ g Z A a *
                tuplePhysicalRow K S D x F θ ((Finset.univ \ J) \ A) b V.toFun Y
                  (activeIdeal K S A a) := by
  let M := Finset.univ \ J
  let H (A : Finset (Fin g.slots)) (t : Fin g.slots → ExteriorPrime K S) : ℂ :=
    tuplePhysicalRow K S D x F θ (M \ A) (fun i => t i) V.toFun Y
      (activeIdeal K S A (fun i => t i))
  have hlinear :
      weightedThetaRow K S D θ ψ g T Z p J V.toFun Y x =
        ∑ A ∈ M.powerset, ∑ t ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
          if ∀ i ∈ J, t i = p i then
            (∏ i ∈ M, windowWeight K S g Z i (t i)) *
              conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S t M).val) *
              (∏ q ∈ M.image t \ A.image t, (q.val.asIdeal.absNorm : ℂ)⁻¹) *
              H A t else 0 := by
    rw [Finset.sum_comm]
    unfold weightedThetaRow
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hfix : ∀ i ∈ J, t i = p i
    · simp only [if_pos hfix]
      rw [completedThetaSum_eq_slotPhysicalRows K S D hD F θ hreflection x g T Z t ht
        M V Y hY, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      dsimp [H]
      ring
    · simp only [if_neg hfix, Finset.sum_const_zero]
  rw [hlinear]
  apply Finset.sum_congr rfl
  intro A hA
  have hAM := Finset.mem_powerset.mp hA
  rw [target_marked_slot_split K S ψ g T Z p hp J A hAM (H A)]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : (fun i : A => SlotTuples.fill J A p a b i) = a :=
    funext (SlotTuples.fill_active J A hAM p a b)
  have hb' : (fun i : ↥(M \ A) => SlotTuples.fill J A p a b i) = b :=
    funext (SlotTuples.fill_inactive J A p a b)
  simp only [H, ha', hb']

def annularTupleRow (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (F : FiniteMellinData K S) (θ ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (J A : Finset (Fin g.slots))
    (b : ↥((Finset.univ \ J) \ A) → ExteriorPrime K S)
    (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  if hb : InactiveGood K S (exteriorPowerfulPart K S x.1) ((Finset.univ \ J) \ A) b then
    if InactiveRowGood K S ((Finset.univ \ J) \ A) b
        (exteriorResidualPart K S x.1).val.val then
      ∑ j ∈ markDyadIndices K S g T Z A,
        ∑ P ∈ activeIdealDyad K S g T Z A j,
          ordinaryActiveWeight K S (exteriorPowerfulPart K S x.1) ψ g T Z A P.val.val *
            fixedPhysicalRow K S D
              (tupleDatum K S (exteriorPowerfulPart K S x.1) (Quotient.out x.2) _ b hb)
              F θ V Y (exteriorResidualPart K S x.1) P
    else 0
  else 0

/-- The mark-ideal aggregation is injective, and the dyad fibers form an
exact partition of the same finite ideal sum. -/
theorem annularTupleRow_eq_active_sum
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (F : FiniteMellinData K S) (θ ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (J A : Finset (Fin g.slots))
    (b : ↥((Finset.univ \ J) \ A) → ExteriorPrime K S) (V : ℝ → ℂ) (Y : ℝ) :
    annularTupleRow K S D x F θ ψ g T Z J A b V Y =
      ∑ a ∈ activeTuples K S g T Z A, activeWeight K S ψ g Z A a *
        tuplePhysicalRow K S D x F θ ((Finset.univ \ J) \ A) b V Y
          (activeIdeal K S A a) := by
  rw [active_weighted_sum_eq_ideal_sum K S ψ g T Z A]
  by_cases hb : InactiveGood K S (exteriorPowerfulPart K S x.1)
      ((Finset.univ \ J) \ A) b
  · by_cases hk : InactiveRowGood K S ((Finset.univ \ J) \ A) b
        (exteriorResidualPart K S x.1).val.val
    · simp only [annularTupleRow, tuplePhysicalRow, dif_pos hb, if_pos hk]
      rw [show (∑ j ∈ markDyadIndices K S g T Z A,
          ∑ P ∈ activeIdealDyad K S g T Z A j,
            ordinaryActiveWeight K S (exteriorPowerfulPart K S x.1) ψ g T Z A P.val.val *
              fixedPhysicalRow K S D
                (tupleDatum K S (exteriorPowerfulPart K S x.1) (Quotient.out x.2) _ b hb)
                F θ V Y (exteriorResidualPart K S x.1) P) =
          ∑ P ∈ activeIdeals K S g T Z A,
            ordinaryActiveWeight K S (exteriorPowerfulPart K S x.1) ψ g T Z A P.val.val *
              fixedPhysicalRow K S D
                (tupleDatum K S (exteriorPowerfulPart K S x.1) (Quotient.out x.2) _ b hb)
                F θ V Y (exteriorResidualPart K S x.1) P from
        Finset.sum_fiberwise_of_maps_to
          (fun P hP => Finset.mem_image.mpr ⟨P, hP, rfl⟩) _]
      apply Finset.sum_congr rfl
      intro P _
      rw [ordinaryActiveWeight_exterior]
      split_ifs <;> simp
    · simp [annularTupleRow, tuplePhysicalRow, hb, hk]
  · simp [annularTupleRow, tuplePhysicalRow, hb]

theorem weightedThetaRow_eq_annularTuples
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ ψ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (J : Finset (Fin g.slots)) (V : SmoothAnnularTest) (Y : ℝ) (hY : 0 < Y)
    (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    weightedThetaRow K S D θ ψ g T Z p J V.toFun Y x =
      ∑ A ∈ (Finset.univ \ J).powerset,
        ∑ b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A),
          inactiveTwistedWeight K S ψ g Z ((Finset.univ \ J) \ A) b *
            annularTupleRow K S D x F θ ψ g T Z J A b V.toFun Y := by
  rw [weightedThetaRow_eq_activeInactive K S D hD F θ ψ hreflection g T Z p hp J V Y hY x]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro b _
  rw [annularTupleRow_eq_active_sum]

/-- Summability and the exact Gaussian identity are obtained from the
derived frozen-row reconstruction for each actual active-ideal dyad. -/
theorem annularTupleRow_reconstruction [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ ψ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z Klo q Ccut : ℝ) (hZ : 1 < Z) (hK : 1 ≤ Klo) (hq : 0 < q) (hCut : 0 < Ccut)
    (x : ExteriorIdeal K S × SixthUnitClasses K S)
    (J A : Finset (Fin g.slots)) (hA : A ⊆ Finset.univ \ J)
    (b : ↥((Finset.univ \ J) \ A) → ExteriorPrime K S)
    (hb : b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A))
    (hselected : Z ^ ((J.card : ℝ) / (6 * g.slots)) ≤ q)
    (hrow : exteriorNorm K S (exteriorPowerfulPart K S x.1) * Klo ≤
      Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2)
    (hkr : Klo ≤ exteriorNorm K S (exteriorResidualPart K S x.1) ∧
      exteriorNorm K S (exteriorResidualPart K S x.1) ≤ 2 * Klo) :
    Summable (fun shift : ℤ => annularTupleRow K S D x F θ ψ g T Z J A b
      (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ))) ∧
    frozenTupleRow K S D (exteriorPowerfulPart K S x.1) (Quotient.out x.2)
      F θ ψ g T Z J A b (exteriorResidualPart K S x.1).val.val =
      ∑' shift : ℤ, annularTupleRow K S D x F θ ψ g T Z J A b
        (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ)) := by
  by_cases hgood : InactiveGood K S (exteriorPowerfulPart K S x.1)
      ((Finset.univ \ J) \ A) b
  · by_cases hk : InactiveRowGood K S ((Finset.univ \ J) \ A) b
        (exteriorResidualPart K S x.1).val.val
    · let f := tupleDatum K S (exteriorPowerfulPart K S x.1) (Quotient.out x.2)
        ((Finset.univ \ J) \ A) b hgood
      let a := ordinaryActiveWeight K S (exteriorPowerfulPart K S x.1) ψ g T Z A
      let H (j : ℕ) (shift : ℤ) : ℂ :=
        ∑ P ∈ activeIdealDyad K S g T Z A j, a P.val.val *
          fixedPhysicalRow K S D f F θ (GaussianTheta.annulusTest shift).toFun
            (Z * Real.exp (shift : ℝ)) (exteriorResidualPart K S x.1) P
      have hr (j : ℕ) (hj : j ∈ markDyadIndices K S g T Z A) :
          Summable (H j) ∧
          frozenReflectedRow K S D f F θ a Z (ordinaryMarkDyad K S g T Z A j)
            (exteriorResidualPart K S x.1).val.val = ∑' shift : ℤ, H j shift := by
        obtain ⟨P, hP, hPj⟩ := markDyadIndices_nonempty K S g T Z A hj
        have hwindow := inactive_times_mark_lower_le K S g T hZ.le J A hA b hb P hP
          ((2 : ℝ) ^ j)
          (activeIdealDyad_support K S g T (zero_lt_one.trans hZ) A j hPj).2.1
        have hd := selected_exponent_bounds g J
        apply actual_frozen_row_reconstruction K S D F hF θ hKernel hθ hD hquadratic hcubic
          hreflection f Z Klo ((2 : ℝ) ^ j) q ((J.card : ℝ) / (6 * g.slots))
          Ccut ((2 : ℝ) ^ g.slots) hZ hK (one_le_pow₀ (by norm_num)) hq hCut
          (by positivity) hd.1 hd.2 (IdealRows.powerfulPart_powerful x.1.val) rfl
          hselected hrow hwindow (activeIdealDyad K S g T Z A j) ?_
          (exteriorResidualPart K S x.1) (tupleDatum_row_admissible K S x _ b hgood hk)
          hkr a
        · intro Q hQ
          have hs := activeIdealDyad_support K S g T (zero_lt_one.trans hZ) A j hQ
          exact ⟨hs.1, hs.2.1, hs.2.2.le⟩
        · intro Q hQ ha
          exact ordinaryActiveWeight_admissible K S _ _ ψ g T Z J A hA b hb hgood Q
            (Finset.mem_filter.mp hQ).1 ha
      have hs : Summable (fun shift : ℤ => ∑ j ∈ markDyadIndices K S g T Z A, H j shift) :=
        summable_sum (fun j hj => (hr j hj).1)
      refine ⟨?_, ?_⟩
      · simpa only [annularTupleRow, dif_pos hgood, if_pos hk, H, a, f] using hs
      · simp only [frozenTupleRow, annularTupleRow, dif_pos hgood, if_pos hk]
        rw [Summable.tsum_finsetSum (fun j hj => (hr j hj).1)]
        apply Finset.sum_congr rfl
        intro j hj
        exact (hr j hj).2
    · simp only [frozenTupleRow, annularTupleRow, dif_pos hgood, if_neg hk, tsum_zero]
      exact ⟨summable_zero, rfl⟩
  · simp only [frozenTupleRow, annularTupleRow, dif_neg hgood, tsum_zero]
    exact ⟨summable_zero, rfl⟩

/-- All original finite tuple sums may now be interchanged with the
Gaussian series.  The supporting convergence is a conclusion of the
actual two-sieve argument in the preceding theorem. -/
theorem weightedThetaRow_gaussian_reconstruction [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ ψ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z Klo q Ccut : ℝ) (hZ : 1 < Z) (hK : 1 ≤ Klo) (hq : 0 < q) (hCut : 0 < Ccut)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (x : ExteriorIdeal K S × SixthUnitClasses K S) (J : Finset (Fin g.slots))
    (hselected : Z ^ ((J.card : ℝ) / (6 * g.slots)) ≤ q)
    (hrow : exteriorNorm K S (exteriorPowerfulPart K S x.1) * Klo ≤
      Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2)
    (hkr : Klo ≤ exteriorNorm K S (exteriorResidualPart K S x.1) ∧
      exteriorNorm K S (exteriorResidualPart K S x.1) ≤ 2 * Klo) :
    markedFrozenRow K S D (exteriorPowerfulPart K S x.1) (Quotient.out x.2)
      F θ ψ g T Z J (exteriorResidualPart K S x.1).val.val =
      ∑' shift : ℤ, weightedThetaRow K S D θ ψ g T Z p J
        (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ)) x := by
  let H (A : Finset (Fin g.slots)) (b : ↥((Finset.univ \ J) \ A) → ExteriorPrime K S)
      (shift : ℤ) : ℂ :=
    annularTupleRow K S D x F θ ψ g T Z J A b
      (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ))
  have hr (A : Finset (Fin g.slots)) (hA : A ∈ (Finset.univ \ J).powerset)
      (b : ↥((Finset.univ \ J) \ A) → ExteriorPrime K S)
      (hb : b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A)) :
      Summable (H A b) ∧
        frozenTupleRow K S D (exteriorPowerfulPart K S x.1) (Quotient.out x.2)
          F θ ψ g T Z J A b (exteriorResidualPart K S x.1).val.val =
            ∑' shift : ℤ, H A b shift :=
    annularTupleRow_reconstruction K S D F hF θ ψ hKernel hθ hD hquadratic hcubic hreflection
      g T Z Klo q Ccut hZ hK hq hCut x J A (Finset.mem_powerset.mp hA) b hb hselected hrow hkr
  have hs (A : Finset (Fin g.slots)) (hA : A ∈ (Finset.univ \ J).powerset) :
      Summable (fun shift : ℤ =>
        ∑ b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A),
          inactiveTwistedWeight K S ψ g Z ((Finset.univ \ J) \ A) b * H A b shift) :=
    summable_sum (fun b hb => ((hr A hA b hb).1).mul_left _)
  have hlinear (shift : ℤ) :
      weightedThetaRow K S D θ ψ g T Z p J
        (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ)) x =
      ∑ A ∈ (Finset.univ \ J).powerset,
        ∑ b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A),
          inactiveTwistedWeight K S ψ g Z ((Finset.univ \ J) \ A) b * H A b shift :=
    weightedThetaRow_eq_annularTuples K S D hD F θ ψ hreflection g T Z p hp J
      (GaussianTheta.annulusTest shift) (Z * Real.exp (shift : ℝ))
      (mul_pos (zero_lt_one.trans hZ) (Real.exp_pos _)) x
  simp_rw [hlinear]
  rw [Summable.tsum_finsetSum hs]
  unfold markedFrozenRow
  apply Finset.sum_congr rfl
  intro A hA
  rw [Summable.tsum_finsetSum (fun b hb => ((hr A hA b hb).1).mul_left _)]
  unfold activeSubsetRow
  apply Finset.sum_congr rfl
  intro b hb
  rw [tsum_mul_left, (hr A hA b hb).2]

#print axioms completedThetaSum_eq_slotPhysicalRows
#print axioms weightedThetaRow_eq_annularTuples
#print axioms annularTupleRow_reconstruction
#print axioms weightedThetaRow_gaussian_reconstruction

section Target

variable (c : HeckeSkeleton.TargetContext K)
local notation "Sc" => HeckeSkeleton.places K c
local notation "Pc" => HeckeSkeleton.probeData K c
local notation "ψc" => HeckeSkeleton.targetCharacter K c
local notation "θc" => thetaPeriod K Sc Pc ψc
local notation "gc" => c.geometry
local notation "Tc" => HeckeSkeleton.rayFilter K c

theorem target_annularMarkedRow_eq_weightedThetaRow
    (Z : ℝ) (p : Fin (gc).slots → ExteriorPrime K Sc)
    (J : Finset (Fin (gc).slots)) (shift : ℤ)
    (x : ExteriorIdeal K Sc × SixthUnitClasses K Sc) :
    TargetGaussian.annularMarkedRow K c Z p J shift
        (idealSectorElement K Sc (Pc).arithmetic x).val =
      weightedThetaRow K Sc (Pc).arithmetic θc ψc gc Tc Z p J
        (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ)) x := by
  unfold TargetGaussian.annularMarkedRow weightedThetaRow
  apply Finset.sum_congr rfl
  intro t _
  have hscale : Z * exteriorNorm K Sc (subsetPrimeIdeal K Sc t (Finset.univ \ J)) *
      Real.exp (shift : ℝ) =
      (Z * Real.exp (shift : ℝ)) *
        exteriorNorm K Sc (subsetPrimeIdeal K Sc t (Finset.univ \ J)) := by ring
  simp only [TargetGaussian.markWeight, TargetGaussian.thetaScale, ite_mul, zero_mul, hscale]

/-- Literal endpoint for the original repository target.  Its only
row-specific bound is the target's own complete-ideal cutoff.  The
auxiliary moving-row interval is chosen from the actual residual norm. -/
theorem completedMarkedRow_eq_markedFrozenRow [Finite (SixthLocalClasses K Sc)]
    (F : FiniteMellinData K Sc) (hF : FiniteMellinAdmissible K Sc F)
    (hKernel : MellinKernelInput K Sc F θc)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sc → UnramifiedAt K θc p)
    (hD : AllowedGeneratorInput K Sc (Pc).arithmetic)
    (hquadratic : ExteriorQuadraticBound K Sc (Pc).arithmetic)
    (hcubic : ExteriorCubicBound K Sc (Pc).arithmetic)
    (hreflection : MarkedCoefficientReflectionInput K Sc (Pc).arithmetic F θc)
    (Z Ccut : ℝ) (hZ : 1 < Z) (hCut : 0 < Ccut)
    (p : Fin (gc).slots → ExteriorPrime K Sc)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K Sc gc Tc Z i))
    (J : Finset (Fin (gc).slots))
    (x : ExteriorIdeal K Sc × SixthUnitClasses K Sc)
    (hcut : exteriorNorm K Sc x.1 ≤
      Ccut * Z ^ (5 / 6 : ℝ) / exteriorNorm K Sc (subsetPrimeIdeal K Sc p J) ^ 2) :
    HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J
        (idealSectorElement K Sc (Pc).arithmetic x) =
      markedFrozenRow K Sc (Pc).arithmetic (exteriorPowerfulPart K Sc x.1)
        (Quotient.out x.2) F θc ψc gc Tc Z J (exteriorResidualPart K Sc x.1).val.val := by
  let Klo := exteriorNorm K Sc (exteriorResidualPart K Sc x.1)
  let q := exteriorNorm K Sc (subsetPrimeIdeal K Sc p J)
  have hK : 1 ≤ Klo := ActualAnnularBlockEnergy.exteriorNorm_one_le K Sc _
  have hN : exteriorNorm K Sc x.1 =
      exteriorNorm K Sc (exteriorPowerfulPart K Sc x.1) * Klo :=
    IdealRows.norm_powerful_residual_decomposition x.1.val
  have hrow : exteriorNorm K Sc (exteriorPowerfulPart K Sc x.1) * Klo ≤
      Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2 := by
    rw [← hN]
    exact hcut
  have hkr : Klo ≤ exteriorNorm K Sc (exteriorResidualPart K Sc x.1) ∧
      exteriorNorm K Sc (exteriorResidualPart K Sc x.1) ≤ 2 * Klo :=
    ⟨le_rfl, by dsimp [Klo]; nlinarith [exteriorNorm_pos K Sc (exteriorResidualPart K Sc x.1)]⟩
  have hrec := weightedThetaRow_gaussian_reconstruction K Sc (Pc).arithmetic F hF θc ψc
    hKernel hθ hD hquadratic hcubic hreflection gc Tc Z Klo q Ccut hZ hK
    (exteriorNorm_pos K Sc _) hCut p hp x J
    (selected_norm_bounds K Sc gc Tc (zero_lt_one.trans hZ) p hp J).1 hrow hkr
  rw [TargetGaussian.completedMarkedRow_gaussian_annuli K c (zero_lt_one.trans hZ)]
  rw [hrec]
  apply tsum_congr
  intro shift
  exact target_annularMarkedRow_eq_weightedThetaRow K c Z p J shift x

#print axioms completedMarkedRow_eq_markedFrozenRow

/-- The public target identity uses only the supplied coefficient reflection
and the two actual sieves. Every kernel, unramifiedness, and admissibility
fact above is extracted from that original reflection input. -/
theorem completedMarkedRow_reflection_identity [Finite (SixthLocalClasses K Sc)]
    (F : FiniteMellinData K Sc)
    (hreflection : MarkedCoefficientReflectionInput K Sc (Pc).arithmetic F θc)
    (hquadratic : ExteriorQuadraticBound K Sc (Pc).arithmetic)
    (hcubic : ExteriorCubicBound K Sc (Pc).arithmetic)
    (Z Ccut : ℝ) (hZ : 1 < Z) (hCut : 0 < Ccut)
    (p : Fin (gc).slots → ExteriorPrime K Sc)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K Sc gc Tc Z i))
    (J : Finset (Fin (gc).slots))
    (x : ExteriorIdeal K Sc × SixthUnitClasses K Sc)
    (hcut : exteriorNorm K Sc x.1 ≤
      Ccut * Z ^ (5 / 6 : ℝ) / exteriorNorm K Sc (subsetPrimeIdeal K Sc p J) ^ 2) :
    HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J
        (idealSectorElement K Sc (Pc).arithmetic x) =
      markedFrozenRow K Sc (Pc).arithmetic (exteriorPowerfulPart K Sc x.1)
        (Quotient.out x.2) F θc ψc gc Tc Z J (exteriorResidualPart K Sc x.1).val.val :=
  completedMarkedRow_eq_markedFrozenRow K c F hreflection.kernel.finite_admissible
    hreflection.kernel hreflection.exterior_unramified hreflection.allowed_generators
    hquadratic hcubic hreflection Z Ccut hZ hCut p hp J x hcut

#print axioms completedMarkedRow_reflection_identity

end Target

end HeckeSkeleton.LowEnergy.ActualTupleReconstruction
