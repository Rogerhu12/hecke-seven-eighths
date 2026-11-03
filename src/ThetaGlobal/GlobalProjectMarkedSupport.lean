import ThetaGlobal.GlobalProjectLocalSupport
import ThetaGlobal.GlobalActualCoordinates
import ThetaGlobal.GlobalSupportRow

/-!
# The actual marked digit row covers the literal reflected frequencies

The auxiliary row has precisely the union of the moving, frozen,
punctured and marked places. Its digit tags are independent of the
auxiliary row's squarefree exponents. Nonvanishing of the actual finite
digit average implies the local valuation restrictions needed by the
proved construction of `ReflectionIndex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectMarkedSupport

open NumberField IsDedekindDomain DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectLocalDigitTables ThetaGlobal.GlobalProjectLocalSupport
open scoped NumberField Classical BigOperators nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

variable (Adata : ThetaArithmeticData F ((R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))) (d : MarkedDatum F ((R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))))

def support : Finset P :=
  exteriorSupport F Sf d.moving ∪ (frozenPrimes F Sf d ∪ d.marks)

def row : ThetaReflectionData.Row R.A :=
  GlobalSupportRow.row R.A R.probe.allowed (support R d)

def digitAt (p : P) : Fin 6 :=
  if p ∈ exteriorSupport F Sf d.moving then ⟨1, by decide⟩ else
    if p ∈ frozenPrimes F Sf d then rowDigit F Sf d p else 0

def markAt (p : P) : Bool := decide (p ∈ d.marks)

def digits (p : GlobalProjectWeightedDigits.Places R (row R d)) : Fin 6 :=
  digitAt R d (exteriorRowPrime R (row R d) p)

def marks (p : GlobalProjectWeightedDigits.Places R (row R d)) : Bool :=
  markAt R d (exteriorRowPrime R (row R d) p)

def weight : GlobalProjectWeightedDigits.Digits R (row R d) → ℂ :=
  GlobalProjectLiteralDigitWeights.tensorWeight R Adata (row R d) (digits R d) (marks R d)

theorem weight_reindexInvariant :
    GlobalProjectWeightedDigits.ReindexInvariant R (row R d) (weight R Adata d) :=
  GlobalProjectLiteralDigitWeights.tensorWeight_reindexInvariant
    R Adata (row R d) (digits R d) (marks R d)

theorem exteriorRows_eq : exteriorRows R (row R d) = support R d :=
  GlobalSupportRow.exteriorRows_eq R (support R d)

theorem support_dvd (I : ExteriorIdeal F Sf) (p : P)
    (hp : p ∈ exteriorSupport F Sf I) : p.val.asIdeal ∣ I.val.val :=
  (mem_idealPrimeSupport_iff F I.val p.val).mp
    (Finsupp.mem_support_iff.mpr ((GlobalIndexSupport.mem_exteriorSupport F Sf I p).mp hp))

theorem moving_disjoint_frozen :
    Disjoint (exteriorSupport F Sf d.moving) (frozenPrimes F Sf d) := by
  apply Finset.disjoint_left.mpr
  intro p hm hf
  have he : primeExponents d.moving.val p.val ≠ 0 :=
    (GlobalIndexSupport.mem_exteriorSupport F Sf d.moving p).mp hm
  rcases Finset.mem_union.mp hf with hf | hf
  · exact he (GlobalIndexSupport.exponent_zero_of_coprime F Sf d.moving d.frozen
      d.moving_frozen_coprime p (support_dvd R d.frozen p hf))
  · exact he (GlobalIndexSupport.exponent_zero_of_coprime F Sf d.moving d.puncture
      d.moving_puncture_coprime p (support_dvd R d.puncture p hf))

theorem moving_disjoint_marks :
    Disjoint (exteriorSupport F Sf d.moving) d.marks := by
  apply Finset.disjoint_left.mpr
  intro p hm hp
  exact (d.marks_coprime p hp).1 (support_dvd R d.moving p hm)

theorem moving_exponent (p : P) :
    primeExponents d.moving.val p.val =
      if p ∈ exteriorSupport F Sf d.moving then 1 else 0 := by
  have hle : primeExponents d.moving.val p.val ≤ 1 :=
    Multiset.nodup_iff_count_le_one.mp
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
        (nonZeroDivisors.coe_ne_zero d.moving.val)).mp d.moving_squarefree) p.val.asIdeal
  by_cases hp : p ∈ exteriorSupport F Sf d.moving
  · rw [if_pos hp]
    have hn := (GlobalIndexSupport.mem_exteriorSupport F Sf d.moving p).mp hp
    omega
  · rw [if_neg hp]
    exact not_ne_iff.mp (fun h => hp ((GlobalIndexSupport.mem_exteriorSupport F Sf d.moving p).mpr h))

theorem digitAt_optional (p : P)
    (hm : p ∉ exteriorSupport F Sf d.moving)
    (hp : p ∉ GlobalIndexSupport.mandatory F Sf d) : digitAt R d p = 0 := by
  rw [digitAt, if_neg hm]
  by_cases hf : p ∈ frozenPrimes F Sf d
  · rw [if_pos hf]
    apply Fin.ext
    by_contra hj
    exact hp ⟨hf, hj⟩
  · exact if_neg hf

variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T) (H : Input R D Adata)
  (E : ExteriorCoefficients R Q T D)

include H in
theorem at_support_nonzero (x : Fˣ)
    (hx : GlobalProjectSignedExtraction.reverseCoefficient R D (row R d)
      (weight R Adata d) x ≠ 0) (p : P) (hp : p ∈ support R d) :
    localValue R Adata p (digitAt R d p) (markAt R d p) x ≠ 0 := by
  let q : RowPrime R (row R d) := ⟨p.val,
    (GlobalSupportRow.mem_rowPrimes R.A R.probe.allowed (support R d) p).mpr hp⟩
  have h := row_nonzero R Adata D H (row R d) (digits R d) (marks R d) x hx q
  have hq : exteriorRowPrime R (row R d) q = p := Subtype.ext rfl
  simpa only [digits, marks, hq] using h

include H E in
theorem outside_nonzero (x : Fˣ)
    (hx : GlobalProjectSignedExtraction.reverseCoefficient R D (row R d)
      (weight R Adata d) x ≠ 0) (p : P) (hp : p ∉ support R d) :
    sphericalValue R Adata p x ≠ 0 :=
  off_row_nonzero R Adata D H E (row R d) (digits R d) (marks R d) x hx p
    (by rwa [exteriorRows_eq])

include H in
theorem moving_order (x : Fˣ)
    (hx : GlobalProjectSignedExtraction.reverseCoefficient R D (row R d)
      (weight R Adata d) x ≠ 0) (p : P)
    (hp : p ∈ exteriorSupport F Sf d.moving) : ThetaBranch.order p.val x = -2 := by
  have hn : p ∉ d.marks :=
    fun h => (Finset.disjoint_left.mp (moving_disjoint_marks R d)) hp h
  apply localValue_moving R Adata p x
  simpa [digitAt, hp, markAt, hn] using
    at_support_nonzero R Adata d D H x hx p (Finset.mem_union_left _ hp)

include H E in
/-- The actual local tables supply every hypothesis of ideal-coordinate
reconstruction. The fixed moving denominator is removed explicitly. -/
theorem localSupport (x : Fˣ)
    (hx : GlobalProjectSignedExtraction.reverseCoefficient R D (row R d)
      (weight R Adata d) x ≠ 0) :
    GlobalFrequencyReconstruction.LocalSupport (GlobalIndexSupport.mandatory F Sf d)
      (GlobalActualCoordinates.allowed R.A d)
      (fun p => ThetaBranch.order p.val x + 2 * (primeExponents d.moving.val p.val : ℤ)) := by
  let v : P → ℤ := fun p => ThetaBranch.order p.val x +
    2 * (primeExponents d.moving.val p.val : ℤ)
  have hmove (p : P) (hp : p ∈ exteriorSupport F Sf d.moving) : v p = 0 := by
    simp only [v]
    rw [moving_order R Adata d D H x hx p hp, moving_exponent, if_pos hp]
    norm_num
  have hnonmove (p : P) (hp : p ∉ exteriorSupport F Sf d.moving) :
      v p = ThetaBranch.order p.val x := by
    simp only [v]
    rw [moving_exponent, if_neg hp]
    simp
  change GlobalFrequencyReconstruction.LocalSupport (GlobalIndexSupport.mandatory F Sf d)
    (GlobalActualCoordinates.allowed R.A d) v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact Finset.mem_union_left _ hp.1
  · intro p hv
    by_contra hp
    have hm : p ∉ exteriorSupport F Sf d.moving := by
      intro hm
      rw [hmove p hm] at hv
      omega
    have ho : p ∉ support R d := by
      intro h
      rcases Finset.mem_union.mp h with hm' | ha
      · exact hm hm'
      · exact hp ha
    have hn := (spherical_nonzero R Adata p x
      (outside_nonzero R Adata d D H E x hx p ho)).1
    rw [hnonmove p hm] at hv
    omega
  · intro p
    by_cases hm : p ∈ exteriorSupport F Sf d.moving
    · rw [hmove p hm]
      omega
    · rw [hnonmove p hm]
      by_cases hp : p ∈ support R d
      · exact localValue_nonzero_lower R Adata p _ _ x
          (at_support_nonzero R Adata d D H x hx p hp)
      · exact (by have := (spherical_nonzero R Adata p x
            (outside_nonzero R Adata d D H E x hx p hp)).1; omega)
  · intro p hp
    have hm : p ∉ exteriorSupport F Sf d.moving :=
      fun h => (Finset.disjoint_left.mp (moving_disjoint_frozen R d)) h hp.1
    have hmark : p ∉ d.marks := fun h =>
      (Finset.disjoint_left.mp (GlobalIndexSupport.marks_disjoint_frozen F Sf d)) h hp.1
    rw [hnonmove p hm]
    apply localValue_nonzero_mandatory_digits R Adata p (rowDigit F Sf d p) hp.2 x
    simpa [digitAt, hm, hp.1, markAt, hmark] using
      at_support_nonzero R Adata d D H x hx p
        (Finset.mem_union_right _ (Finset.mem_union_left _ hp.1))
  · intro p hp hv
    have hm : p ∉ exteriorSupport F Sf d.moving := by
      intro hm
      rw [hmove p hm] at hv
      omega
    rw [hnonmove p hm] at hv ⊢
    by_cases hs : p ∈ support R d
    · apply localValue_optional_negative R Adata p (markAt R d p) x _ hv
      simpa only [digitAt_optional R d p hm hp] using
        at_support_nonzero R Adata d D H x hx p hs
    · have hn := (spherical_nonzero R Adata p x
        (outside_nonzero R Adata d D H E x hx p hs)).1
      omega
  · intro p hp hv
    by_cases hm : p ∈ exteriorSupport F Sf d.moving
    · rw [hmove p hm]
      decide
    · rw [hnonmove p hm] at hv ⊢
      by_cases hs : p ∈ support R d
      · apply localValue_optional_nonnegative R Adata p (markAt R d p) x _ hv
        simpa only [digitAt_optional R d p hm hp] using
          at_support_nonzero R Adata d D H x hx p hs
      · exact (spherical_nonzero R Adata p x
          (outside_nonzero R Adata d D H E x hx p hs)).2

include H E in
theorem exists_index (x : Fˣ)
    (hx : GlobalProjectSignedExtraction.reverseCoefficient R D (row R d)
      (weight R Adata d) x ≠ 0) :
    ∃ i : ReflectionIndex F Sf d,
      GlobalFrequency.Supported (GlobalIndexSupport.mandatory F Sf d)
        (GlobalIndexSupport.branch F Sf d i) ∧
      GlobalActualReindex.frequency R.A Adata d i = QuotientGroup.mk x :=
  GlobalActualCoordinates.exists_index_with_frequency R.A d Adata x
    (localSupport R Adata d D H E x hx)

end ThetaGlobal.GlobalProjectMarkedSupport
