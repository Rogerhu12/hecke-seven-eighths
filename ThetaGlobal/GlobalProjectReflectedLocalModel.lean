import ThetaGlobal.GlobalProjectLocalPhases
import ThetaGlobal.GlobalProjectArithmeticProduct

/-!
# Local normal form of a supported reflected frequency

At a supported coordinate the moving, active frozen and active marked
places are disjoint from the squarefree and cube coordinates. All other
places contribute the spherical squarefree/cube factor. These statements
use the actual field representative and its proved exterior orders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace ThetaGlobal.GlobalProjectReflectedLocalModel

open NumberField IsDedekindDomain DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectLocalDigitTables ThetaGlobal.GlobalProjectLocalSupport
open ThetaGlobal.GlobalProjectLocalPhases
open scoped NumberField Classical BigOperators nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

variable (Adata : ThetaArithmeticData F ((R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))) (d : MarkedDatum F ((R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))))
  (i : ReflectionIndex F ((R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))) d)

structure Admissible : Prop where
  supported : GlobalFrequency.Supported (GlobalIndexSupport.mandatory F Sf d)
    (GlobalIndexSupport.branch F Sf d i)
  moving_c : ∀ p ∈ exteriorSupport F Sf d.moving, primeExponents i.c.val p.val = 0
  moving_n : ∀ p ∈ exteriorSupport F Sf d.moving, primeExponents i.n.val p.val = 0

theorem admissible_of_nonzero (θ : HeckeCharacter F)
    (hi : ReflectedArithmetic.reflectedCoefficient F Sf Adata d i θ ≠ 0) :
    Admissible R d i := by
  refine ⟨GlobalIndexSupport.supported F Sf Adata d i θ hi, ?_, ?_⟩
  · intro p hp
    by_contra hn
    have hz := GlobalIndexSupport.idealSymbol_generator_zero F Sf Adata d.moving i.c p
      (GlobalProjectMarkedSupport.support_dvd R d.moving p hp)
      ((mem_idealPrimeSupport_iff F i.c.val p.val).mp (Finsupp.mem_support_iff.mpr hn))
    apply hi
    simp [ReflectedArithmetic.reflectedCoefficient,
      GlobalProjectPhases.idealSymbol_mul, hz]
  · intro p hp
    by_contra hn
    have hz := GlobalIndexSupport.idealSymbol_generator_zero F Sf Adata d.moving i.n p
      (GlobalProjectMarkedSupport.support_dvd R d.moving p hp)
      ((mem_idealPrimeSupport_iff F i.n.val p.val).mp (Finsupp.mem_support_iff.mpr hn))
    apply hi
    simp [ReflectedArithmetic.reflectedCoefficient,
      GlobalProjectPhases.idealSymbol_mul, hz]

variable (hi : Admissible R d i)

def x : Fˣ := GlobalActualFrequency.representative F Sf Adata d i

theorem marks_frozen_disjoint : Disjoint i.activeMarks i.activeFrozen :=
  (GlobalIndexSupport.marks_disjoint_frozen F Sf d).mono i.marks_subset i.frozen_subset

theorem moving_active_disjoint :
    Disjoint (exteriorSupport F Sf d.moving) (i.activeFrozen ∪ i.activeMarks) := by
  apply Finset.disjoint_left.mpr
  intro p hm ha
  rcases Finset.mem_union.mp ha with hf | hp
  · exact (Finset.disjoint_left.mp (GlobalProjectMarkedSupport.moving_disjoint_frozen R d))
      hm (i.frozen_subset hf)
  · exact (Finset.disjoint_left.mp (GlobalProjectMarkedSupport.moving_disjoint_marks R d))
      hm (i.marks_subset hp)

include hi in
theorem active_c (p : P) (hp : p ∈ i.activeFrozen ∪ i.activeMarks) :
    primeExponents i.c.val p.val = 0 := hi.supported.c_active p hp

include hi in
theorem active_n (p : P) (hp : p ∈ i.activeFrozen ∪ i.activeMarks) :
    primeExponents i.n.val p.val = 0 := hi.supported.n_active p hp

theorem outside_a (p : P) (hp : p ∉ i.activeFrozen) :
    primeExponents i.numeratorFrozen.val p.val = 0 := by
  by_contra hn
  exact hp (i.frozen_support
    ((GlobalIndexSupport.mem_exteriorSupport F Sf i.numeratorFrozen p).mpr hn))

include hi in
theorem moving_order (p : P) (hp : p ∈ exteriorSupport F Sf d.moving) :
    ThetaBranch.order p.val (x R Adata d i) = -2 := by
  have ha : p ∉ i.activeFrozen ∪ i.activeMarks :=
    fun h => (Finset.disjoint_left.mp (moving_active_disjoint R d i)) hp h
  have hfa : p ∉ i.activeFrozen := fun h => ha (Finset.mem_union_left _ h)
  rw [x, GlobalActualReindex.order_representative R.A Adata d i p]
  simp only [GlobalFrequency.valuation, GlobalIndexSupport.branch, Finset.mem_coe,
    outside_a R d i p hfa, hi.moving_c p hp, hi.moving_n p hp,
    GlobalProjectMarkedSupport.moving_exponent R d p, if_pos hp,
    if_neg ha, Nat.cast_zero, Nat.cast_one]
  norm_num

include hi in
theorem frozen_order (p : P) (hp : p ∈ i.activeFrozen) :
    ThetaBranch.order p.val (x R Adata d i) =
      (primeExponents i.numeratorFrozen.val p.val : ℤ) - 2 := by
  have ha : p ∈ i.activeFrozen ∪ i.activeMarks := Finset.mem_union_left _ hp
  have hm : p ∉ exteriorSupport F Sf d.moving :=
    fun h => (Finset.disjoint_left.mp (moving_active_disjoint R d i)) h ha
  rw [x, GlobalActualReindex.order_representative R.A Adata d i p]
  simp only [GlobalFrequency.valuation, GlobalIndexSupport.branch, Finset.mem_coe,
    active_c R d i hi p ha, active_n R d i hi p ha,
    GlobalProjectMarkedSupport.moving_exponent R d p, if_neg hm,
    if_pos ha, Nat.cast_zero, add_zero, mul_zero, sub_zero]

include hi in
theorem marked_order (p : P) (hp : p ∈ i.activeMarks) :
    ThetaBranch.order p.val (x R Adata d i) = -2 := by
  have hf : p ∉ i.activeFrozen :=
    fun h => (Finset.disjoint_left.mp (marks_frozen_disjoint R d i)) hp h
  have ha : p ∈ i.activeFrozen ∪ i.activeMarks := Finset.mem_union_right _ hp
  have hm : p ∉ exteriorSupport F Sf d.moving :=
    fun h => (Finset.disjoint_left.mp (moving_active_disjoint R d i)) h ha
  rw [x, GlobalActualReindex.order_representative R.A Adata d i p]
  simp only [GlobalFrequency.valuation, GlobalIndexSupport.branch, Finset.mem_coe,
    outside_a R d i p hf, active_c R d i hi p ha, active_n R d i hi p ha,
    GlobalProjectMarkedSupport.moving_exponent R d p, if_neg hm,
    if_pos ha, Nat.cast_zero]
  norm_num

theorem outside_order (p : P) (hm : p ∉ exteriorSupport F Sf d.moving)
    (ha : p ∉ i.activeFrozen ∪ i.activeMarks) :
    ThetaBranch.order p.val (x R Adata d i) =
      (primeExponents i.c.val p.val : ℤ) + 3 * (primeExponents i.n.val p.val : ℤ) := by
  have hf : p ∉ i.activeFrozen := fun h => ha (Finset.mem_union_left _ h)
  rw [x, GlobalActualReindex.order_representative R.A Adata d i p]
  simp only [GlobalFrequency.valuation, GlobalIndexSupport.branch, Finset.mem_coe,
    outside_a R d i p hf, GlobalProjectMarkedSupport.moving_exponent R d p,
    if_neg hm, if_neg ha, Nat.cast_zero, zero_add, sub_zero, mul_zero]

include hi in
theorem optional_frozen_a (p : P) (hp : p ∈ i.activeFrozen)
    (hj : (rowDigit F Sf d p).val = 0) : primeExponents i.numeratorFrozen.val p.val = 0 := by
  exact hi.supported.optional_zero p (Finset.mem_union_left _ hp)
    (fun h => h.2 hj)

theorem inactive_frozen_digit (p : P) (hp : p ∈ frozenPrimes F Sf d)
    (ha : p ∉ i.activeFrozen) : rowDigit F Sf d p = 0 := by
  apply Fin.ext
  by_contra hj
  exact ha (i.nonzero_active p hp hj)

theorem spherical_order (p : P) (a : Fˣ) (c n : ℕ) (hc : c ≤ 1)
    (ha : ThetaBranch.order p.val a = (c : ℤ) + 3 * (n : ℤ)) :
    sphericalValue R Adata p a =
      (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ n *
        (if c = 1 then (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
          thetaGamma F Sf Adata (exteriorPrimeIdeal F Sf (skeletonPrime R p)) 2 *
            unitPhase R Adata p a ^ 2 else 1) := by
  have hn : ¬ ThetaBranch.order p.val a < 0 := by omega
  have he : (ThetaBranch.order p.val a).toNat = c + 3 * n := by omega
  have hmod : (c + 3 * n) % 3 = c := by omega
  have hdiv : (c + 3 * n) / 3 = n := by omega
  have hp : unitPhase R Adata p a ^ (2 * (c + 3 * n)) = unitPhase R Adata p a ^ (2 * c) := by
    have hexp : 2 * (c + 3 * n) = 2 * c + 6 * n := by omega
    have h6 : unitPhase R Adata p a ^ 6 = 1 := phaseHom_sixth R Adata p a
    rw [hexp, pow_add, pow_mul (unitPhase R Adata p a) 6 n, h6, one_pow, mul_one]
  rw [sphericalValue, if_neg hn, he, hp, sphericalDigit, hmod, hdiv]
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simp <;> ring

def localTotal (p : P) (a : Fˣ) : ℂ :=
  if p ∈ GlobalProjectMarkedSupport.support R d then
    localValue R Adata p (GlobalProjectMarkedSupport.digitAt R d p)
      (GlobalProjectMarkedSupport.markAt R d p) a
  else sphericalValue R Adata p a

include hi in
theorem localTotal_moving (p : P) (hp : p ∈ exteriorSupport F Sf d.moving) :
    localTotal R Adata d p (x R Adata d i) =
      localWeylScalar F Sf Adata (skeletonPrime R p) ⟨1, by decide⟩ 0 *
        unitPhase R Adata p (x R Adata d i) := by
  have hmark : p ∉ d.marks := fun h =>
    (Finset.disjoint_left.mp (GlobalProjectMarkedSupport.moving_disjoint_marks R d)) hp h
  have hs : p ∈ GlobalProjectMarkedSupport.support R d := Finset.mem_union_left _ hp
  simp [localTotal, hs, GlobalProjectMarkedSupport.digitAt, hp,
    GlobalProjectMarkedSupport.markAt, hmark, localValue, inactiveCoefficient,
    activeCoefficient, activeValue, moving_order R Adata d i hi p hp, localWeylExponent]

include hi in
theorem localTotal_frozen (p : P) (hp : p ∈ i.activeFrozen) :
    localTotal R Adata d p (x R Adata d i) =
      localWeylScalar F Sf Adata (skeletonPrime R p) (rowDigit F Sf d p)
        (primeExponents i.numeratorFrozen.val p.val) *
      unitPhase R Adata p (x R Adata d i) ^
        localWeylExponent (rowDigit F Sf d p) (primeExponents i.numeratorFrozen.val p.val) := by
  have hf := i.frozen_subset hp
  have hm : p ∉ exteriorSupport F Sf d.moving := fun h =>
    (Finset.disjoint_left.mp (GlobalProjectMarkedSupport.moving_disjoint_frozen R d)) h hf
  have hmark : p ∉ d.marks := fun h =>
    (Finset.disjoint_left.mp (GlobalIndexSupport.marks_disjoint_frozen F Sf d)) h hf
  have hs : p ∈ GlobalProjectMarkedSupport.support R d :=
    Finset.mem_union_right _ (Finset.mem_union_left _ hf)
  have he : ThetaBranch.order p.val (x R Adata d i) + 2 =
      (primeExponents i.numeratorFrozen.val p.val : ℤ) := by
    rw [frozen_order R Adata d i hi p hp]
    omega
  have hi0 : inactiveCoefficient R Adata p (rowDigit F Sf d p) false (x R Adata d i) = 0 := by
    by_cases hj : (rowDigit F Sf d p).val = 0
    · have hz := optional_frozen_a R d i hi p hp hj
      simp [inactiveCoefficient, sphericalValue, frozen_order R Adata d i hi p hp, hz]
    · simp [inactiveCoefficient, hj]
  simp only [localTotal, if_pos hs, GlobalProjectMarkedSupport.digitAt,
    if_neg hm, if_pos hf, GlobalProjectMarkedSupport.markAt, hmark, decide_false,
    localValue, hi0, zero_add, activeCoefficient, Bool.false_eq_true, if_false]
  simp [activeValue, he]

include hi in
theorem localTotal_marked (p : P) (hp : p ∈ i.activeMarks) :
    localTotal R Adata d p (x R Adata d i) =
      (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
        thetaGamma F Sf Adata (exteriorPrimeIdeal F Sf (skeletonPrime R p)) 2 *
          unitPhase R Adata p (x R Adata d i) ^ 2 := by
  have hm := i.marks_subset hp
  have hs : p ∈ GlobalProjectMarkedSupport.support R d :=
    Finset.mem_union_right _ (Finset.mem_union_right _ hm)
  simp [localTotal, hs, GlobalProjectMarkedSupport.markAt, hm, localValue,
    inactiveCoefficient, activeCoefficient, markedActive, sphericalValue,
    marked_order R Adata d i hi p hp]

def inactiveLocal (p : P) : ℂ :=
  (if p ∈ frozenPrimes F Sf d \ i.activeFrozen then 1 - (p.val.asIdeal.absNorm : ℂ)⁻¹ else 1) *
    (if p ∈ d.marks \ i.activeMarks then (p.val.asIdeal.absNorm : ℂ)⁻¹ else 1)

theorem localTotal_inactive (p : P) (hm : p ∉ exteriorSupport F Sf d.moving)
    (ha : p ∉ i.activeFrozen ∪ i.activeMarks) :
    localTotal R Adata d p (x R Adata d i) =
      inactiveLocal R d i p * sphericalValue R Adata p (x R Adata d i) := by
  have hf : p ∉ i.activeFrozen := fun h => ha (Finset.mem_union_left _ h)
  have hp : p ∉ i.activeMarks := fun h => ha (Finset.mem_union_right _ h)
  have hn : 0 ≤ ThetaBranch.order p.val (x R Adata d i) := by
    rw [outside_order R Adata d i p hm ha]
    positivity
  have hne : ThetaBranch.order p.val (x R Adata d i) ≠ -2 := by omega
  by_cases hmark : p ∈ d.marks
  · have hfr : p ∉ frozenPrimes F Sf d := fun h =>
      (Finset.disjoint_left.mp (GlobalIndexSupport.marks_disjoint_frozen F Sf d)) hmark h
    simp [localTotal, GlobalProjectMarkedSupport.support, hm, hmark,
      GlobalProjectMarkedSupport.markAt, localValue, inactiveCoefficient,
      activeCoefficient, markedActive, hne, inactiveLocal, hfr, hp]
  · by_cases hfr : p ∈ frozenPrimes F Sf d
    · have hj := inactive_frozen_digit R d i p hfr hf
      simp [localTotal, GlobalProjectMarkedSupport.support, hm, hfr,
        GlobalProjectMarkedSupport.digitAt, GlobalProjectMarkedSupport.markAt, hmark,
        localValue, inactiveCoefficient, activeCoefficient, hj,
        active_zero_digit R Adata p (x R Adata d i) hne, inactiveLocal, hf]
    · simp [localTotal, GlobalProjectMarkedSupport.support, hm, hfr, hmark, inactiveLocal]

def movingLocal (p : P) : ℂ :=
  localWeylScalar F Sf Adata (skeletonPrime R p) ⟨1, by decide⟩ 0 *
    unitPhase R Adata p (x R Adata d i)

def frozenLocal (p : P) : ℂ :=
  localWeylScalar F Sf Adata (skeletonPrime R p) (rowDigit F Sf d p)
    (primeExponents i.numeratorFrozen.val p.val) *
    unitPhase R Adata p (x R Adata d i) ^
      localWeylExponent (rowDigit F Sf d p) (primeExponents i.numeratorFrozen.val p.val)

def quadraticLocal (p : P) : ℂ :=
  (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
    thetaGamma F Sf Adata (exteriorPrimeIdeal F Sf (skeletonPrime R p)) 2 *
      unitPhase R Adata p (x R Adata d i) ^ 2

def modelLocal (p : P) : ℂ :=
  inactiveLocal R d i p *
    (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ primeExponents i.n.val p.val *
    (if p ∈ exteriorSupport F Sf d.moving then movingLocal R Adata d i p else 1) *
    (if p ∈ i.activeFrozen then frozenLocal R Adata d i p else 1) *
    (if p ∈ i.activeMarks then quadraticLocal R Adata d i p else 1) *
    (if p ∈ exteriorSupport F Sf i.c then quadraticLocal R Adata d i p else 1)

include hi in
theorem localTotal_model (p : P) :
    localTotal R Adata d p (x R Adata d i) = modelLocal R Adata d i p := by
  have hc0 (h : primeExponents i.c.val p.val = 0) : p ∉ exteriorSupport F Sf i.c := by
    rw [GlobalIndexSupport.mem_exteriorSupport, h]
    exact not_ne_iff.mpr rfl
  by_cases hm : p ∈ exteriorSupport F Sf d.moving
  · have ha : p ∉ i.activeFrozen ∪ i.activeMarks := fun h =>
      (Finset.disjoint_left.mp (moving_active_disjoint R d i)) hm h
    have hf : p ∉ i.activeFrozen := fun h => ha (Finset.mem_union_left _ h)
    have hp : p ∉ i.activeMarks := fun h => ha (Finset.mem_union_right _ h)
    have hfr : p ∉ frozenPrimes F Sf d := fun h =>
      (Finset.disjoint_left.mp (GlobalProjectMarkedSupport.moving_disjoint_frozen R d)) hm h
    have hmr : p ∉ d.marks := fun h =>
      (Finset.disjoint_left.mp (GlobalProjectMarkedSupport.moving_disjoint_marks R d)) hm h
    rw [localTotal_moving R Adata d i hi p hm]
    simp [modelLocal, inactiveLocal, hm, hf, hp, hfr, hmr,
      hi.moving_n p hm, hc0 (hi.moving_c p hm), movingLocal]
  · by_cases hf : p ∈ i.activeFrozen
    · have ha : p ∈ i.activeFrozen ∪ i.activeMarks := Finset.mem_union_left _ hf
      have hp : p ∉ i.activeMarks := fun h =>
        (Finset.disjoint_left.mp (marks_frozen_disjoint R d i)) h hf
      have hmr : p ∉ d.marks := fun h =>
        (Finset.disjoint_left.mp (GlobalIndexSupport.marks_disjoint_frozen F Sf d))
          h (i.frozen_subset hf)
      rw [localTotal_frozen R Adata d i hi p hf]
      simp [modelLocal, inactiveLocal, hm, hf, hp, hmr,
        active_n R d i hi p ha, hc0 (active_c R d i hi p ha), frozenLocal]
    · by_cases hp : p ∈ i.activeMarks
      · have ha : p ∈ i.activeFrozen ∪ i.activeMarks := Finset.mem_union_right _ hp
        have hfr : p ∉ frozenPrimes F Sf d := fun h =>
          (Finset.disjoint_left.mp (GlobalIndexSupport.marks_disjoint_frozen F Sf d))
            (i.marks_subset hp) h
        rw [localTotal_marked R Adata d i hi p hp]
        simp [modelLocal, inactiveLocal, hm, hf, hp, hfr,
          active_n R d i hi p ha, hc0 (active_c R d i hi p ha), quadraticLocal]
      · have ha : p ∉ i.activeFrozen ∪ i.activeMarks := by simp [hf, hp]
        rw [localTotal_inactive R Adata d i p hm ha,
          spherical_order R Adata p (x R Adata d i)
            (primeExponents i.c.val p.val) (primeExponents i.n.val p.val)
            (hi.supported.c_squarefree p) (outside_order R Adata d i p hm ha)]
        have hce : primeExponents i.c.val p.val = 1 ↔ p ∈ exteriorSupport F Sf i.c := by
          rw [GlobalProjectArithmeticProduct.squarefree_exponent F Sf i.c i.c_squarefree]
          by_cases h : p ∈ exteriorSupport F Sf i.c <;> simp [h]
        simp only [modelLocal, if_neg hm, if_neg hf, if_neg hp, hce, mul_one, quadraticLocal]
        ring

def envelope : Finset P :=
  GlobalProjectMarkedSupport.support R d ∪ exteriorSupport F Sf i.c ∪ exteriorSupport F Sf i.n

theorem modelLocal_support : Function.mulSupport (modelLocal R Adata d i) ⊆ envelope R d i := by
  intro p hp
  by_contra hn
  have ht : p ∉ GlobalProjectMarkedSupport.support R d :=
    fun h => hn (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hc : p ∉ exteriorSupport F Sf i.c :=
    fun h => hn (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hn' : p ∉ exteriorSupport F Sf i.n := fun h => hn (Finset.mem_union_right _ h)
  have hne : primeExponents i.n.val p.val = 0 :=
    not_ne_iff.mp (fun h => hn' ((GlobalIndexSupport.mem_exteriorSupport F Sf i.n p).mpr h))
  have hm : p ∉ exteriorSupport F Sf d.moving := fun h => ht (Finset.mem_union_left _ h)
  have hf : p ∉ frozenPrimes F Sf d :=
    fun h => ht (Finset.mem_union_right _ (Finset.mem_union_left _ h))
  have hmark : p ∉ d.marks :=
    fun h => ht (Finset.mem_union_right _ (Finset.mem_union_right _ h))
  have hfa : p ∉ i.activeFrozen := fun h => hf (i.frozen_subset h)
  have hma : p ∉ i.activeMarks := fun h => hmark (i.marks_subset h)
  exact hp (by simp [modelLocal, inactiveLocal, hm, hf, hmark, hfa, hma, hc, hne])

include hi in
theorem localTotal_finite :
    Function.HasFiniteMulSupport (fun p => localTotal R Adata d p (x R Adata d i)) := by
  simp_rw [localTotal_model R Adata d i hi]
  exact (envelope R d i).finite_toSet.subset (modelLocal_support R Adata d i)

def rawCoefficient : ℂ :=
  (∏ p ∈ frozenPrimes F Sf d \ i.activeFrozen, (1 - (p.val.asIdeal.absNorm : ℂ)⁻¹)) *
  (∏ p ∈ d.marks \ i.activeMarks, (p.val.asIdeal.absNorm : ℂ)⁻¹) *
  (exteriorNorm F Sf i.n : ℂ)⁻¹ *
  (∏ p ∈ exteriorSupport F Sf d.moving, movingLocal R Adata d i p) *
  (∏ p ∈ i.activeFrozen, frozenLocal R Adata d i p) *
  (∏ p ∈ i.activeMarks, quadraticLocal R Adata d i p) *
  (∏ p ∈ exteriorSupport F Sf i.c, quadraticLocal R Adata d i p)

theorem extend_product {M : Type*} [CommMonoid M] (s t : Finset P)
    (h : t ⊆ s) (f : P → M) :
    (∏ p ∈ s, if p ∈ t then f p else 1) = ∏ p ∈ t, f p := by
  rw [← Finset.prod_filter]
  congr 1
  exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr h)

theorem inverseNorm_product (I : ExteriorIdeal F Sf) (s : Finset P)
    (hs : exteriorSupport F Sf I ⊆ s) :
    (∏ p ∈ s, (p.val.asIdeal.absNorm : ℂ)⁻¹ ^ primeExponents I.val p.val) =
      (exteriorNorm F Sf I : ℂ)⁻¹ := by
  have hn : (∏ p ∈ s, (p.val.asIdeal.absNorm : ℂ) ^ primeExponents I.val p.val) =
      (exteriorNorm F Sf I : ℂ) := by
    have he := congrArg (fun t : ℝ => (t : ℂ))
      (GlobalProjectArithmeticProduct.exteriorNorm_product F Sf I)
    push_cast at he
    rw [he]
    symm
    apply Finset.prod_subset hs
    intro p _ hp
    have hz : primeExponents I.val p.val = 0 :=
      not_ne_iff.mp (fun h => hp ((GlobalIndexSupport.mem_exteriorSupport F Sf I p).mpr h))
    rw [hz, pow_zero]
  calc
    _ = (∏ p ∈ s, (p.val.asIdeal.absNorm : ℂ) ^ primeExponents I.val p.val)⁻¹ := by
      simp only [inv_pow, Finset.prod_inv_distrib]
    _ = _ := congrArg Inv.inv hn

theorem finprod_model : (∏ᶠ p : P, modelLocal R Adata d i p) = rawCoefficient R Adata d i := by
  let s := envelope R d i
  have hd : exteriorSupport F Sf d.moving ⊆ s := by
    intro p hp
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
  have hf : frozenPrimes F Sf d ⊆ s := by
    intro p hp
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_union_left _ hp)))
  have hm : d.marks ⊆ s := by
    intro p hp
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_union_right _ hp)))
  have hc : exteriorSupport F Sf i.c ⊆ s :=
    fun _ hp => Finset.mem_union_left _ (Finset.mem_union_right _ hp)
  have hn : exteriorSupport F Sf i.n ⊆ s := fun _ hp => Finset.mem_union_right _ hp
  rw [finprod_eq_prod_of_mulSupport_subset _ (modelLocal_support R Adata d i)]
  change (∏ p ∈ s, modelLocal R Adata d i p) = _
  simp only [modelLocal, inactiveLocal, Finset.prod_mul_distrib]
  rw [extend_product R s _ (Finset.sdiff_subset.trans hf),
    extend_product R s _ (Finset.sdiff_subset.trans hm), inverseNorm_product R i.n s hn,
    extend_product R s _ hd, extend_product R s _ (i.frozen_subset.trans hf),
    extend_product R s _ (i.marks_subset.trans hm), extend_product R s _ hc]
  rfl

variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T) (H : Input R D Adata)

include hi H in
/-- Exact finite product of the actual local exterior slots, with the
same frozen source tuple retained by the global Fourier extraction. -/
theorem reverseCoefficient_raw :
    GlobalProjectSignedExtraction.reverseCoefficient R D (GlobalProjectMarkedSupport.row R d)
      (GlobalProjectMarkedSupport.weight R Adata d) (x R Adata d i) =
        rawCoefficient R Adata d i := by
  have he : GlobalProjectSignedExtraction.reverseCoefficient R D
      (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
      (x R Adata d i) =
      ∏ᶠ p : P, localTotal R Adata d p (x R Adata d i) := by
    rw [GlobalProjectMarkedSupport.weight,
      reverseCoefficient_literal_product R D Adata H]
    change (∏ p : RowPrime R (GlobalProjectMarkedSupport.row R d),
        localValue R Adata (exteriorRowPrime R (GlobalProjectMarkedSupport.row R d) p)
          (GlobalProjectMarkedSupport.digitAt R d
            (exteriorRowPrime R (GlobalProjectMarkedSupport.row R d) p))
          (GlobalProjectMarkedSupport.markAt R d
            (exteriorRowPrime R (GlobalProjectMarkedSupport.row R d) p)) (x R Adata d i)) *
      GlobalProjectDigitProduct.offRowProduct R D (GlobalProjectMarkedSupport.row R d) (x R Adata d i) = _
    rw [show (∏ p : RowPrime R (GlobalProjectMarkedSupport.row R d),
        localValue R Adata (exteriorRowPrime R (GlobalProjectMarkedSupport.row R d) p)
          (GlobalProjectMarkedSupport.digitAt R d
            (exteriorRowPrime R (GlobalProjectMarkedSupport.row R d) p))
          (GlobalProjectMarkedSupport.markAt R d
            (exteriorRowPrime R (GlobalProjectMarkedSupport.row R d) p)) (x R Adata d i)) =
        ∏ p ∈ exteriorRows R (GlobalProjectMarkedSupport.row R d),
          localValue R Adata p (GlobalProjectMarkedSupport.digitAt R d p)
            (GlobalProjectMarkedSupport.markAt R d p) (x R Adata d i) from
      (prod_exteriorRows R _ (fun p => localValue R Adata p
        (GlobalProjectMarkedSupport.digitAt R d p)
        (GlobalProjectMarkedSupport.markAt R d p) (x R Adata d i))).symm]
    rw [GlobalProjectMarkedSupport.exteriorRows_eq,
      split_product (GlobalProjectMarkedSupport.support R d) _ (localTotal_finite R Adata d i hi)]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      simp only [localTotal, if_pos hp]
    · rw [GlobalProjectDigitProduct.offRowProduct,
        GlobalProjectMarkedSupport.exteriorRows_eq]
      apply finprod_congr
      intro p
      by_cases hp : p ∈ GlobalProjectMarkedSupport.support R d
      · simp [hp]
      · simp [hp, localTotal, H.diagonal]
  rw [he]
  simp_rw [localTotal_model R Adata d i hi]
  exact finprod_model R Adata d i

end ThetaGlobal.GlobalProjectReflectedLocalModel
