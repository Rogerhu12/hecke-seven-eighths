import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteMovingRowRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalProfileNormalizationInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalAllocatedCosts

/-!
# Original single-prime input on the actual normalized allocation

The independent MOM_PRIME input below is stated on original complete
rows, the literal list of moving S-integers and integer exponents, the
original remaining mask, and one original Schwartz function. It does
not mention a child, capacity choice, Fourier parameter, or moment bound.
Its constants and seminorm orders precede all of those moving data.

The analytic shape is that of
`PrimeCancellation.PairedProfiles.exists_uniform_masked_prime_seminorm_bound`
and `exists_uniform_paired_seminorm_bound`: the small prime loss is
retained, and the zero boundary is required only below the endpoint.
The repository's actual-Hecke adapter in
`cloud_notes/prime_cancellation/project_adapters/` is a draft text file,
not an imported theorem. Accordingly this module accepts the precise
independent canonical prime theorem under the task-group parallel rule;
it does not claim to derive that theorem from the generic analytic core.

The bridge proves the actual character, complete mask, nonprincipality,
window, support, and normalization identities internally. The output
has `primeBound ξ i = amplitude ξ ^ 2 * (Cprime * Z ^ loss)`, with the
same existing amplitude and kappa. The normalized cost is independent
of the Fourier parameter. Its product over the actual removed slots
pays the small loss once, with their actual cardinality.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

namespace CanonicalNormalizedPrimeAtoms

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The literal complete row character, including both fixed corrections
and all original moving factors. -/
def originalCharacter (moving : OriginalMovingFactors A P R)
    (correction slot : HeckeCharacter K)
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (u : NonzeroIdeal K) : HeckeCharacter K :=
  (correction * moving.character *
    completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R sector u) * slot

/-- The original mask includes the whole row, every displayed moving
factor, and the unchanged remaining ideal. -/
def originalMask (moving : OriginalMovingFactors A P R)
    (remaining u : NonzeroIdeal K) (I : Ideal (𝓞 K)) : Bool :=
  ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
    decide (IsCoprime I moving.support.val)) && decide (IsCoprime I remaining.val))

def originalPrimeSum (moving : OriginalMovingFactors A P R)
    (correction slot : HeckeCharacter K)
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (remaining u : NonzeroIdeal K) (W : 𝓢(ℝ, ℂ))
    (pool : Finset (HeightOneSpectrum (𝓞 K))) (X : ℝ) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹ * ∑ p ∈ pool,
    primeCoefficient K (originalCharacter moving correction slot sector u) p *
      W ((Ideal.absNorm p.asIdeal : ℝ) / X) *
        (if originalMask moving remaining u p.asIdeal then 1 else 0)

/-- The primitive bound is quantified over original arithmetic and a
single Schwartz window. In particular it is not a bound assumed for an
already constructed allocation. The whole complete-mask norm controls
the deleted primes and the moving conductor, before exponent cancellation. -/
def OriginalPrimeBound (theta : Finset (HeckeCharacter K))
    (lower upper maxLength κ loss Cprime Z₀ : ℝ)
    (orders : Finset (ℕ × ℕ)) : Prop :=
  ∀ Z : ℝ, Z₀ ≤ Z →
    ∀ (moving : OriginalMovingFactors A P R) (correction slot : HeckeCharacter K)
      (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      (remaining u : NonzeroIdeal K),
    (correction = 1 ∨ correction ∈ theta) → slot ∈ theta →
    completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u →
    originalCharacter moving correction slot sector u ≠ 1 →
    idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) ≤ Z ^ maxLength →
    ∀ length : ℝ, 0 < length → length ≤ maxLength →
    ∀ (W : 𝓢(ℝ, ℂ)) (pool : Finset (HeightOneSpectrum (𝓞 K))),
    Function.support (W : ℝ → ℂ) ⊆ Set.Icc lower upper →
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ 1 →
    (∀ p, W ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ length) ≠ 0 → p ∈ pool) →
    ‖originalPrimeSum moving correction slot sector remaining u W pool (Z ^ length)‖ ^ 2 ≤
      (Cprime * Z ^ loss) * Z ^ (κ * length)

/-- Required independent MOM_PRIME theorem, with its complete original
quantifier order. At kappa one the implication supplies no zero-free
premise. The entire interval [3/4,1] is retained. -/
def OriginalPrimeProvider (theta : Finset (HeckeCharacter K)) : Prop :=
  (∀ θ ∈ theta, FiniteOrder θ) →
  ∀ lower upper maxLength loss : ℝ,
    0 < lower → lower ≤ upper → 0 ≤ maxLength → 0 < loss →
    ∃ (orders : Finset (ℕ × ℕ)) (Cprime Z₀ : ℝ),
      1 ≤ Cprime ∧ 1 < Z₀ ∧
      ∀ κ : ℝ, 3 / 4 ≤ κ → κ ≤ 1 →
        (κ < 1 → FiniteOrderBoundary (K := K) ((1 + κ) / 2)) →
        OriginalPrimeBound (A := A) (P := P) (R := R) theta
          lower upper maxLength κ loss Cprime Z₀ orders

/-- A live slot makes the length positive. The actual paired-row
exclusion and inverse membership, rather than finite order alone,
then rule out its principal prime character. -/
theorem slot_character_ne_one {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (a : RealParameters) (Z : ℝ)
    (hz : a.z = d.geometry.totalLength)
    (hinv : ∀ θ ∈ d.theta, θ⁻¹ ∈ d.theta)
    (hslot : ∀ i, d.slotCoefficient i ∈ d.theta)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows d a Z)
    (i : Fin d.geometry.slotCount) : d.rowCharacter u * d.slotCoefficient i ≠ 1 := by
  have hi : (d.geometry.slots i).length ≤ d.geometry.totalLength :=
    Finset.single_le_sum (fun j _ => (d.geometry.slots j).length_pos.le)
      (Finset.mem_univ i)
  have hzpos : 0 < a.z := by
    rw [hz]
    exact (d.geometry.slots i).length_pos.trans_le hi
  have hnot : d.rowCharacter u ∉ d.theta := by
    have h := (Finset.mem_filter.mp hu).2
    simpa only [if_neg hzpos.ne'] using h
  intro hone
  have heq : d.rowCharacter u = (d.slotCoefficient i)⁻¹ := by
    calc
      d.rowCharacter u = (d.rowCharacter u * d.slotCoefficient i) *
          (d.slotCoefficient i)⁻¹ := by simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = (d.slotCoefficient i)⁻¹ := by rw [hone, one_mul]
  apply hnot
  rw [heq]
  exact hinv _ (hslot i)

section ActualFamily

variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}

/-- Identify the primitive original finite sum with the actual polynomial.
The same original support and Boolean mask are used term by term. -/
theorem originalPrimeSum_eq_primePolynomial
    (recipe : CompleteMovingRowRecipe A P R data) (ξ : X)
    (u : NonzeroIdeal K) (hu : (data ξ).allowedRow u)
    (i : Fin (data ξ).geometry.slotCount) (Z t : ℝ)
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (w : RawProfileWindow rowDomain heightDomain window orders (data ξ) amplitude) :
    originalPrimeSum recipe.moving recipe.correction ((data ξ).slotCoefficient i)
        (recipe.sector u) recipe.remaining u (w.primeRep i t)
        (((data ξ).geometry.slots i).support t (Z ^ ((data ξ).geometry.slots i).length))
        (Z ^ ((data ξ).geometry.slots i).length) =
      primePolynomial (data ξ) i u Z t := by
  unfold originalPrimeSum primePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [recipe.character ξ u hu, w.prime_eq, maskValue, recipe.mask ξ u p.asIdeal]
  rfl

theorem primePolynomial_bound
    (recipe : CompleteMovingRowRecipe A P R data)
    {theta : Finset (HeckeCharacter K)}
    {lower upper maxLength κ loss Cprime Z₀ : ℝ} {orders : Finset (ℕ × ℕ)}
    (prime : OriginalPrimeBound (A := A) (P := P) (R := R) theta
      lower upper maxLength κ loss Cprime Z₀ orders)
    (Z : ℝ) (hZ : Z₀ ≤ Z) (a : RealParameters) (hκ : a.κ = κ)
    (htheta : ∀ ξ, (data ξ).theta = theta)
    (hinv : ∀ θ ∈ theta, θ⁻¹ ∈ theta)
    (hslot : ∀ ξ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)
    (hz : ∀ ξ, a.z = (data ξ).geometry.totalLength)
    (hjoint : recipe.FullJointBudget Z maxLength)
    (hlength : ∀ ξ i, ((data ξ).geometry.slots i).length ≤ maxLength)
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain : Set ℝ}
    {controlledOrders : Finset (ℕ × ℕ)} (horders : orders ⊆ controlledOrders)
    (ξ : X) (t : ℝ) (ht : t ∈ heightDomain)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lower upper)
      controlledOrders (data ξ) 1)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows (data ξ) a Z)
    (i : Fin (data ξ).geometry.slotCount) :
    ‖primePolynomial (data ξ) i u Z t‖ ^ 2 ≤
      (Cprime * Z ^ loss) * Z ^ (a.κ * ((data ξ).geometry.slots i).length) := by
  have hallowed : (data ξ).allowedRow u :=
    (((data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  have hcorrection : recipe.correction = 1 ∨ recipe.correction ∈ theta := by
    simpa only [htheta ξ] using recipe.correction_mem ξ
  have hslot' : (data ξ).slotCoefficient i ∈ theta := by
    simpa only [htheta ξ] using hslot ξ i
  have hnonprincipal :
      originalCharacter recipe.moving recipe.correction ((data ξ).slotCoefficient i)
        (recipe.sector u) u ≠ 1 := by
    rw [originalCharacter, ← recipe.character ξ u hallowed]
    exact slot_character_ne_one (data ξ) a Z (hz ξ)
      (by simpa only [htheta ξ] using hinv) (hslot ξ) u hu i
  have hseminorm : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (w.primeRep i t) ≤ 1 :=
    (Seminorm.le_def.mp (Finset.sup_mono horders) (w.primeRep i t)).trans
      (w.prime_bound i t ht)
  have hcover : ∀ p : HeightOneSpectrum (𝓞 K),
      w.primeRep i t ((Ideal.absNorm p.asIdeal : ℝ) /
        Z ^ ((data ξ).geometry.slots i).length) ≠ 0 →
      p ∈ ((data ξ).geometry.slots i).support t
        (Z ^ ((data ξ).geometry.slots i).length) := by
    intro p hp
    apply (((data ξ).geometry.slots i).support_spec t _ p).mpr
    rw [w.prime_eq]
    exact hp
  have h := prime Z hZ recipe.moving recipe.correction ((data ξ).slotCoefficient i)
    (recipe.sector u) recipe.remaining u hcorrection hslot'
    (recipe.exterior ξ u hallowed) hnonprincipal (hjoint ξ u hallowed)
    ((data ξ).geometry.slots i).length ((data ξ).geometry.slots i).length_pos
    (hlength ξ i) (w.primeRep i t) _ (w.prime_support i t ht) hseminorm hcover
  rw [originalPrimeSum_eq_primePolynomial recipe ξ u hallowed i Z t w] at h
  simpa only [hκ] using h

end ActualFamily

/-- The Fourier-independent prime cost still displays its entire small
power. It is never folded into a purported fixed constant. -/
def primeCost (Cprime Z loss : ℝ) : ℝ := Cprime * Z ^ loss

theorem primeCost_nonneg {Cprime Z loss : ℝ} (hC : 0 ≤ Cprime) (hZ : 0 ≤ Z) :
    0 ≤ primeCost Cprime Z loss := mul_nonneg hC (Real.rpow_nonneg hZ _)

section ActualAllocation

variable {σ : K →+* ℂ} {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {source : ActualAllocatedSource A V H k}
variable {ω ψ : HeckeCharacter K}

/-- Apply the original prime theorem to the actual normalized data,
without changing its profile radius or choosing a new child. -/
theorem normalized_prime_bound
    (D : source.Calibration (σ := σ) ω ψ)
    (recipe : CompleteMovingRowRecipe A P R D.data)
    {theta : Finset (HeckeCharacter K)}
    {lower upper maxLength loss Cprime Z₀ : ℝ} {orders : Finset (ℕ × ℕ)}
    (prime : OriginalPrimeBound (A := A) (P := P) (R := R) theta
      lower upper maxLength D.parameters.κ loss Cprime Z₀ orders)
    (hZ : Z₀ ≤ source.base)
    (htheta : ∀ ξ, (D.data ξ).theta = theta)
    (hinv : ∀ θ ∈ theta, θ⁻¹ ∈ theta)
    (hjoint : recipe.FullJointBudget source.base maxLength)
    (hlength : ∀ i, source.childLength i ≤ maxLength)
    (amplitude : V → ℝ) (hamp : ∀ ξ, 0 < amplitude ξ)
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain : Set ℝ}
    (profiles : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lower upper)
      (OriginalProfileAtomBounds.profileOrders orders) (D.data ξ) (amplitude ξ))
    (hheight : ∀ ξ, D.height ξ ∈ heightDomain)
    (ξ : V) (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows (D.data ξ) D.parameters source.base)
    (i : Fin source.allocation.keep.card) :
    ‖primePolynomial (normalizedMomentProfiles (D.data ξ) (amplitude ξ) (hamp ξ))
      (lengthSlot (D.data ξ) source.allocation.keep.card (D.count ξ) i)
      u source.base (D.height ξ)‖ ^ 2 ≤
      primeCost Cprime source.base loss * source.base ^ (D.parameters.κ * source.childLength i) := by
  let normalized := recipe.normalized amplitude hamp
  have hz (ζ : V) : D.parameters.z = (D.data ζ).geometry.totalLength := by
    apply D.slot_sum.trans
    symm
    apply length_totalLength_eq (D.data ζ) source.allocation.keep.card
      (D.count ζ) source.childLength
    exact D.clipped_lengths ζ
  obtain ⟨w⟩ := normalizedMomentProfiles_in_fixed_window (hamp ξ) (profiles ξ)
  have h := primePolynomial_bound normalized prime source.base hZ D.parameters rfl
    htheta hinv D.slot_in_theta hz hjoint
    (fun ζ j => by
      change ((D.data ζ).geometry.slots j).length ≤ maxLength
      rw [D.lengths ζ j]
      exact hlength _)
    (show orders ⊆ OriginalProfileAtomBounds.profileOrders orders from
      Finset.subset_insert _ _) ξ (D.height ξ) (hheight ξ) w u hu
    (lengthSlot (D.data ξ) source.allocation.keep.card (D.count ξ) i)
  have hlen : ((D.data ξ).geometry.slots
      (lengthSlot (D.data ξ) source.allocation.keep.card (D.count ξ) i)).length =
        source.childLength i := D.clipped_lengths ξ i
  change ‖primePolynomial (normalizedMomentProfiles (D.data ξ) (amplitude ξ) (hamp ξ))
      (lengthSlot (D.data ξ) source.allocation.keep.card (D.count ξ) i)
      u source.base (D.height ξ)‖ ^ 2 ≤
    (Cprime * source.base ^ loss) * source.base ^
      (D.parameters.κ * ((D.data ξ).geometry.slots
        (lengthSlot (D.data ξ) source.allocation.keep.card (D.count ξ) i)).length) at h
  rw [hlen] at h
  exact h

/-- Original raw atoms with their exact separated prime cost. All
annulus and raw-amplitude factors are supplied by the existing original
profile producer; the normalized prime premise is proved above. -/
def originalCapacityAtoms
    (D : source.Calibration (σ := σ) ω ψ)
    (recipe : CompleteMovingRowRecipe A P R D.data)
    {theta : Finset (HeckeCharacter K)}
    {lower upper maxLength loss Cprime Z₀ : ℝ} {orders : Finset (ℕ × ℕ)}
    (prime : OriginalPrimeBound (A := A) (P := P) (R := R) theta
      lower upper maxLength D.parameters.κ loss Cprime Z₀ orders)
    (hC : 0 ≤ Cprime) (hZ : Z₀ ≤ source.base) (hupper : 1 ≤ upper)
    (htheta : ∀ ξ, (D.data ξ).theta = theta)
    (hinv : ∀ θ ∈ theta, θ⁻¹ ∈ theta)
    (hjoint : recipe.FullJointBudget source.base maxLength)
    (hlength : ∀ i, source.childLength i ≤ maxLength)
    (amplitude : V → ℝ) (hamp : ∀ ξ, 0 < amplitude ξ)
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain : Set ℝ}
    (profiles : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lower upper)
      (OriginalProfileAtomBounds.profileOrders orders) (D.data ξ) (amplitude ξ))
    (hrows : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters source.base, u ∈ rowDomain)
    (hheight : ∀ ξ, D.height ξ ∈ heightDomain) : D.OriginalCapacityAtoms :=
  D.originalCapacityAtomsOfNormalizedPrime amplitude hamp profiles upper hupper
    (fun _ hx => hx.2) hrows hheight (primeCost Cprime source.base loss)
    (primeCost_nonneg hC (zero_le_one.trans source.base_gt_one.le))
    (normalized_prime_bound D recipe prime hZ htheta hinv hjoint hlength
      amplitude hamp profiles hheight)

/-- Consume the independent original provider before selecting any
allocated source, parameter kappa, profile, radius, or Fourier member.
The returned record is the actual capacity record for that source,
with both original annuli and the separated prime factors identified. -/
theorem exists_originalCapacityAtoms
    (theta : Finset (HeckeCharacter K))
    (provider : OriginalPrimeProvider (A := A) (P := P) (R := R) theta)
    (hfinite : ∀ θ ∈ theta, FiniteOrder θ)
    (lower upper maxLength loss : ℝ)
    (hlower : 0 < lower) (hwindow : lower ≤ upper) (hupper : 1 ≤ upper)
    (hmaxLength : 0 ≤ maxLength) (hloss : 0 < loss) :
    ∃ (orders : Finset (ℕ × ℕ)) (Cprime Z₀ : ℝ),
      1 ≤ Cprime ∧ 1 < Z₀ ∧
      ∀ {n : ℕ} (s : ActualAllocatedSource A V H n) (D : s.Calibration (σ := σ) ω ψ)
        (recipe : CompleteMovingRowRecipe A P R D.data),
        3 / 4 ≤ D.parameters.κ → D.parameters.κ ≤ 1 →
        (D.parameters.κ < 1 →
          FiniteOrderBoundary (K := K) ((1 + D.parameters.κ) / 2)) →
        Z₀ ≤ s.base → (∀ ξ, (D.data ξ).theta = theta) →
        (∀ θ ∈ theta, θ⁻¹ ∈ theta) → recipe.FullJointBudget s.base maxLength →
        (∀ i, s.childLength i ≤ maxLength) →
        ∀ (amplitude : V → ℝ) (hamp : ∀ ξ, 0 < amplitude ξ)
          (rowDomain : Set (NonzeroIdeal K)) (heightDomain : Set ℝ),
        (∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lower upper)
          (OriginalProfileAtomBounds.profileOrders orders) (D.data ξ) (amplitude ξ)) →
        (∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, u ∈ rowDomain) →
        (∀ ξ, D.height ξ ∈ heightDomain) →
        ∃ atoms : D.OriginalCapacityAtoms,
          atoms.leftAnnulus = upper ∧ atoms.rightAnnulus = upper ∧
          ∀ ξ i, atoms.primeBound ξ i = amplitude ξ ^ 2 * primeCost Cprime s.base loss := by
  obtain ⟨orders, Cprime, Z₀, hC, hZ₀, hprime⟩ :=
    provider hfinite lower upper maxLength loss hlower hwindow hmaxLength hloss
  refine ⟨orders, Cprime, Z₀, hC, hZ₀, ?_⟩
  intro n s D recipe hκlo hκhi hboundary hZ htheta hinv hjoint hlength
    amplitude hamp rowDomain heightDomain profiles hrows hheight
  let atoms := originalCapacityAtoms D recipe
    (hprime D.parameters.κ hκlo hκhi hboundary) (zero_le_one.trans hC) hZ hupper
    htheta hinv hjoint hlength amplitude hamp profiles hrows hheight
  exact ⟨atoms, rfl, rfl, fun _ _ => rfl⟩

end ActualAllocation

/-- The exact removed product contains each prime loss once. This
identity applies to the actual already selected removal set. -/
theorem removed_primeCost_product {ι : Type*} (removed : Finset ι)
    (Cprime Z loss : ℝ) (hZ : 0 ≤ Z) :
    (∏ _i ∈ removed, primeCost Cprime Z loss) =
      Cprime ^ removed.card * Z ^ (loss * removed.card) := by
  simp only [Finset.prod_const, primeCost, mul_pow,
    Real.rpow_mul_natCast hZ]

theorem removed_primeCost_product_le {ι : Type*} [Fintype ι]
    (removed : Finset ι) (cap : ℕ) (hcap : Fintype.card ι ≤ cap)
    (Cprime Z loss : ℝ) (hC : 1 ≤ Cprime) (hZ : 1 ≤ Z) (hloss : 0 ≤ loss) :
    (∏ _i ∈ removed, primeCost Cprime Z loss) ≤
      Cprime ^ cap * Z ^ (loss * cap) := by
  have hcost : 1 ≤ primeCost Cprime Z loss :=
    one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hZ hloss)
  have h := selected_factor_product_le removed (fun _ => primeCost Cprime Z loss)
    (primeCost Cprime Z loss) cap hcost hcap
    (fun _ _ => primeCost_nonneg (zero_le_one.trans hC) (zero_le_one.trans hZ))
    (fun _ _ => le_rfl)
  simpa only [primeCost, mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hZ)] using h

/-- The prime loss fits inside the same enlarged original profile
budget. The radius of the actual child is unchanged. -/
theorem primeCost_le_profile_envelope
    (Cprime Cprofile profile Z loss rate : ℝ)
    (hC : 0 ≤ Cprime) (hCC : Cprime ≤ Cprofile)
    (hprofile : 1 ≤ profile) (hZ : 1 ≤ Z) (hloss : loss ≤ rate) :
    primeCost Cprime Z loss ≤ Cprofile * profile * Z ^ rate := by
  have hCp : 0 ≤ Cprofile := hC.trans hCC
  have hcoefficient : Cprime ≤ Cprofile * profile :=
    hCC.trans (le_mul_of_one_le_right hCp hprofile)
  calc
    _ ≤ Cprime * Z ^ rate :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hloss) hC
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoefficient
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)

/-- A varying normalized prime cost belongs to the same profile power
as the original atom envelopes. Only its fixed coefficient enters the
constant, so no power of Z is hidden in that constant. With the actual
log-profile degree one and prime degree one, the displayed maximum is
still two. -/
theorem atomBudget_le_profile_power_with_prime
    (annulus amplitude rowCost cost Cprime profile : ℝ)
    (dAmplitude dRow dPrime : ℕ)
    (hannulus : 0 ≤ annulus) (hprofile : 1 ≤ profile)
    (hamplitude : 0 ≤ amplitude) (hamp : amplitude ≤ profile ^ dAmplitude)
    (hrow : rowCost ≤ profile ^ dRow)
    (hprime : cost ≤ Cprime * profile ^ dPrime) :
    OriginalProfileAtomBounds.atomBudget annulus amplitude rowCost cost ≤
      max 1 (max annulus Cprime) *
        profile ^ max (2 * dAmplitude) (max dRow dPrime) := by
  let C := max 1 (max annulus Cprime)
  let degree := max (2 * dAmplitude) (max dRow dPrime)
  have hC : 1 ≤ C := le_max_left _ _
  have hCA : annulus ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCP : Cprime ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hpow : 1 ≤ profile ^ degree := one_le_pow₀ hprofile
  have hCpow : C ≤ C * profile ^ degree := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hC)
  have hunit : 1 ≤ C * profile ^ degree := hC.trans hCpow
  have hrowDegree : dRow ≤ degree := (le_max_left _ _).trans (le_max_right _ _)
  have hprimeDegree : dPrime ≤ degree := (le_max_right _ _).trans (le_max_right _ _)
  have hrow' : rowCost ≤ C * profile ^ degree := by
    calc
      _ ≤ profile ^ dRow := hrow
      _ ≤ profile ^ degree := pow_le_pow_right₀ hprofile hrowDegree
      _ ≤ C * profile ^ degree := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC
          (pow_nonneg (zero_le_one.trans hprofile) _)
  have hamp' : amplitude ^ 2 ≤ profile ^ (2 * dAmplitude) := by
    calc
      _ ≤ (profile ^ dAmplitude) ^ 2 := pow_le_pow_left₀ hamplitude hamp 2
      _ = _ := by rw [← pow_mul, Nat.mul_comm dAmplitude 2]
  have hatom : annulus * amplitude ^ 2 ≤ C * profile ^ degree :=
    (mul_le_mul_of_nonneg_left hamp' hannulus).trans
      (mul_le_mul hCA (pow_le_pow_right₀ hprofile (le_max_left _ _))
        (pow_nonneg (zero_le_one.trans hprofile) _) (zero_le_one.trans hC))
  have hprime' : cost ≤ C * profile ^ degree :=
    hprime.trans (mul_le_mul hCP (pow_le_pow_right₀ hprofile hprimeDegree)
      (pow_nonneg (zero_le_one.trans hprofile) _) (zero_le_one.trans hC))
  exact max_le hunit (max_le hrow' (max_le hatom hprime'))

end CanonicalNormalizedPrimeAtoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.slot_character_ne_one
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.originalPrimeSum_eq_primePolynomial
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.primePolynomial_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.normalized_prime_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.originalCapacityAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.exists_originalCapacityAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.removed_primeCost_product
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.removed_primeCost_product_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.primeCost_le_profile_envelope
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalNormalizedPrimeAtoms.atomBudget_le_profile_power_with_prime
