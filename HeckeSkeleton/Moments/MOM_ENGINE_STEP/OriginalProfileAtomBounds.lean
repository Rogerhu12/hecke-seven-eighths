import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonAtomBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalCapacityKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileNormalizationInput
import Mathlib.Topology.Order.Compact

/-!
# Original profile control produces the actual frozen atom windows

The fixed control set is enlarged by the point-evaluation seminorm
before any original profile, slot or source label is chosen. Compact
support gives one upper annulus. The original Schwartz representatives
then bound every frozen prime profile, including its unchanged unit
Fourier phase. The arithmetic coefficients use their actual Hecke
characters and their original zero-or-one mask.

The resulting common and allocation bounds have constant, computed
annulus and profile fields. A final constructor fills the pointwise
OriginalAtomWindow used by the actual normalized-family mass theorem.
The retained prime-polynomial bound remains the independent MOM_PRIME
input; it is not replaced by a cardinality estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace OriginalProfileAtomBounds

/-- Select this finite set together with the other fixed analytic
orders. No inclusion condition is imposed on the incoming order set. -/
def profileOrders (orders : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  insert (0, 0) orders

theorem norm_le_profileOrders (orders : Finset (ℕ × ℕ))
    (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖f x‖ ≤ (profileOrders orders).sup (schwartzSeminormFamily ℂ ℝ ℂ) f := by
  apply (SchwartzMap.norm_le_seminorm ℂ f x).trans
  exact Seminorm.le_finset_sup_apply (Finset.mem_insert_self (0, 0) orders)

theorem exists_upper_window_bound (window : Set ℝ) (hcompact : IsCompact window) :
    ∃ annulus : ℝ, 1 ≤ annulus ∧ window ⊆ Set.Iic annulus := by
  obtain ⟨upper, hupper⟩ := hcompact.bddAbove
  exact ⟨max 1 upper, le_max_left _ _, fun _ hx =>
    (hupper hx).trans (le_max_right _ _)⟩

theorem indicator_norm_le_one (z : ℂ) (hz : z = 0 ∨ z = 1) : ‖z‖ ≤ 1 := by
  rcases hz with rfl | rfl <;> norm_num

theorem sourcePlainCoefficient_norm_le_one
    (χ θ : HeckeCharacter K) (mask : Ideal (𝓞 K) →* ℂ)
    (I : NonzeroIdeal K) (hmask : mask I.val = 0 ∨ mask I.val = 1) :
    ‖sourcePlainCoefficient χ θ mask I‖ ≤ 1 := by
  have hχ := norm_heckeIdealCoefficient_le_one K χ I
  have hθ := norm_heckeIdealCoefficient_le_one K θ I
  have hM := indicator_norm_le_one _ hmask
  have hpair : ‖heckeIdealCoefficient K χ I‖ * ‖heckeIdealCoefficient K θ I‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hχ hθ (norm_nonneg _) zero_le_one
  simpa only [sourcePlainCoefficient, norm_mul, one_mul] using
    mul_le_mul hpair hM (norm_nonneg _) zero_le_one

theorem sourcePrimeCoefficient_norm_le_one
    (χ θ : HeckeCharacter K) (mask : Ideal (𝓞 K) →* ℂ)
    (p : HeightOneSpectrum (𝓞 K)) (hmask : mask p.asIdeal = 0 ∨ mask p.asIdeal = 1) :
    ‖sourcePrimeCoefficient χ θ mask p‖ ≤ 1 := by
  have hχ := norm_primeCoefficient_le_one K χ p
  have hθ := norm_primeCoefficient_le_one K θ p
  have hM := indicator_norm_le_one _ hmask
  have hpair : ‖primeCoefficient K χ p‖ * ‖primeCoefficient K θ p‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hχ hθ (norm_nonneg _) zero_le_one
  simpa only [sourcePrimeCoefficient, norm_mul, one_mul] using
    mul_le_mul hpair hM (norm_nonneg _) zero_le_one

/-- A common constant selected from original individual costs. It
does not contain an envelope product, a child weight or a mass. -/
def atomBudget (annulus amplitude rowCost primeCost : ℝ) : ℝ :=
  max 1 (max rowCost (max (annulus * amplitude ^ 2) primeCost))

theorem atomBudget_one (annulus amplitude rowCost primeCost : ℝ) :
    1 ≤ atomBudget annulus amplitude rowCost primeCost := le_max_left _ _

theorem atomBudget_row (annulus amplitude rowCost primeCost : ℝ) :
    rowCost ≤ atomBudget annulus amplitude rowCost primeCost :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem atomBudget_atom (annulus amplitude rowCost primeCost : ℝ) :
    annulus * amplitude ^ 2 ≤ atomBudget annulus amplitude rowCost primeCost :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem atomBudget_prime (annulus amplitude rowCost primeCost : ℝ) :
    primeCost ≤ atomBudget annulus amplitude rowCost primeCost :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The original atom cost has a fixed power of the same profile
control. The exponent is chosen before that control or a source label. -/
theorem atomBudget_le_profile_power (annulus amplitude rowCost primeCost P : ℝ)
    (dAmplitude dRow : ℕ) (hannulus : 0 ≤ annulus) (hP : 1 ≤ P)
    (hamplitude : 0 ≤ amplitude) (hamp : amplitude ≤ P ^ dAmplitude)
    (hrow : rowCost ≤ P ^ dRow) :
    atomBudget annulus amplitude rowCost primeCost ≤
      max 1 (max annulus primeCost) * P ^ max (2 * dAmplitude) dRow := by
  let C := max 1 (max annulus primeCost)
  let d := max (2 * dAmplitude) dRow
  have hC : 1 ≤ C := le_max_left _ _
  have hCA : annulus ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCP : primeCost ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hpow : 1 ≤ P ^ d := one_le_pow₀ hP
  have hCpow : C ≤ C * P ^ d := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hC)
  have hunit : 1 ≤ C * P ^ d := hC.trans hCpow
  have hrow' : rowCost ≤ C * P ^ d := by
    calc
      _ ≤ P ^ dRow := hrow
      _ ≤ P ^ d := pow_le_pow_right₀ hP (le_max_right _ _)
      _ ≤ C * P ^ d := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hC (pow_nonneg (zero_le_one.trans hP) _)
  have hamp' : amplitude ^ 2 ≤ P ^ (2 * dAmplitude) := by
    calc
      _ ≤ (P ^ dAmplitude) ^ 2 := pow_le_pow_left₀ hamplitude hamp 2
      _ = _ := by rw [← pow_mul, Nat.mul_comm dAmplitude 2]
  have hatom : annulus * amplitude ^ 2 ≤ C * P ^ d :=
    (mul_le_mul_of_nonneg_left hamp' hannulus).trans
      (mul_le_mul hCA (pow_le_pow_right₀ hP (le_max_left _ _))
        (pow_nonneg (zero_le_one.trans hP) _) (zero_le_one.trans hC))
  exact max_le hunit (max_le hrow' (max_le hatom (hCP.trans hCpow)))

end OriginalProfileAtomBounds

namespace RawProfileWindow

variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window
  (OriginalProfileAtomBounds.profileOrders orders) d amplitude)

theorem original_prime_profile_norm_le (i : Fin d.geometry.slotCount)
    (t : ℝ) (ht : t ∈ heightDomain) (x : ℝ) :
    ‖(d.geometry.slots i).profile t x‖ ≤ amplitude := by
  rw [profiles.prime_eq]
  exact (OriginalProfileAtomBounds.norm_le_profileOrders orders _ x).trans
    (profiles.prime_bound i t ht)

theorem original_prime_profile_phase_sq_le (i : Fin d.geometry.slotCount)
    (t : ℝ) (ht : t ∈ heightDomain) (x : ℝ) (phase : Circle) :
    ‖(d.geometry.slots i).profile t x * (phase : ℂ)‖ ^ 2 ≤ amplitude ^ 2 := by
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact pow_le_pow_left₀ (norm_nonneg _) (profiles.original_prime_profile_norm_le i t ht x) 2

theorem original_prime_norm_le_annulus (annulus Z t : ℝ)
    (hZ : 0 < Z) (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)) :
    (Ideal.absNorm p.asIdeal : ℝ) ≤ annulus * Z ^ (d.geometry.slots i).length := by
  have hprofile := ((d.geometry.slots i).support_spec t
    (Z ^ (d.geometry.slots i).length) p).mp hp
  have hrep : profiles.primeRep i t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
    simpa only [profiles.prime_eq] using hprofile
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp
    (hwindow (profiles.prime_support i t ht hrep))

theorem original_left_profile_upper (annulus : ℝ)
    (hwindow : window ⊆ Set.Iic annulus)
    (u : NonzeroIdeal K) (hu : u ∈ rowDomain) (t : ℝ) (ht : t ∈ heightDomain)
    (x : ℝ) (hx : d.plainTest₁.profile u t x ≠ 0) : x ≤ annulus := by
  apply hwindow
  apply profiles.left_support u hu t ht
  simpa only [profiles.left_eq] using hx

theorem original_right_profile_upper (annulus : ℝ)
    (hwindow : window ⊆ Set.Iic annulus)
    (u : NonzeroIdeal K) (hu : u ∈ rowDomain) (t : ℝ) (ht : t ∈ heightDomain)
    (x : ℝ) (hx : d.plainTest₂.profile u t x ≠ 0) : x ≤ annulus := by
  apply hwindow
  apply profiles.right_support u hu t ht
  simpa only [profiles.right_eq] using hx

end RawProfileWindow

section PrimeNormalization

variable {ω ψ : HeckeCharacter K}

/-- The normalized single-prime estimate recovers exactly one squared
profile amplitude on the original polynomial, without any slot count. -/
theorem primePolynomial_sq_recover_profile_amplitude
    (d : MomentData K ω ψ) (amplitude : ℝ) (hamp : 0 < amplitude)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ) :
    ‖primePolynomial d i u Z t‖ ^ 2 = amplitude ^ 2 *
      ‖primePolynomial (normalizedMomentProfiles d amplitude hamp) i u Z t‖ ^ 2 := by
  rw [primePolynomial_normalizedMomentProfiles, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hamp), mul_pow]
  field_simp [hamp.ne'] <;> ring

end PrimeNormalization

namespace ActualAllocatedSource.Calibration

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {ω ψ : HeckeCharacter K}
variable (D : s.Calibration (σ := σ) ω ψ)
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)}

/-- Actual profile support gives both plain windows. The only analytic
prime premise is the original normalized single-prime input. Its raw
amplitude factor and the entire OriginalCapacityAtoms record are
constructed here, before any capacity deletion is selected. -/
def originalCapacityAtomsOfNormalizedPrime
    (amplitude : V → ℝ) (hamp : ∀ ξ, 0 < amplitude ξ)
    (profiles : ∀ ξ, RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) (D.data ξ) (amplitude ξ))
    (annulus : ℝ) (hannulus : 1 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (hrows : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, u ∈ rowDomain)
    (hheight : ∀ ξ, D.height ξ ∈ heightDomain)
    (primeCost : ℝ) (hprimeCost : 0 ≤ primeCost)
    (hprime : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base,
      ∀ i : Fin s.allocation.keep.card,
      ‖primePolynomial (normalizedMomentProfiles (D.data ξ) (amplitude ξ) (hamp ξ))
        (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i)
        u s.base (D.height ξ)‖ ^ 2 ≤
        primeCost * s.base ^ (D.parameters.κ * s.childLength i)) :
    D.OriginalCapacityAtoms where
  leftAnnulus := annulus
  rightAnnulus := annulus
  leftAnnulus_one := hannulus
  rightAnnulus_one := hannulus
  left_window ξ u hu x hx :=
    (profiles ξ).original_left_profile_upper annulus hwindow u
      (hrows ξ u hu) (D.height ξ) (hheight ξ) x hx
  right_window ξ u hu x hx :=
    (profiles ξ).original_right_profile_upper annulus hwindow u
      (hrows ξ u hu) (D.height ξ) (hheight ξ) x hx
  primeBound ξ _ := amplitude ξ ^ 2 * primeCost
  primeBound_nonneg ξ _ := mul_nonneg (sq_nonneg _) hprimeCost
  prime_bound ξ u hu i := by
    rw [primePolynomial_sq_recover_profile_amplitude (D.data ξ) (amplitude ξ) (hamp ξ)]
    exact (mul_le_mul_of_nonneg_left (hprime ξ u hu i) (sq_nonneg _)).trans_eq (by ring)

end ActualAllocatedSource.Calibration

namespace SupportCartesianBranch

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S P)
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}

/-- Only the literal original prime dictionary and mask identity enter.
All norm bounds and both constant fields are constructed here. -/
def commonAtomBoundsOfOriginalProfiles
    (profiles : RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) d amplitude)
    (T : FixedChildCharacters K k) (Z t annulus : ℝ)
    (hZ : 0 < Z) (ht : t ∈ heightDomain) (hannulus : 1 ≤ annulus)
    (hwindow : window ⊆ Set.Iic annulus)
    (index : Fin k → Fin d.geometry.slotCount) (length : Fin k → ℝ)
    (hlength : ∀ i, length i = (d.geometry.slots (index i)).length)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (phase : Fin k → HeightOneSpectrum (𝓞 K) → Circle)
    (hweight : ∀ i p, w i p = (d.geometry.slots (index i)).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots (index i)).length) *
        (phase i p : ℂ))
    (hmask : ∀ I, T.mask I = 0 ∨ T.mask I = 1)
    (hsupport : ∀ i ∈ Finset.univ \ b.keep,
      b.witness.2 i ∈ (d.geometry.slots (index i)).support t
        (Z ^ (d.geometry.slots (index i)).length)) :
    b.CommonAtomBounds T Z length w where
  base_pos := hZ
  annulus _ := annulus
  profile _ := amplitude ^ 2
  annulus_nonneg _ := zero_le_one.trans hannulus
  profile_nonneg _ := sq_nonneg _
  plain₁ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _ (hmask _)
  plain₂ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _ (hmask _)
  prime i _ := OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one _ _ _ _ (hmask _)
  prime_annulus i hi := by
    simpa only [hlength i] using
      profiles.original_prime_norm_le_annulus annulus Z t hZ ht hwindow
        (index i) (b.witness.2 i) (hsupport i hi)
  slot i _ := by
    rw [hweight]
    exact profiles.original_prime_profile_phase_sq_le (index i) t ht _ _

end SupportCartesianBranch

namespace ParentRawAtoms

variable {A : SArithmeticData K} {Γ : Subgroup A.U} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
variable (raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}

/-- The actual original atlas supplies the frozen support membership;
the producer does not assume separate per-prime annulus windows. -/
def originalCommonAtomBounds
    (profiles : RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) d amplitude)
    (T : FixedChildCharacters K d.geometry.slotCount) (annulus : ℝ)
    (hZ : 0 < Z) (ht : t ∈ heightDomain) (hannulus : 1 ≤ annulus)
    (hwindow : window ⊆ Set.Iic annulus)
    (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
    (label : raw.originalAtlas.labels P D)
    (w : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ)
    (phase : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → Circle)
    (hweight : ∀ i p, w i p = (d.geometry.slots i).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) * (phase i p : ℂ))
    (hmask : ∀ I, T.mask I = 0 ∨ T.mask I = 1) :
    (raw.originalAtlas.branch P D label).CommonAtomBounds T Z
      (fun i => (d.geometry.slots i).length) w := by
  let b := raw.originalAtlas.branch P D label
  apply b.commonAtomBoundsOfOriginalProfiles profiles T Z t annulus
    hZ ht hannulus hwindow id (fun i => (d.geometry.slots i).length)
    (fun _ => rfl) w phase hweight hmask
  intro i _
  have hp := (Finset.mem_filter.mp (b.witness_slots i)).1
  change b.witness.2 i ∈ raw.exteriorSlots i at hp
  exact (Finset.mem_filter.mp hp).1

end ParentRawAtoms

namespace ActualAllocatedSource.FrozenAtomBounds

variable {A : SArithmeticData K} {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} (s : ActualAllocatedSource A V H k)
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}

/-- The selected original divisor and its actual occurrence allocation
provide only structural membership. All frozen analytic estimates are
proved from the original profile representatives. -/
def ofOriginalProfiles
    (profiles : RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders orders) d amplitude)
    (t annulus : ℝ) (ht : t ∈ heightDomain) (hannulus : 1 ≤ annulus)
    (hwindow : window ⊆ Set.Iic annulus)
    (index : Fin k → Fin d.geometry.slotCount)
    (hlength : ∀ i, s.length i = (d.geometry.slots (index i)).length)
    (phase : H → Fin k → HeightOneSpectrum (𝓞 K) → Circle)
    (hweight : ∀ h ∈ s.rows, ∀ i p, s.slotWeight h i p =
      (d.geometry.slots (index i)).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / s.base ^ (d.geometry.slots (index i)).length) *
          (phase h i p : ℂ))
    (hmask : ∀ h ∈ s.rows, ∀ I, (s.characters h).mask I = 0 ∨ (s.characters h).mask I = 1)
    (hsupport : ∀ i ∈ Finset.univ \ s.allocation.keep,
      s.allocation.witness.2 i ∈ (d.geometry.slots (index i)).support t
        (s.base ^ (d.geometry.slots (index i)).length))
    (hsquarefree : Squarefree s.allocation.divisor)
    (hallocation : s.allocation.selection ∈
      AllocationMass.idealAllocations s.allocation.divisor (k + 2)) : s.FrozenAtomBounds where
  annulus _ := annulus
  profile _ := amplitude ^ 2
  annulus_nonneg _ := zero_le_one.trans hannulus
  profile_nonneg _ := sq_nonneg _
  plain₁_bound h hh :=
    OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _ (hmask h hh _)
  plain₂_bound h hh :=
    OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _ (hmask h hh _)
  prime_bound h hh i _ :=
    OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one _ _ _ _ (hmask h hh _)
  prime_annulus i hi := by
    simpa only [hlength i] using
      profiles.original_prime_norm_le_annulus annulus s.base t
        (zero_lt_one.trans s.base_gt_one) ht hwindow
        (index i) (s.allocation.witness.2 i) (hsupport i hi)
  slot_bound h hh i _ := by
    rw [hweight h hh]
    exact profiles.original_prime_profile_phase_sq_le (index i) t ht _ _
  divisor_squarefree := hsquarefree
  allocation_mem := hallocation

end ActualAllocatedSource.FrozenAtomBounds

namespace CanonicalCapacityKernelMass.OriginalAtomWindow

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)

/-- The original producer uses the constant choices made above, and
the independently supplied single-prime cost. The displayed equalities
are definitional for those choices. No resulting atom-envelope bound
is requested from the caller. -/
def ofConstantOriginalAtoms (cap : ℕ) (annulus amplitude rowCost primeCost : ℝ)
    (hleft : k ≤ cap) (hright : l ≤ cap)
    (hcommonLeft : kLeft ≤ cap) (hcommonRight : kRight ≤ cap)
    (hrow : W.profileBound = rowCost)
    (hcommonLA : ∀ i, W.leftAtoms.annulus i = annulus)
    (hcommonLP : ∀ i, W.leftAtoms.profile i = amplitude ^ 2)
    (hcommonRA : ∀ i, W.rightAtoms.annulus i = annulus)
    (hcommonRP : ∀ i, W.rightAtoms.profile i = amplitude ^ 2)
    (hfrozenLA : ∀ i, BL.annulus i = annulus)
    (hfrozenLP : ∀ i, BL.profile i = amplitude ^ 2)
    (hfrozenRA : ∀ i, BR.annulus i = annulus)
    (hfrozenRP : ∀ i, BR.profile i = amplitude ^ 2)
    (hprimeL : ∀ i, boundsL i = primeCost)
    (hprimeR : ∀ i, boundsR i = primeCost) :
    CanonicalCapacityKernelMass.OriginalAtomWindow left right W BL BR boundsL boundsR cap
      (OriginalProfileAtomBounds.atomBudget annulus amplitude rowCost primeCost) where
  left_count := hleft
  right_count := hright
  common_left_count := hcommonLeft
  common_right_count := hcommonRight
  row_profile := by
    rw [hrow]
    exact OriginalProfileAtomBounds.atomBudget_row _ _ _ _
  common_left i _ := by
    rw [hcommonLA, hcommonLP]
    exact OriginalProfileAtomBounds.atomBudget_atom _ _ _ _
  common_right i _ := by
    rw [hcommonRA, hcommonRP]
    exact OriginalProfileAtomBounds.atomBudget_atom _ _ _ _
  frozen_left i _ := by
    rw [hfrozenLA, hfrozenLP]
    exact OriginalProfileAtomBounds.atomBudget_atom _ _ _ _
  frozen_right i _ := by
    rw [hfrozenRA, hfrozenRP]
    exact OriginalProfileAtomBounds.atomBudget_atom _ _ _ _
  removed_left i := by
    rw [hprimeL]
    exact OriginalProfileAtomBounds.atomBudget_prime _ _ _ _
  removed_right i := by
    rw [hprimeR]
    exact OriginalProfileAtomBounds.atomBudget_prime _ _ _ _

end CanonicalCapacityKernelMass.OriginalAtomWindow
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalProfileAtomBounds.norm_le_profileOrders
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalProfileAtomBounds.exists_upper_window_bound
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalProfileAtomBounds.atomBudget_le_profile_power
#print axioms HeckeSkeleton.Moments.EngineStep.RawProfileWindow.original_prime_norm_le_annulus
#print axioms HeckeSkeleton.Moments.EngineStep.primePolynomial_sq_recover_profile_amplitude
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.originalCapacityAtomsOfNormalizedPrime
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.commonAtomBoundsOfOriginalProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.originalCommonAtomBounds
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.FrozenAtomBounds.ofOriginalProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCapacityKernelMass.OriginalAtomWindow.ofConstantOriginalAtoms
