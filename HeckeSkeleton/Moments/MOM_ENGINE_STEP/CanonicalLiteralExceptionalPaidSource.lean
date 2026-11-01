import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalFactory
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPaidTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalPaidOrdinaryTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalAtomBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPaidScales
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalNumbers
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalPhysicalBox
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormFactorTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalOrdinaryExceptionalCalibration

/-!
# The paid exceptional terminal on the actual literal sources

The original single-character ideal-series primitive selects the orders,
height degree and constant before any moving atom table or Fourier mode.
The two literal tables then construct their own side frames, comparison
dictionary, exceptional charts and atomic controls. Their original
profile seminorms, actual divisor phases and physical row restrictions
are retained. The original cutoff loss remains explicit.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralExceptionalCharts CanonicalLiteralExceptionalWindows

variable {K : Type} [Field K] [NumberField K]

def characterCatalogue (ψ : HeckeCharacter K) (theta : Finset (HeckeCharacter K))
    (i : CanonicalLiteralExceptionalCharacters.CatalogueIndex theta) : HeckeCharacter K :=
  CanonicalLiteralExceptionalCharacters.background ψ i.1 * i.2.val

@[simp] theorem coefficient_characterCatalogue (ψ : HeckeCharacter K)
    (theta : Finset (HeckeCharacter K))
    (i : CanonicalLiteralExceptionalCharacters.CatalogueIndex theta) :
    CanonicalExceptionalVolume.coefficient (characterCatalogue ψ theta i) =
      CanonicalLiteralExceptionalCharacters.catalogue ψ theta i := rfl

/-- Only the original one-character smoothed ideal series is primitive.
No source estimate, volume-control catalogue or terminal bound is a field. -/
structure VolumePrimitive (ψ : HeckeCharacter K)
    (theta : Finset (HeckeCharacter K)) (window : Set ℝ) where
  compact : IsCompact window
  positive : window ⊆ Set.Ioi 0
  density : CanonicalLiteralExceptionalCharacters.CatalogueIndex theta → 𝓢(ℝ, ℂ) → ℂ
  remainder : CanonicalLiteralExceptionalCharacters.CatalogueIndex theta →
    Seminorm ℂ (𝓢(ℝ, ℂ))
  continuous : ∀ i, Continuous (remainder i)
  volume : ∀ i (φ : 𝓢(ℝ, ℂ)) (X : ℝ), 0 < X →
    ‖(∑' I : Ideal (𝓞 K),
        CanonicalExceptionalVolume.coefficient (characterCatalogue ψ theta i) I *
          φ ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density i φ‖ ≤ remainder i φ

section UniformVolume

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ψ : HeckeCharacter K} {theta : Finset (HeckeCharacter K)} {window : Set ℝ}
variable (primitive : VolumePrimitive ψ theta window)
variable (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent)

include A σ η hS

private def centeredExistence :=
  CanonicalExceptionalTerminal.exists_original_magnitude_terminal_with_cutoff
    (A := A) (σ := σ) (η := η) (hS := hS) (V := WithLp 2 (ℝ × ℝ))
    (characterCatalogue ψ theta) primitive.density primitive.remainder
    primitive.continuous primitive.volume window primitive.compact primitive.positive
    ε maskExponent hε hmask

def centeredOrders : Finset (ℕ × ℕ) :=
  (centeredExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose

def centeredOrder : ℕ :=
  (centeredExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.2.choose

def centeredConstant : ℝ :=
  (centeredExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.2.choose_spec.choose

theorem centeredOrders_zero :
    (0, 0) ∈ centeredOrders (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExponent hε hmask :=
  (centeredExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.1

theorem centeredConstant_pos :
    0 < centeredConstant (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExponent hε hmask :=
  (centeredExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.2.choose_spec.choose_spec.1

private def centeredEstimate :=
  (centeredExistence (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExponent hε hmask).choose_spec.2.choose_spec.choose_spec.2

private def ordinaryExistence :=
  CanonicalExceptionalTerminal.exists_original_ordinary_magnitude_terminal_with_cutoff
    (A := A) (σ := σ) (η := η) (hS := hS) (V := WithLp 2 (ℝ × ℝ))
    (characterCatalogue ψ theta) primitive.density primitive.remainder
    primitive.continuous primitive.volume window primitive.compact primitive.positive

def ordinaryOrders : Finset (ℕ × ℕ) :=
  (ordinaryExistence (A := A) (σ := σ) (η := η) (hS := hS) primitive).choose

def ordinaryConstant : ℝ :=
  (ordinaryExistence (A := A) (σ := σ) (η := η) (hS := hS) primitive).choose_spec.2.choose

theorem ordinaryOrders_zero :
    (0, 0) ∈ ordinaryOrders (A := A) (σ := σ) (η := η) (hS := hS) primitive :=
  (ordinaryExistence (A := A) (σ := σ) (η := η) (hS := hS) primitive).choose_spec.1

theorem ordinaryConstant_pos :
    0 < ordinaryConstant (A := A) (σ := σ) (η := η) (hS := hS) primitive :=
  (ordinaryExistence (A := A) (σ := σ) (η := η) (hS := hS) primitive).choose_spec.2.choose_spec.1

private def ordinaryEstimate :=
  (ordinaryExistence (A := A) (σ := σ) (η := η) (hS := hS) primitive).choose_spec.2.choose_spec.2

end UniformVolume

section OriginalSide

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable {ω ψ : HeckeCharacter K} (parent : MomentData K ω ψ)
variable (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)

def historySecondInput {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
    (H : CanonicalLiteralExceptionalPaidScales.History (σ := σ) P R d) :
    CanonicalLiteralRectangles.Atoms (K := K) H.first.keep.card :=
  H.original.secondInput (σ := σ) H.first P R H.power H.firstFixed H.poolFixed H.unitFixed
    H.firstElement H.poolElement H.unitElement H.first_generates H.pool_generates
    H.unit_generates H.firstTilt H.secondTilt

/-- The coefficient table used by the actual factor-free source. The
original deletion remains in every character, and redistribution is
performed before its common scalar is extracted. Only the unchanged
formal scales are read from the numerical history. -/
def historyActualSecondInput {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
    (H : CanonicalLiteralExceptionalPaidScales.History (σ := σ) P R d) :
    CanonicalLiteralRectangles.Atoms (K := K) H.first.keep.card :=
  ((historySecondInput P R H).deleteMask extra).redistributeNormFactors
    H.firstTilt H.secondTilt

section RedistributedHistory

variable {n : ℕ} (original : CanonicalLiteralRectangles.Atoms (K := K) n)
variable {firstSupport : Finset (Ideal (𝓞 K))}
variable (first : SupportCartesianBranch original.plain₁ original.plain₂ original.slots firstSupport)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
local notation "bare" => original.secondInput (σ := σ) first P R power firstFixed
  poolFixed unitFixed firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂
local notation "actual" => (bare.deleteMask extra).redistributeNormFactors δ₁ δ₂
variable {secondSupport : Finset (Ideal (𝓞 K))}
variable (second : SupportCartesianBranch actual.plain₁ actual.plain₂ actual.slots secondSupport)
variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal) (count : second.keep.card = atlas.slotCount)
variable (scalar : ℂ) (balance : Bool → ℝ)

/-- The actual redistributed source supplies its numerical history.
Deletion and profile-factor redistribution change neither its scales
nor its selected support branch. They are not removed from any actual
coefficient or common scalar. -/
def redistributedHistory : CanonicalLiteralExceptionalPaidScales.History (σ := σ) P R
    ((((actual.extract second).onAtlas atlas count).scale scalar).balancePlain balance) where
  originalCount := n
  original := original
  firstSupport := firstSupport
  first := first
  power := power
  firstFixed := firstFixed
  poolFixed := poolFixed
  unitFixed := unitFixed
  firstElement := firstElement
  poolElement := poolElement
  unitElement := unitElement
  first_generates := hfirst
  pool_generates := hpool
  unit_generates := hunit
  firstTilt := δ₁
  secondTilt := δ₂
  secondSupport := secondSupport
  second := second
  base_eq := by
    change ((actual.extract second).onAtlas atlas count).base = original.base
    cases count
    rfl
  scale_eq := by
    rw [CanonicalLiteralRectangles.Atoms.balancePlain_scaleProduct,
      CanonicalLiteralRectangles.Atoms.scale_scaleProduct,
      CanonicalLiteralRectangles.Atoms.onAtlas_scaleProduct]
    rfl

end RedistributedHistory

/-- The actual atom-level inputs for one side. These are the existing
literal table, its original representatives/characters/supports and the
actual allocation label. There is no completed frame or child bound. -/
structure OriginalSide (firstSupport secondSupport : Finset (Ideal (𝓞 K)))
    (window : Set ℝ) (Z : ℝ) where
  count : ℕ
  atoms : CanonicalLiteralRectangles.Atoms (K := K) count
  history : CanonicalLiteralExceptionalPaidScales.History (σ := σ) P R atoms
  count_eq : count = history.second.keep.card
  base_eq : atoms.base = Z
  profiles : atoms.ProfileData
  model : profiles.SchwartzModel window
  recipe : CanonicalLiteralActualCharacters.Recipe P R F parent oldMoving correction
    remaining extra atoms
  commonRecipe : CanonicalLiteralActualCharacters.Recipe P R F parent oldMoving correction
    remaining extra (historyActualSecondInput P R extra history)
  left_scale_eq : ∀ r, atoms.scale₁ r = history.original.scale₁ r /
    idealNorm K (history.first.plainDivisor₁ * history.second.plainDivisor₁)
  right_scale_eq : ∀ r, atoms.scale₂ r = history.original.scale₂ r /
    idealNorm K (history.first.plainDivisor₂ * history.second.plainDivisor₂)
  gauss_eq : extraGaussScale atoms.gauss₁ atoms.gauss₂ atoms.gaussSlot =
    extraGaussScale (historySecondInput P R history).gauss₁
      (historySecondInput P R history).gauss₂ (historySecondInput P R history).gaussSlot
  original_gauss : extraGaussScale history.original.gauss₁
    history.original.gauss₂ history.original.gaussSlot = 1
  support : atoms.SupportData ((primeSupport A.cS ∪ firstSupport) ∪ secondSupport)
  ray : (PUnit.{1} × PUnit.{1}) →* Circle
  ideal : AllocationColumn K count → A.Exterior
  ideal_eq : ∀ i ∈ childCartesianColumns atoms.plain₁ atoms.plain₂ atoms.slots,
    (ideal i).val = allocationColumnIdeal i
  firstSign : ℝ
  firstSign_le : |firstSign| ≤ 1
  divisor : Ideal (𝓞 K)
  selection : primeSupport divisor → Finset (Fin (count + 2))
  nonempty : (pairedAllocatedColumns divisor selection atoms.plain₁ atoms.plain₂ atoms.slots
    id id HeightOneSpectrum.asIdeal).Nonempty
  squarefree : Squarefree divisor
  selection_mem : selection ∈ AllocationMass.idealAllocations divisor (count + 2)

variable {P R F parent oldMoving correction remaining extra}
variable {firstSupport secondSupport : Finset (Ideal (𝓞 K))} {window : Set ℝ} {Z : ℝ}
variable (D : OriginalSide (σ := σ) P R F parent oldMoving correction remaining extra
  firstSupport secondSupport window Z)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι) (C : A.GeneralArithmeticContext σ η hS)
variable (side : SecondColumnSide)

def OriginalSide.frame : SecondSideFrame (V := WithLp 2 (ℝ × ℝ)) C S PUnit.{1} side D.count :=
  (D.atoms.factors S side D.ray D.ideal D.ideal_eq D.firstSign false).frame
    C D.divisor D.selection D.nonempty

def OriginalSide.comparison : SecondCoefficientComparison (D.frame S C side).dictionary :=
  CanonicalLiteralExceptionalFactory.comparison D.atoms (side.phase PUnit.{1} D.ray)

def OriginalSide.leftProfile (ξ : WithLp 2 (ℝ × ℝ)) : 𝓢(ℝ, ℂ) :=
  profile D.firstSign (orientedMode side.literalNegative ξ)
    ((D.frame S C side).allocation.plainDivisor 0) (D.model.left false)

def OriginalSide.rightProfile (ξ : WithLp 2 (ℝ × ℝ)) : 𝓢(ℝ, ℂ) :=
  profile D.firstSign (orientedMode side.literalNegative ξ)
    ((D.frame S C side).allocation.plainDivisor (Fin.succ 0)) (D.model.right false)

def OriginalSide.scales (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude) :
    ExceptionalAtomicScales (D.frame S C side).allocation :=
  CanonicalLiteralExceptionalAtoms.scales D.atoms S C side D.ray D.ideal D.ideal_eq
    D.firstSign D.divisor D.selection D.nonempty annulus amplitude hannulus hamplitude

def OriginalSide.targetTotal (originalTotal : ℝ) : ℝ :=
  originalTotal - idealLogLength Z D.history.firstIdeal - idealLogLength Z D.history.secondIdeal

def OriginalSide.paidScales (originalTotal annulus amplitude : ℝ) (cap : ℕ)
    (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude) :
    ExceptionalAtomicScales (D.frame S C side).allocation :=
  CanonicalLiteralExceptionalPaidScales.scales (D.frame S C side).allocation Z
    (D.targetTotal originalTotal) D.atoms.length (fun i => (D.atoms.length_pos i).le)
    annulus amplitude cap hannulus hamplitude

theorem OriginalSide.history_window (originalTotal annulus : ℝ) (cap : ℕ)
    (hannulus : 1 ≤ annulus) (hcap : D.history.originalCount ≤ cap)
    (hprime : D.history.original.PrimeNormWindow annulus)
    (horiginal : D.history.original.scaleProduct false = Z ^ originalTotal) :
    D.atoms.scale₁ false * D.atoms.scale₂ false * (∏ i, Z ^ D.atoms.length i) ≤
      (annulus ^ cap) ^ 2 * Z ^ D.targetTotal originalTotal := by
  have hz : D.history.original.base = Z := D.history.base_eq.symm.trans D.base_eq
  have ho : D.history.original.scaleProduct false = D.history.original.base ^ originalTotal := by
    simpa only [hz] using horiginal
  have hw := D.history.window annulus hannulus cap hcap hprime originalTotal ho
  simpa only [CanonicalLiteralRectangles.Atoms.scaleProduct, D.base_eq,
    OriginalSide.targetTotal] using hw

theorem OriginalSide.count_le (cap : ℕ) (hcap : D.history.originalCount ≤ cap) :
    D.count ≤ cap := by
  rw [D.count_eq]
  exact (by simpa only [Fintype.card_fin] using Finset.card_le_univ D.history.second.keep).trans
    ((by simpa only [Fintype.card_fin] using Finset.card_le_univ D.history.first.keep).trans hcap)

theorem OriginalSide.scales_eq (annulus amplitude : ℝ)
    (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude) :
    D.scales S C side annulus amplitude hannulus hamplitude =
      (D.frame S C side).allocation.originalAtomicScales Z
        (Real.log (D.atoms.scale₁ false * D.atoms.scale₂ false) / Real.log Z)
        D.atoms.length (fun i => (D.atoms.length_pos i).le)
        (fun _ => annulus) (fun _ => amplitude) (fun _ => hannulus) (fun _ => hamplitude) := by
  unfold OriginalSide.scales CanonicalLiteralExceptionalAtoms.scales
  rw [D.base_eq]

theorem OriginalSide.profile_supports (ξ : WithLp 2 (ℝ × ℝ)) :
    tsupport (D.leftProfile S C side ξ) ⊆ window ∧
      tsupport (D.rightProfile S C side ξ) ⊆ window :=
  ⟨(profile_support _ _ _ _).trans (D.model.left_support false),
    (profile_support _ _ _ _).trans (D.model.right_support false)⟩

theorem OriginalSide.profile_seminorms (ξ : WithLp 2 (ℝ × ℝ)) (orders : Finset (ℕ × ℕ)) :
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (D.leftProfile S C side ξ) =
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (D.model.left false) ∧
      orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (D.rightProfile S C side ξ) =
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (D.model.right false) :=
  ⟨profile_seminorm _ _ _ _ _, profile_seminorm _ _ _ _ _⟩

theorem OriginalSide.comparison_product {a : RealParameters} {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain true parent a Z Y₁ Y₂ floor padding)
    (hleft : ∀ r, D.history.original.scale₁ r = if r then Y₁ else Z ^ a.n₁)
    (hright : ∀ r, D.history.original.scale₂ r = if r then Y₂ else Z ^ a.n₂) :
    D.atoms.scale₁ true * D.atoms.scale₂ true = D.atoms.scale₁ false * D.atoms.scale₂ false := by
  rw [D.left_scale_eq true, D.right_scale_eq true, D.left_scale_eq false,
    D.right_scale_eq false, hleft true, hright true, hleft false, hright false]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [div_mul_div_comm, div_mul_div_comm, domain.comparison_product_eq_power rfl,
    Real.rpow_add (zero_lt_one.trans domain.scale)]

private theorem frozen_left_dvd {n : ℕ} (I J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (keep : Finset (Fin n)) (p : Fin n → HeightOneSpectrum (𝓞 K)) :
    I.val ∣ frozenSourceIdeal I J keep p := by
  refine ⟨J.val * ∏ i ∈ Finset.univ \ keep, (p i).asIdeal, ?_⟩
  exact mul_assoc _ _ _

private theorem frozen_right_dvd {n : ℕ} (I J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (keep : Finset (Fin n)) (p : Fin n → HeightOneSpectrum (𝓞 K)) :
    J.val ∣ frozenSourceIdeal I J keep p := by
  refine ⟨I.val * ∏ i ∈ Finset.univ \ keep, (p i).asIdeal, ?_⟩
  change I.val * J.val * _ = J.val * (I.val * _)
  ac_rfl

theorem OriginalSide.preDivisors_dvd :
    (D.history.first.plainDivisor₁ * D.history.second.plainDivisor₁).val ∣
        D.history.firstIdeal * D.history.secondIdeal ∧
      (D.history.first.plainDivisor₂ * D.history.second.plainDivisor₂).val ∣
        D.history.firstIdeal * D.history.secondIdeal :=
  ⟨mul_dvd_mul (frozen_left_dvd _ _ _ _) (frozen_left_dvd _ _ _ _),
    mul_dvd_mul (frozen_right_dvd _ _ _ _) (frozen_right_dvd _ _ _ _)⟩

/-- The true divisor loss is paid by the original frozen-prime
annulus. No final allocation lower-bound inequality is assumed. -/
theorem OriginalSide.divisor_window (annulus slotLoss : ℝ) (hZ : 1 < Z)
    (hprime : D.atoms.PrimeNormWindow annulus) (hannulus : annulus ≤ Z ^ (2 * slotLoss)) :
    idealLogLength Z D.divisor - (D.frame S C side).allocation.rawExtractionLength Z D.atoms.length ≤
      ∑ i ∈ Finset.univ \ (D.frame S C side).allocation.keep, slotLoss := by
  let B := (D.frame S C side).allocation
  have hd := B.divisor_dvd_frozenIdeal D.squarefree D.selection_mem
  have hD : B.divisor ≠ 0 := by
    intro he
    rw [he, zero_dvd_iff] at hd
    exact B.frozenIdeal_ne_zero hd
  apply B.divisor_window_of_prime_windows Z hZ D.atoms.length (fun _ => slotLoss)
    (idealLogLength Z D.divisor) D.squarefree D.selection_mem
      (rpow_idealLogLength Z hZ B.divisor hD).le
  intro i hi
  have hw := B.witness_mem
  rw [WholeAllocation.paired_allocated_columns_eq_filter] at hw
  have hp : B.witness.2 i ∈ D.atoms.slots i :=
    Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hw).1).2 i
  have hnorm := hprime i (B.witness.2 i) hp
  rw [D.base_eq] at hnorm
  apply hnorm.trans
  calc
    annulus * Z ^ D.atoms.length i ≤ Z ^ (2 * slotLoss) * Z ^ D.atoms.length i :=
      mul_le_mul_of_nonneg_right hannulus
        (Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
    _ = Z ^ (D.atoms.length i + 2 * slotLoss) := by
      rw [Real.rpow_add (zero_lt_one.trans hZ)]
      ring

end OriginalSide

section ActualRows

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {Dmask : (∅ : Finset (HeightOneSpectrum A.R)).powerset}
variable (chart : SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C left right
  profiles finiteTest radius Dmask.val)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (hclass : chart.NonunitLabelStable) (hsector : chart.SectorLabelStable P)
variable (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable {ω ψ : HeckeCharacter K}
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K)

local notation "Orbit" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "Joint" => WithLp 2 (ℝ × ℝ)
local notation "rawRows" => chart.actualRows ∅ X hX label
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "sector" => chart.originalSector P ∅ X hX label
local notation "characters" => rawRows.literalFiniteCharacters C P R F oldMoving
  correction pattern sector parent.theta

variable {kCommonL kCommonR : ℕ}
variable (leftAtoms : FrozenSourceAtoms A σ Orbit rawRows.rows kCommonL)
variable (rightAtoms : FrozenSourceAtoms A σ Orbit rawRows.rows kCommonR)
variable (thetaPair : parent.theta × parent.theta)

local notation "S" => CanonicalLiteralExceptionalFactory.rows chart P R X hX label F
  parent oldMoving correction leftAtoms rightAtoms thetaPair

variable (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (firstSupport : Finset (Ideal (𝓞 K))) (hfirst : ∀ p ∈ firstSupport, Prime p)
variable (hextra : extra = literalDeletionIdeal firstSupport hfirst)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable {window : Set ℝ} {Z : ℝ}

local notation "Input" => OriginalSide (σ := σ) P R F parent oldMoving correction remaining extra
  firstSupport (primeSupport (primePowerProduct b.primes b.leftMultiplicity).val) window Z

variable (D : Input) (side : SecondColumnSide)
local notation "entry" => CanonicalLiteralExceptionalCharacters.catalogue ψ parent.theta
  (CanonicalLiteralExceptionalCharacters.selectedIndex parent
    (CanonicalLiteralExceptionalFactory.thetaForSide parent thetaPair side))

include hclass hsector hcorr hfirst hextra hone hroot hemb in
def OriginalSide.actualCentered
    (hc : SamePlainProfiles D.model)
    (hscale : D.atoms.scale₁ true * D.atoms.scale₂ true =
      D.atoms.scale₁ false * D.atoms.scale₂ false)
    (ξ : Joint) (h : S.exceptionalRows characters) :
    (D.frame S C side).source.ExceptionalAt (σ := σ)
      (D.comparison S C side).scale₁ (D.comparison S C side).scale₂
      (fun _ => (D.comparison S C side).leftWeight)
      (fun _ => (D.comparison S C side).rightWeight)
      entry (D.leftProfile S C side ξ) (D.rightProfile S C side ξ) ξ h.val :=
  CanonicalLiteralExceptionalFactory.centeredFamily chart P R hclass hsector X hX label F
    parent oldMoving correction leftAtoms rightAtoms thetaPair D.atoms D.model hcorr
    remaining extra D.recipe firstSupport hfirst hextra D.support hone hroot hemb side D.ray
    D.ideal D.ideal_eq D.firstSign D.divisor D.selection D.nonempty hc hscale ξ h.val

include hclass hsector hcorr hfirst hextra hone hroot hemb in
def OriginalSide.actualOrdinary (ξ : Joint) (h : S.exceptionalRows characters) :
    (D.frame S C side).source.OrdinaryExceptionalAt (σ := σ)
      entry (D.leftProfile S C side ξ) (D.rightProfile S C side ξ) ξ h.val :=
  CanonicalLiteralExceptionalFactory.ordinaryFamily chart P R hclass hsector X hX label F
    parent oldMoving correction leftAtoms rightAtoms thetaPair D.atoms D.model hcorr
    remaining extra D.recipe firstSupport hfirst hextra D.support hone hroot hemb side D.ray
    D.ideal D.ideal_eq D.firstSign D.divisor D.selection D.nonempty ξ h.val

local notation "centered" => OriginalSide.actualCentered chart P R hclass hsector X hX
  label F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb D side
local notation "ordinary" => OriginalSide.actualOrdinary chart P R hclass hsector X hX
  label F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb D side

variable (annulus amplitude : ℝ) (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude)
variable (hprime : D.atoms.PrimeNormWindow annulus)
variable (hprofile : ∀ i, SchwartzMap.seminorm ℂ 0 0 (D.model.slot i) ≤ amplitude)

include hprime hprofile in
def OriginalSide.actualCenteredAtoms
    (hc : SamePlainProfiles D.model)
    (hscale : D.atoms.scale₁ true * D.atoms.scale₂ true =
      D.atoms.scale₁ false * D.atoms.scale₂ false)
    (ξ : Joint) (h : S.exceptionalRows characters) :
    (centered hc hscale ξ h).source.AtomicControl Z
      (D.scales S C side annulus amplitude hannulus hamplitude) := by
  have hp : (centered hc hscale ξ h).source.AtomicControl D.atoms.base
      (D.scales S C side annulus amplitude hannulus hamplitude) :=
    CanonicalLiteralExceptionalFactory.centeredAtomicControl chart P R hclass hsector X hX
      label F parent oldMoving correction leftAtoms rightAtoms thetaPair D.atoms D.model
      hcorr remaining extra D.recipe firstSupport hfirst hextra D.support hone hroot hemb
      side D.ray D.ideal D.ideal_eq D.firstSign D.divisor D.selection D.nonempty
      annulus amplitude hannulus hamplitude hprime hprofile hc hscale ξ h.val
  exact (congrArg (fun z => (centered hc hscale ξ h).source.AtomicControl z
    (D.scales S C side annulus amplitude hannulus hamplitude)) D.base_eq).mp hp

include hprime hprofile in
def OriginalSide.actualOrdinaryAtoms (ξ : Joint) (h : S.exceptionalRows characters) :
    (ordinary ξ h).source.AtomicControl Z
      (D.scales S C side annulus amplitude hannulus hamplitude) := by
  have hp : (ordinary ξ h).source.AtomicControl D.atoms.base
      (D.scales S C side annulus amplitude hannulus hamplitude) :=
    CanonicalLiteralExceptionalFactory.ordinaryAtomicControl chart P R hclass hsector X hX
      label F parent oldMoving correction leftAtoms rightAtoms thetaPair D.atoms D.model
      hcorr remaining extra D.recipe firstSupport hfirst hextra D.support hone hroot hemb
      side D.ray D.ideal D.ideal_eq D.firstSign D.divisor D.selection D.nonempty
      annulus amplitude hannulus hamplitude hprime hprofile ξ h.val
  exact (congrArg (fun z => (ordinary ξ h).source.AtomicControl z
    (D.scales S C side annulus amplitude hannulus hamplitude)) D.base_eq).mp hp

variable (originalTotal : ℝ) (cap : ℕ)
variable (horiginalCap : D.history.originalCount ≤ cap)
variable (horiginalPrime : D.history.original.PrimeNormWindow annulus)
variable (horiginalProduct : D.history.original.scaleProduct false = Z ^ originalTotal)

include hprime hprofile horiginalCap horiginalPrime horiginalProduct in
/-- The final source receives the true paid atom budget. Its final
scale window is proved through the stored actual extraction history. -/
def OriginalSide.actualCenteredPaidAtoms (hZ : 1 < Z)
    (hc : SamePlainProfiles D.model)
    (hscale : D.atoms.scale₁ true * D.atoms.scale₂ true =
      D.atoms.scale₁ false * D.atoms.scale₂ false)
    (ξ : Joint) (h : S.exceptionalRows characters) :
    (centered hc hscale ξ h).source.AtomicControl Z
      (D.paidScales S C side originalTotal annulus amplitude cap hannulus hamplitude) := by
  have original := OriginalSide.actualCenteredAtoms chart P R hclass hsector X hX
    label F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
    firstSupport hfirst hextra hone hroot hemb D side annulus amplitude hannulus hamplitude
    hprime hprofile hc hscale ξ h
  rw [D.scales_eq S C side annulus amplitude hannulus hamplitude] at original
  exact CanonicalLiteralExceptionalPaidScales.control (centered hc hscale ξ h).source
    Z (D.targetTotal originalTotal) D.atoms.length (fun i => (D.atoms.length_pos i).le)
    annulus amplitude cap hannulus hamplitude hZ
    (D.atoms.scale₁ false) (D.atoms.scale₂ false)
    (D.atoms.scale₁_pos false) (D.atoms.scale₂_pos false) original
    (D.history_window originalTotal annulus cap hannulus horiginalCap horiginalPrime horiginalProduct)

include hprime hprofile horiginalCap horiginalPrime horiginalProduct in
def OriginalSide.actualOrdinaryPaidAtoms (hZ : 1 < Z)
    (ξ : Joint) (h : S.exceptionalRows characters) :
    (ordinary ξ h).source.AtomicControl Z
      (D.paidScales S C side originalTotal annulus amplitude cap hannulus hamplitude) := by
  have original := OriginalSide.actualOrdinaryAtoms chart P R hclass hsector X hX
    label F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
    firstSupport hfirst hextra hone hroot hemb D side annulus amplitude hannulus hamplitude
    hprime hprofile ξ h
  rw [D.scales_eq S C side annulus amplitude hannulus hamplitude] at original
  exact CanonicalLiteralExceptionalPaidScales.control (ordinary ξ h).source
    Z (D.targetTotal originalTotal) D.atoms.length (fun i => (D.atoms.length_pos i).le)
    annulus amplitude cap hannulus hamplitude hZ
    (D.atoms.scale₁ false) (D.atoms.scale₂ false)
    (D.atoms.scale₁_pos false) (D.atoms.scale₂_pos false) original
    (D.history_window originalTotal annulus cap hannulus horiginalCap horiginalPrime horiginalProduct)

section Pair

variable (LD RD : Input)
variable (hleftCommon : leftAtoms.ideal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hrightCommon : rightAtoms.ideal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (rowProfileBound : ℝ) (hrowProfileBound : 0 ≤ rowProfileBound)
variable (hrowProfile : ∀ q ∈ rawRows.rows, ‖chart.weight q‖ ≤ rowProfileBound)
variable {a : RealParameters} {step : ℝ}
variable (first : OriginalNominalGeometry (K := K) a Z step)
variable (slotLoss firstProfile : ℝ)

local notation "mass" => CanonicalLiteralExceptionalArithmetic.actualMass chart P R hclass
  X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
  hleftCommon hrightCommon rowProfileBound hrowProfileBound hrowProfile
local notation "G" => CanonicalLiteralExceptionalNumbers.geometry chart X hX label first
local notation "LF" => LD.frame S C .left
local notation "RF" => RD.frame S C .right
local notation "EL" => LD.comparison S C .left
local notation "ER" => RD.comparison S C .right
local notation "rL" => LF.allocation.rawExtractionLength Z LD.atoms.length
local notation "rR" => RF.allocation.rawExtractionLength Z RD.atoms.length
local notation "slotError" => ∑ i ∈ Finset.univ \ RF.allocation.keep, slotLoss
local notation "n" => CanonicalLiteralExceptionalNumbers.numbers chart P R hclass X hX label F
  parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
  rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile

variable (hfirstL : LD.history.firstIdeal = (first.ideals.first * first.tag.extractionIdeal).val)
variable (hfirstR : RD.history.firstIdeal = (first.ideals.first * first.tag.extractionIdeal).val)
variable (hsecondL : LD.history.secondIdeal = (primePowerProduct b.primes b.leftMultiplicity).val)
variable (hsecondR : RD.history.secondIdeal = (primePowerProduct b.primes b.rightMultiplicity).val)
variable (hplaces : CanonicalLiteralExceptionalArithmetic.thetaBadPrimes parent.theta ⊆ A.Sf)
variable (hscalar : (historyActualSecondInput P R extra LD.history).commonScalar
  LD.history.second ≠ 0)

include hclass hsector hcorr hplaces hscalar hsecondL in
/-- The original common branch proves the arithmetic classification.
No sixth-power class or valuation-divisibility certificate is supplied. -/
theorem actual_classification :
    ∃ base : HeckeGeneral.Analysis.NonzeroIdeal K,
      (∀ h : S.live, ∃ q : Ideal (𝓞 K),
        (S.extractedRow C h).ideal.val = base.val * q ^ 6) ∧
      (∀ h : S.live, ∀ i ∈ multiplicityOneNonunitPrimes C S.primes S.leftMultiplicity
        S.rightMultiplicity (S.frequency h.val),
        6 ∣ (UniqueFactorizationMonoid.normalizedFactors
          (S.originalIdeal h.val).val).count (S.primes i).val.asIdeal) := by
  let rowMap := CanonicalLiteralExceptionalFactory.originalRow chart P R hclass hsector
    X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
  let selected := (Finset.univ : Finset S.live).image rowMap
  have hmem (h : S.live) : rowMap h ∈ selected :=
    Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩
  have htheta (h : S.live) :
      S.literalCharacter C P R F oldMoving correction pattern sector
        (rowMap h).val.val.val = thetaPair.1.val :=
    CanonicalLiteralExceptionalFactory.character_on_class chart P R X hX label F
      parent oldMoving correction leftAtoms rightAtoms thetaPair .left h
  have hcommon : frozenSourceIdeal LD.history.second.plainDivisor₁
      LD.history.second.plainDivisor₂ LD.history.second.keep LD.history.second.witness.2 =
        (primePowerProduct S.primes S.leftMultiplicity).val := hsecondL
  obtain ⟨base, _hfree, hfactor, hvaluation⟩ :=
    CanonicalLiteralExceptionalClassification.exists_actual_classification P R F
      parent oldMoving correction hcorr remaining extra LD.commonRecipe LD.history.second
      C S pattern sector (CanonicalLiteralPrimitiveCharacters.primitiveCharacterLaws P R)
      (CanonicalLiteralExceptionalArithmetic.theta_unramified parent.theta hplaces)
      hcommon hscalar selected thetaPair.1
  exact ⟨base, fun h => hfactor (rowMap h) (hmem h) (htheta h),
    fun h => hvaluation (rowMap h) (hmem h) (htheta h)⟩

private theorem first_extraction_length :
    idealLogLength Z (first.ideals.first * first.tag.extractionIdeal).val =
      G.skeleton.c + G.skeleton.w := by
  change idealLogLength Z (first.ideals.first.val * first.tag.extractionIdeal.val) = _
  rw [original_plain_log_mul Z _ _ (nonZeroDivisors.coe_ne_zero _)
    (nonZeroDivisors.coe_ne_zero _), first.tag.extractionIdeal_length Z]
  rfl

local notation "UL" => LD.paidScales S C .left G.skeleton.A annulus amplitude cap hannulus hamplitude
local notation "UR" => RD.paidScales S C .right G.skeleton.A annulus amplitude cap hannulus hamplitude

include hfirstL hfirstR hsecondL hsecondR in
/-- The source's paid atomic exponent is now exactly the original
ledger exponent. The only payment was the fixed annulus constant. -/
theorem paid_atom_exponent :
    UL.exponent + UR.exponent = n.Aexp - n.c - n.w - n.b₂ - n.r₁ - n.r₂ := by
  simp only [OriginalSide.paidScales, CanonicalLiteralExceptionalPaidScales.scales_exponent]
  change (LD.targetTotal G.skeleton.A / 2 - rL) +
    (RD.targetTotal G.skeleton.A / 2 - rR) =
      G.skeleton.A - G.skeleton.c - G.skeleton.w -
        ((idealLogLength Z (primePowerProduct b.primes b.leftMultiplicity).val +
          idealLogLength Z (primePowerProduct b.primes b.rightMultiplicity).val) / 2) - rL - rR
  unfold OriginalSide.targetTotal
  rw [hfirstL, hfirstR, hsecondL, hsecondR, first_extraction_length chart X hX label first]
  ring

section CenteredWindows

variable {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain true parent a Z Y₁ Y₂ floor padding)
variable (hseedLeftL : ∀ r, LD.history.original.scale₁ r = if r then Y₁ else Z ^ a.n₁)
variable (hseedRightL : ∀ r, LD.history.original.scale₂ r = if r then Y₂ else Z ^ a.n₂)
variable (hcL : SamePlainProfiles LD.model)

local notation "prodL" => LD.comparison_product domain hseedLeftL hseedRightL
local notation "TL" => OriginalSide.actualCentered chart P R hclass hsector X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb LD .left hcL prodL

variable (horder : idealLogLength Z (primePowerProduct b.primes b.leftMultiplicity).val ≤
  idealLogLength Z (primePowerProduct b.primes b.rightMultiplicity).val)

include hfirstL hsecondL horder in
/-- The actual two pre-divisors belong to the smaller original
common ideal. The centered quarter-width minimum then follows from
the original domain, including the final allocated divisors. -/
theorem centered_minimum (ξ : Joint) (h : S.exceptionalRows characters) :
    Z ^ ((a.m + a.q) / 4 - G.centeredExtractionLength - rL) ≤ (TL ξ h).source.lower := by
  have hchoose : G.centeredSecondIdeal = G.ideals.second := by
    apply if_pos
    exact horder
  have hcommon : LD.history.firstIdeal * LD.history.secondIdeal =
      G.centeredCommonIdeal.val := by
    rw [hfirstL, hsecondL]
    change _ = (G.ideals.first * G.tag.extractionIdeal * G.centeredSecondIdeal).val
    rw [hchoose]
    rfl
  have hp := LD.preDivisors_dvd
  rw [hcommon] at hp
  have hmin := G.fourPlain_minimum_window_of_domain LF.allocation domain
    (LD.history.first.plainDivisor₁ * LD.history.second.plainDivisor₁)
    (LD.history.first.plainDivisor₂ * LD.history.second.plainDivisor₂)
    hp.1 hp.2 LD.atoms.length (fun i => (LD.atoms.length_pos i).le)
  have hf := CanonicalLiteralExceptionalWindows.centered_fields P R F parent oldMoving
    correction hcorr C S pattern sector remaining extra hone hroot hemb
    (CanonicalLiteralExceptionalFactory.originalRow chart P R hclass hsector X hX label
      F parent oldMoving correction leftAtoms rightAtoms thetaPair h.val)
    LD.recipe LD.model firstSupport hfirst hextra b.left_positive b.right_positive LD.support
    .left LD.ray LD.ideal LD.ideal_eq LD.firstSign LD.divisor LD.selection LD.nonempty
    thetaPair.1 (CanonicalLiteralExceptionalFactory.character_on_class chart P R X hX
      label F parent oldMoving correction leftAtoms rightAtoms thetaPair .left h.val)
    hcL prodL ξ
  rw [hf.2.2, LD.left_scale_eq false, LD.right_scale_eq false,
    LD.left_scale_eq true, LD.right_scale_eq true, hseedLeftL false, hseedRightL false,
    hseedLeftL true, hseedRightL true]
  simpa only [Bool.false_eq_true, if_false, if_true] using hmin

variable (columnLoss cutoffExponent widthMax : ℝ)
variable (hZ : 1 < Z) (hstep : 0 ≤ step)
variable (hwidth : a.m + a.q ≤ widthMax)
variable (hthreshold : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z)
variable (hradius : radius = CanonicalRowBall.gaussRadius first.retainedScale Z first.enlargement
  first.retainedScale_pos (zero_lt_one.trans hZ))
variable (hcutoff : X ≤ Z ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤
    Z ^ (2 * (first.skeleton.A - first.skeleton.c - first.skeleton.w + columnLoss)))
variable (hold : A.exteriorNorm ((F.moving P R oldMoving).effectiveFullSupport
  (remaining * extra)) ≤
    Z ^ (a.q + G.skeleton.R + G.skeleton.E + G.skeleton.wo + widthMax))

include hstep hwidth hthreshold hradius hcutoff hproduct hold in
/-- A fixed parent box bounds the actual complete mask. Its initial
bad-prime ideal costs one fixed threshold and one exponent, while the
original physical cutoff cost remains explicit. The full first deletion
is charged to the additional fixed width, including its passive primes. -/
theorem centered_mask (ξ : Joint) (h : S.exceptionalRows characters) :
    (Ideal.absNorm (TL ξ h).source.mask : ℝ) ≤
      Z ^ CanonicalLiteralExceptionalPhysicalBox.maskExponent
        widthMax columnLoss cutoffExponent := by
  have hradius' : radius = CanonicalRowBall.gaussRadius first.retainedScale
      LD.atoms.base first.enlargement first.retainedScale_pos
        (zero_lt_one.trans LD.atoms.base_gt_one) := by
    simpa only [LD.base_eq] using hradius
  have hcutoff' : X ≤ LD.atoms.base ^ cutoffExponent := by
    simpa only [LD.base_eq] using hcutoff
  have hproduct' : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
      (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤
        LD.atoms.base ^ (2 * (G.skeleton.A - G.skeleton.c - G.skeleton.w + columnLoss)) := by
    simpa only [LD.base_eq] using hproduct
  have hold' : A.exteriorNorm ((F.moving P R oldMoving).effectiveFullSupport
      (remaining * extra)) ≤
      LD.atoms.base ^ ((a.q + G.skeleton.R + G.skeleton.E + widthMax) + G.skeleton.wo) := by
    have he : a.q + G.skeleton.R + G.skeleton.E + G.skeleton.wo + widthMax =
        (a.q + G.skeleton.R + G.skeleton.E + widthMax) + G.skeleton.wo := by ring
    simpa only [LD.base_eq, he] using hold
  have hm := CanonicalLiteralExceptionalFactory.centered_mask_window chart P R hclass hsector
    X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair LD.atoms LD.model
    hcorr remaining extra LD.recipe firstSupport hfirst hextra LD.support hone hroot hemb
    .left LD.ray LD.ideal LD.ideal_eq LD.firstSign LD.divisor LD.selection LD.nonempty
    first.retainedScale first.enlargement
    (G.skeleton.A - G.skeleton.c - G.skeleton.w + columnLoss)
    (a.q + G.skeleton.R + G.skeleton.E + widthMax) G.skeleton.wo cutoffExponent
    first.retainedScale_pos hradius' hcutoff' hproduct' hold' hcL prodL ξ h.val
  have hm' : (Ideal.absNorm (TL ξ h).source.mask : ℝ) ≤
      (Ideal.absNorm A.cS : ℝ) *
        Z ^ (CanonicalLiteralExceptionalPhysicalBox.physicalWidth G b.primes
          b.leftMultiplicity b.rightMultiplicity pattern columnLoss cutoffExponent + widthMax) := by
    simpa only [LD.base_eq, CanonicalLiteralExceptionalPhysicalBox.physicalWidth_shift] using hm
  exact hm'.trans ((fixed_mask_threshold Z _ hthreshold).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le
      (CanonicalLiteralExceptionalPhysicalBox.physicalWidth_add_width_add_one_le G b.primes
        b.leftMultiplicity b.rightMultiplicity b.left_positive b.right_positive pattern
        widthMax columnLoss cutoffExponent hZ hstep hwidth)))

end CenteredWindows

section Terminal

variable (primitive : VolumePrimitive ψ parent.theta window)
variable (hZ : 1 < Z) (hstep : 0 ≤ step) (hq : 0 ≤ a.q)
variable (herrorPrime : ∀ e p, first.tag = .error e p →
  (Ideal.absNorm p.asIdeal : ℝ) ≤ Z ^ (step / 3))
variable (columnLoss cutoffExponent : ℝ)
variable (hradius : radius = CanonicalRowBall.gaussRadius first.retainedScale Z first.enlargement
  first.retainedScale_pos (zero_lt_one.trans hZ))
variable (hcutoff : X ≤ Z ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤
    Z ^ (2 * (first.skeleton.A - first.skeleton.c - first.skeleton.w + columnLoss)))
variable (hcapL : LD.history.originalCount ≤ cap) (hcapR : RD.history.originalCount ≤ cap)
variable (hprimeOriginalL : LD.history.original.PrimeNormWindow annulus)
variable (hprimeOriginalR : RD.history.original.PrimeNormWindow annulus)
variable (hproductOriginalL : LD.history.original.scaleProduct false = Z ^ G.skeleton.A)
variable (hproductOriginalR : RD.history.original.scaleProduct false = Z ^ G.skeleton.A)
variable (hprimeL : LD.atoms.PrimeNormWindow annulus)
variable (hprimeR : RD.atoms.PrimeNormWindow annulus)
variable (hslotL : ∀ i, SchwartzMap.seminorm ℂ 0 0 (LD.model.slot i) ≤ amplitude)
variable (hslotR : ∀ i, SchwartzMap.seminorm ℂ 0 0 (RD.model.slot i) ≤ amplitude)
variable (hamplitudeOne : 1 ≤ amplitude) (hslotLoss : annulus ≤ Z ^ (2 * slotLoss))

local notation "cutoffLoss" =>
  CanonicalLiteralExceptionalGeometry.paidCutoff columnLoss cutoffExponent 0
local notation "childExponent" =>
  (2 * (n.Aexp - n.c - n.w) - n.K₀ - n.g - n.g₂ - n.V₀) +
    (a.q + n.R₀ + n.E₀ + n.wo + n.t₂ + n.V₀) +
    (n.b₂ - n.p₂ + n.w + n.Bcommon + n.ell)
local notation "rowFactor" => mass.originalRowAmplitude * Z ^ (n.g₂ - n.t₂) /
  (Real.sqrt LF.normalizationScale * Real.sqrt RF.normalizationScale)

section Centered

variable (ε widthMax : ℝ) (hε : 0 < ε)
variable (hwidthMax : 0 ≤ widthMax) (hcolumnLoss : 0 ≤ columnLoss)
variable (hcutoffExponent : 0 ≤ cutoffExponent)
local notation "maskExp" =>
  CanonicalLiteralExceptionalPhysicalBox.maskExponent widthMax columnLoss cutoffExponent
local notation "hmaskExp" => CanonicalLiteralExceptionalPhysicalBox.maskExponent_nonneg
  hwidthMax hcolumnLoss hcutoffExponent
local notation "orders" => centeredOrders (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExp hε hmaskExp
local notation "order" => centeredOrder (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExp hε hmaskExp
local notation "constant" => centeredConstant (A := A) (σ := σ) (η := η) (hS := hS)
  primitive ε maskExp hε hmaskExp
variable {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain true parent a Z Y₁ Y₂ floor padding)
variable (hseedLeftL : ∀ r, LD.history.original.scale₁ r = if r then Y₁ else Z ^ a.n₁)
variable (hseedRightL : ∀ r, LD.history.original.scale₂ r = if r then Y₂ else Z ^ a.n₂)
variable (hseedLeftR : ∀ r, RD.history.original.scale₁ r = if r then Y₁ else Z ^ a.n₁)
variable (hseedRightR : ∀ r, RD.history.original.scale₂ r = if r then Y₂ else Z ^ a.n₂)
variable (hcL : SamePlainProfiles LD.model) (hcR : SamePlainProfiles RD.model)
variable (hprofileL₁ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.left false) ≤ amplitude)
variable (hprofileL₂ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.right false) ≤ amplitude)
variable (hprofileR₁ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.left false) ≤ amplitude)
variable (hprofileR₂ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.right false) ≤ amplitude)
variable (horder : idealLogLength Z (primePowerProduct b.primes b.leftMultiplicity).val ≤
  idealLogLength Z (primePowerProduct b.primes b.rightMultiplicity).val)
variable (hwidth : a.m + a.q ≤ widthMax)
variable (hthreshold : max 2 (Ideal.absNorm A.cS : ℝ) ≤ Z)
variable (hold : A.exteriorNorm ((F.moving P R oldMoving).effectiveFullSupport
  (remaining * extra)) ≤
    Z ^ (a.q + G.skeleton.R + G.skeleton.E + G.skeleton.wo + widthMax))

local notation "prodL" => LD.comparison_product domain hseedLeftL hseedRightL
local notation "prodR" => RD.comparison_product domain hseedLeftR hseedRightR
local notation "TL" => OriginalSide.actualCentered chart P R hclass hsector X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb LD .left hcL prodL
local notation "TR" => OriginalSide.actualCentered chart P R hclass hsector X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb RD .right hcR prodR

include hclass hsector hcorr hfirst hextra hone hroot hemb
  hfirstL hfirstR hsecondL hsecondR hplaces hscalar hZ hstep hq herrorPrime
  hradius hcutoff hproduct hcapL hcapR hprimeOriginalL hprimeOriginalR
  hproductOriginalL hproductOriginalR hprimeL hprimeR hslotL hslotR
  hamplitudeOne hslotLoss domain hseedLeftL hseedRightL hseedLeftR hseedRightR
  hcL hcR hprofileL₁ hprofileL₂ hprofileR₁ hprofileR₂ horder hwidth hthreshold hold in
/-- The actual centered magnitude satisfies the paid terminal. Every
row/class/window/atomic hypothesis of the terminal is constructed from
the original data above. The uniform orders and constant were selected
by the primitive before either atom table or Fourier mode. -/
theorem centered_magnitude_bound (ξ : Joint) :
    Z ^ (-childExponent) * LF.exceptionalMagnitude RF EL ER characters ξ ≤
      rowFactor * ((Γ.index : ℝ) * constant * (UL.constant * UR.constant)) * amplitude ^ 4 *
        (1 + fourierHeight ξ) ^ order *
        Z ^ (max (n.Aexp - (a.m + a.q)) 0 + 3 * n.stepσ + 5 * n.δ / 6 + ε +
          n.slotError - idealLogLength Z RD.divisor + cutoffLoss / 6) := by
  have hC := centeredConstant_pos (A := A) (σ := σ) (η := η) (hS := hS)
    primitive ε maskExp hε hmaskExp
  have hrow0 := mass.originalRowAmplitude_nonneg
  have hUL := UL.constant_nonneg
  have hUR := UR.constant_nonneg
  by_cases hlive : Nonempty S.live
  · let row : S.live := Classical.choice hlive
    obtain ⟨base, hfactor, hvaluation⟩ := actual_classification
      chart P R hclass hsector X hX label F parent oldMoving correction leftAtoms rightAtoms
      thetaPair hcorr remaining extra firstSupport LD hsecondL hplaces hscalar
    have hPL := LD.profile_supports S C .left ξ
    have hPR := RD.profile_supports S C .right ξ
    have hSL := LD.profile_seminorms S C .left ξ orders
    have hSR := RD.profile_seminorms S C .right ξ orders
    have hAL (h : S.exceptionalRows characters) : (TL ξ h).source.AtomicControl Z UL :=
      OriginalSide.actualCenteredPaidAtoms chart P R hclass hsector X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
        firstSupport hfirst hextra hone hroot hemb LD .left annulus amplitude hannulus
        hamplitude hprimeL hslotL G.skeleton.A cap hcapL hprimeOriginalL hproductOriginalL
        hZ hcL prodL ξ h
    have hAR (h : S.exceptionalRows characters) : (TR ξ h).source.AtomicControl Z UR :=
      OriginalSide.actualCenteredPaidAtoms chart P R hclass hsector X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
        firstSupport hfirst hextra hone hroot hemb RD .right annulus amplitude hannulus
        hamplitude hprimeR hslotR G.skeleton.A cap hcapR hprimeOriginalR hproductOriginalR
        hZ hcR prodR ξ h
    have hmin (h : S.exceptionalRows characters) :
        Z ^ ((a.m + a.q) / 4 - n.vStar - n.r₁) ≤ (TL ξ h).source.lower :=
      centered_minimum (chart := chart) (P := P) (R := R) (hclass := hclass)
        (hsector := hsector) (F := F) (parent := parent) (oldMoving := oldMoving)
        (correction := correction) (hcorr := hcorr) (leftAtoms := leftAtoms)
        (rightAtoms := rightAtoms) (thetaPair := thetaPair) (remaining := remaining)
        (extra := extra) (firstSupport := firstSupport) (hfirst := hfirst) (hextra := hextra)
        (hone := hone) (hroot := hroot) (hemb := hemb) (LD := LD) (first := first)
        (hfirstL := hfirstL) (hsecondL := hsecondL) (domain := domain)
        (hseedLeftL := hseedLeftL) (hseedRightL := hseedRightL) (hcL := hcL)
        (horder := horder) ξ h
    have hmask (h : S.exceptionalRows characters) :
        (Ideal.absNorm (TL ξ h).source.mask : ℝ) ≤ Z ^ maskExp :=
      centered_mask (chart := chart) (P := P) (R := R) (hclass := hclass)
        (hsector := hsector) (F := F) (parent := parent) (oldMoving := oldMoving)
        (correction := correction) (hcorr := hcorr) (leftAtoms := leftAtoms)
        (rightAtoms := rightAtoms) (thetaPair := thetaPair) (remaining := remaining)
        (extra := extra) (firstSupport := firstSupport) (hfirst := hfirst) (hextra := hextra)
        (hone := hone) (hroot := hroot) (hemb := hemb) (LD := LD) (first := first)
        (domain := domain) (hseedLeftL := hseedLeftL) (hseedRightL := hseedRightL)
        (hcL := hcL) (columnLoss := columnLoss) (cutoffExponent := cutoffExponent)
        (widthMax := widthMax) (hZ := hZ) (hstep := hstep) (hwidth := hwidth)
        (hthreshold := hthreshold) (hradius := hradius) (hcutoff := hcutoff)
        (hproduct := hproduct) (hold := hold) ξ h
    have hb := centeredEstimate (A := A) (σ := σ) (η := η) (hS := hS)
      primitive ε maskExp hε hmaskExp
      (CanonicalLiteralExceptionalCharacters.selectedIndex parent thetaPair.1)
      (CanonicalLiteralExceptionalCharacters.selectedIndex parent thetaPair.2)
      (LD.leftProfile S C .left ξ) (LD.rightProfile S C .left ξ)
      (RD.leftProfile S C .right ξ) (RD.rightProfile S C .right ξ)
      hPL.1 hPL.2 hPR.1 hPR.2 amplitude hamplitudeOne
      (hSL.1.le.trans hprofileL₁) (hSL.2.le.trans hprofileL₂)
      (hSR.1.le.trans hprofileR₁) (hSR.2.le.trans hprofileR₂)
      C S LF RF EL ER characters ξ (TL ξ) (TR ξ) UL UR
      Z n.Aexp a.m a.q n.c n.d n.R₀ n.E₀ n.K₀ n.w n.wo n.Bcommon n.g n.ell
      n.b₂ n.p₂ n.g₂ n.t₂ n.V₀ n.v n.vStar n.r₁ n.r₂ (idealLogLength Z RD.divisor)
      n.slotError cutoffLoss (Γ.index : ℝ) (fourierHeight ξ) n.stepσ n.δ mass.originalRowAmplitude
      hZ.le
      (CanonicalLiteralExceptionalNumbers.v_nonneg chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile hZ)
      (LF.allocation.rawExtractionLength_nonneg Z hZ LD.atoms.length
        (fun i => (LD.atoms.length_pos i).le))
      (RD.divisor_window S C .right annulus slotLoss hZ hprimeR hslotLoss)
      (Nat.cast_nonneg Γ.index) (fourierHeight_nonneg ξ) hrow0 hAL hAR
      (paid_atom_exponent chart P R hclass X hX label F parent oldMoving correction
        leftAtoms rightAtoms thetaPair remaining extra firstSupport annulus amplitude
        hannulus hamplitude cap LD RD hleftCommon hrightCommon rowProfileBound
        hrowProfileBound hrowProfile first slotLoss firstProfile hfirstL hfirstR hsecondL hsecondR)
      b.left_positive
      (CanonicalLiteralExceptionalNumbers.gcd_window chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile hZ)
      (fun h hh => CanonicalLiteralExceptionalNumbers.unit_window chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile first rL rR slotError
        firstProfile hZ h (Finset.mem_filter.mp hh).1)
      (fun h hh => mass.original_row_weight_bound h (Finset.mem_filter.mp hh).1)
      base.val (fun h => hvaluation h.val) (fun h => hfactor h.val)
      (fun h => CanonicalLiteralExceptionalNumbers.radical_window chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile first rL rR slotError
        firstProfile hZ h.val.val (Finset.mem_filter.mp h.val.property).1)
      (fun h => CanonicalLiteralExceptionalNumbers.cutoff_window chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile first rL rR slotError
        firstProfile columnLoss cutoffExponent hZ hradius hcutoff hproduct h.val)
      (CanonicalLiteralExceptionalArithmetic.exceptional_fibers chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile characters)
      (CanonicalLiteralExceptionalNumbers.first_saving chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile
        hZ hstep hq herrorPrime)
      (CanonicalLiteralExceptionalNumbers.second_saving chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile hZ row)
      (CanonicalLiteralExceptionalNumbers.v_sum chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile)
      (fun h => CanonicalLiteralExceptionalFactory.centered_mask_ne_zero chart P R hclass
        hsector X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
        LD.atoms LD.model hcorr remaining extra LD.recipe firstSupport hfirst hextra
        LD.support hone hroot hemb .left LD.ray LD.ideal LD.ideal_eq LD.firstSign
        LD.divisor LD.selection LD.nonempty hcL prodL ξ h.val)
      hmask
      (fun h => by simpa only [Real.norm_eq_abs] using
        CanonicalLiteralExceptionalFactory.centered_time_window chart P R hclass hsector
          X hX label F parent oldMoving correction leftAtoms rightAtoms thetaPair
          LD.atoms LD.model hcorr remaining extra LD.recipe firstSupport hfirst hextra
          LD.support hone hroot hemb .left LD.ray LD.ideal LD.ideal_eq LD.firstSign
          LD.divisor LD.selection LD.nonempty LD.firstSign_le hcL prodL ξ h.val)
      hmin
    exact hb
  · have hempty : S.exceptionalRows characters = ∅ :=
      Finset.eq_empty_of_forall_not_mem (fun h _ => hlive ⟨h⟩)
    simp only [SecondSideFrame.exceptionalMagnitude, jointColumnPairMagnitude,
      hempty, Finset.sum_empty, mul_zero]
    positivity

end Centered

section Ordinary

local notation "orders" => ordinaryOrders (A := A) (σ := σ) (η := η) (hS := hS) primitive
local notation "constant" => ordinaryConstant (A := A) (σ := σ) (η := η) (hS := hS) primitive
variable {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain false parent a Z Y₁ Y₂ floor padding)
variable (hprofileL₁ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.left false) ≤ amplitude)
variable (hprofileL₂ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (LD.model.right false) ≤ amplitude)
variable (hprofileR₁ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.left false) ≤ amplitude)
variable (hprofileR₂ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) (RD.model.right false) ≤ amplitude)

local notation "TL" => OriginalSide.actualOrdinary chart P R hclass hsector X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb LD .left
local notation "TR" => OriginalSide.actualOrdinary chart P R hclass hsector X hX label
  F parent oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
  firstSupport hfirst hextra hone hroot hemb RD .right

include hclass hsector hcorr hfirst hextra hone hroot hemb
  hfirstL hfirstR hsecondL hsecondR hplaces hscalar hZ hstep hq herrorPrime
  hradius hcutoff hproduct hcapL hcapR hprimeOriginalL hprimeOriginalR
  hproductOriginalL hproductOriginalR hprimeL hprimeR hslotL hslotR
  hamplitudeOne hslotLoss domain hprofileL₁ hprofileL₂ hprofileR₁ hprofileR₂ in
/-- The ordinary literal source uses its own absolute terminal and
the original ordinary domain. It needs neither a comparison minimum
nor a residue cancellation hypothesis, and pays the same physical
cutoff loss without changing the selected source. -/
theorem ordinary_magnitude_bound (ξ : Joint) :
    Z ^ (-childExponent) * LF.ordinaryExceptionalMagnitude RF characters ξ ≤
      rowFactor * ((Γ.index : ℝ) * constant * (UL.constant * UR.constant)) * amplitude ^ 4 *
        Z ^ (3 * n.stepσ + 5 * n.δ / 6 +
          n.slotError - idealLogLength Z RD.divisor + cutoffLoss / 6) := by
  have hC := ordinaryConstant_pos (A := A) (σ := σ) (η := η) (hS := hS) primitive
  have hrow0 := mass.originalRowAmplitude_nonneg
  have hUL := UL.constant_nonneg
  have hUR := UR.constant_nonneg
  by_cases hlive : Nonempty S.live
  · let row : S.live := Classical.choice hlive
    obtain ⟨base, hfactor, hvaluation⟩ := actual_classification
      chart P R hclass hsector X hX label F parent oldMoving correction leftAtoms rightAtoms
      thetaPair hcorr remaining extra firstSupport LD hsecondL hplaces hscalar
    have hPL := LD.profile_supports S C .left ξ
    have hPR := RD.profile_supports S C .right ξ
    have hSL := LD.profile_seminorms S C .left ξ orders
    have hSR := RD.profile_seminorms S C .right ξ orders
    have hAL (h : S.exceptionalRows characters) : (TL ξ h).source.AtomicControl Z UL :=
      OriginalSide.actualOrdinaryPaidAtoms chart P R hclass hsector X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
        firstSupport hfirst hextra hone hroot hemb LD .left annulus amplitude hannulus
        hamplitude hprimeL hslotL G.skeleton.A cap hcapL hprimeOriginalL hproductOriginalL hZ ξ h
    have hAR (h : S.exceptionalRows characters) : (TR ξ h).source.AtomicControl Z UR :=
      OriginalSide.actualOrdinaryPaidAtoms chart P R hclass hsector X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hcorr remaining extra
        firstSupport hfirst hextra hone hroot hemb RD .right annulus amplitude hannulus
        hamplitude hprimeR hslotR G.skeleton.A cap hcapR hprimeOriginalR hproductOriginalR hZ ξ h
    have hnonneg := G.exceptionalNumbers_common_nonneg mass G.centeredExtractionLength
      rL rR slotError firstProfile hZ
    have hb := ordinaryEstimate (A := A) (σ := σ) (η := η) (hS := hS) primitive
      (CanonicalLiteralExceptionalCharacters.selectedIndex parent thetaPair.1)
      (CanonicalLiteralExceptionalCharacters.selectedIndex parent thetaPair.2)
      (LD.leftProfile S C .left ξ) (LD.rightProfile S C .left ξ)
      (RD.leftProfile S C .right ξ) (RD.rightProfile S C .right ξ)
      hPL.1 hPL.2 hPR.1 hPR.2 amplitude hamplitudeOne
      (hSL.1.le.trans hprofileL₁) (hSL.2.le.trans hprofileL₂)
      (hSR.1.le.trans hprofileR₁) (hSR.2.le.trans hprofileR₂)
      C S LF RF characters ξ (TL ξ) (TR ξ) UL UR
      Z n.Aexp a.m a.q n.c n.d n.R₀ n.E₀ n.K₀ n.w n.wo n.Bcommon n.g n.ell
      n.b₂ n.p₂ n.g₂ n.t₂ n.V₀ n.v n.r₁ n.r₂ (idealLogLength Z RD.divisor)
      n.slotError cutoffLoss (Γ.index : ℝ) n.stepσ n.δ mass.originalRowAmplitude
      hZ.le
      (CanonicalLiteralExceptionalNumbers.v_nonneg chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile hZ)
      (LF.allocation.rawExtractionLength_nonneg Z hZ LD.atoms.length
        (fun i => (LD.atoms.length_pos i).le))
      (RD.divisor_window S C .right annulus slotLoss hZ hprimeR hslotLoss)
      (Nat.cast_nonneg Γ.index) hrow0
      (G.exceptionalNumbers_ordinary_range mass G.centeredExtractionLength
        rL rR slotError firstProfile domain)
      hnonneg.1 hnonneg.2.1 hnonneg.2.2 hAL hAR
      (paid_atom_exponent chart P R hclass X hX label F parent oldMoving correction
        leftAtoms rightAtoms thetaPair remaining extra firstSupport annulus amplitude
        hannulus hamplitude cap LD RD hleftCommon hrightCommon rowProfileBound
        hrowProfileBound hrowProfile first slotLoss firstProfile hfirstL hfirstR hsecondL hsecondR)
      b.left_positive
      (CanonicalLiteralExceptionalNumbers.gcd_window chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile hZ)
      (fun h hh => CanonicalLiteralExceptionalNumbers.unit_window chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile first rL rR slotError
        firstProfile hZ h (Finset.mem_filter.mp hh).1)
      (fun h hh => mass.original_row_weight_bound h (Finset.mem_filter.mp hh).1)
      base.val (fun h => hvaluation h.val) (fun h => hfactor h.val)
      (fun h => CanonicalLiteralExceptionalNumbers.radical_window chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile first rL rR slotError
        firstProfile hZ h.val.val (Finset.mem_filter.mp h.val.property).1)
      (fun h => CanonicalLiteralExceptionalNumbers.cutoff_window chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile first rL rR slotError
        firstProfile columnLoss cutoffExponent hZ hradius hcutoff hproduct h.val)
      (CanonicalLiteralExceptionalArithmetic.exceptional_fibers chart P R hclass X hX
        label F parent oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon
        hrightCommon rowProfileBound hrowProfileBound hrowProfile characters)
      (CanonicalLiteralExceptionalNumbers.first_saving chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile
        hZ hstep hq herrorPrime)
      (CanonicalLiteralExceptionalNumbers.second_saving chart P R hclass X hX label F parent
        oldMoving correction leftAtoms rightAtoms thetaPair hleftCommon hrightCommon
        rowProfileBound hrowProfileBound hrowProfile first rL rR slotError firstProfile hZ row)
    exact hb
  · have hempty : S.exceptionalRows characters = ∅ :=
      Finset.eq_empty_of_forall_not_mem (fun h _ => hlive ⟨h⟩)
    simp only [SecondSideFrame.ordinaryExceptionalMagnitude, jointColumnPairMagnitude,
      hempty, Finset.sum_empty, mul_zero]
    positivity

end Ordinary

end Terminal

end Pair

end ActualRows

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.centeredConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.ordinaryConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.redistributedHistory
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.OriginalSide.actualCenteredPaidAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.OriginalSide.actualOrdinaryPaidAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.actual_classification
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.paid_atom_exponent
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.centered_minimum
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.centered_mask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.centered_magnitude_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidSource.ordinary_magnitude_bound
