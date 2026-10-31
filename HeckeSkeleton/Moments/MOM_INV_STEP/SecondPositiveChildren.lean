import HeckeSkeleton.Moments.MOM_INV_STEP.SecondMobiusGeometry

/-!
# Whole second positive energies with literal fixed-center children

The actual ideal Moebius pool is converted to exterior overlap ideals
and partitioned into the previously fixed finite norm bins. Every branch
is the literal canonical child with the original surviving prime lists.
Its genuine Mellin energy is integrable against the common Fourier
density. The only optional comparison is a pointwise density envelope;
no source identity, column bound or energy estimate is an input.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondPositiveChildren

open NumberField IsDedekindDomain MeasureTheory UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CommonKernel
  SecondOverlapColumns SecondCompleteColumns SecondCenteredFamily
  SecondMellinEnergy SecondColumnEnergy SecondMobiusGeometry
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

variable (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
variable (G : HeckeCharacter K) (hG : G ∈ Θ) (g j d₂ I : Ext) (ξ : Sector)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)) (X : ℝ)

def branchEnergy (i : Index X) (v : overlapPool K S X g) (τ : ℝ) : ℝ :=
  (‖overlapZero K S g j (overlapIdeal K S X g v)‖ *
    (((C.survivors γ₀).powerset.card : ℝ) * mellinMass W hW)) *
    ∑ J ∈ (C.survivors γ₀).powerset,
      ‖assignedMark K S g (overlapIdeal K S X g v) C.primeLists C.primeWeights J‖ ^ 2 *
        columnEnergy K S D Γ C γ₀ G hG J (childScale X i)
          (appendResidual K γ₀ (residual K S g d₂).val.val)
          (finalLabel K S j d₂ (overlapIdeal K S X g v)).val.val (I.val.val,ξ) W hW τ

theorem branchEnergy_nonneg (i : Index X) (v : overlapPool K S X g) (τ : ℝ) :
    0 ≤ branchEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X i v τ := by
  apply mul_nonneg (mul_nonneg (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (mellinMass_nonneg W hW)))
  apply Finset.sum_nonneg
  intro J hJ
  exact mul_nonneg (sq_nonneg _)
    (column_energy_nonneg K S D Γ C γ₀ G hG J (childScale X i)
      (appendResidual K γ₀ (residual K S g d₂).val.val)
      (finalLabel K S j d₂ (overlapIdeal K S X g v)).val.val (I.val.val,ξ) W hW τ)

def centeredEnergy (w : LogPlane → ℝ) (coordinate : LogPlane →L[ℝ] ℝ) : ℝ :=
  ∑ i : Index X, ∑ v ∈ bin K S X g i,
    ‖(moebius v.val : ℂ)‖ * ∫ τ : LogPlane,
      w τ * branchEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X i v (coordinate τ)

theorem centeredEnergy_eq (w : LogPlane → ℝ) (coordinate : LogPlane →L[ℝ] ℝ) :
    centeredEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X w coordinate =
      ∑ v : overlapPool K S X g, ‖(moebius v.val : ℂ)‖ * ∫ τ : LogPlane,
        w τ * branchEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X
          (centerIndex K S X g v) v (coordinate τ) := by
  unfold centeredEnergy bin
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem sourceColumn_continuous (v : Ext) :
    Continuous (fun τ : ℝ => sourceColumn K S D Γ C γ₀ G g j d₂ v I ξ W X τ) := by
  exact IntegralEnergy.finite_column_continuous
    ((SecondPhysicalEnergy.sourcePool K S g X).filter (fun z => v.val.val ∣ z.val.val))
    (SecondPhysicalEnergy.sourceCoefficient K S D Γ C γ₀ G g j d₂ I ξ W X)
    (fun z => Real.log (height K Sset z / (X / height K Sset g)))

theorem sourceEnergy_eq (P : CanonicalFirstEnergy.Profile K S)
    (coordinate : LogPlane →L[ℝ] ℝ) :
    SecondPhysicalEnergy.positiveEnergy K S D Γ C γ₀ G g j d₂ I ξ W X P coordinate =
      ∑ v : overlapPool K S X g, ‖(moebius v.val : ℂ)‖ * ∫ τ : LogPlane,
        ‖SecondPhysicalEnergy.density K S Γ P τ‖ *
          ‖sourceColumn K S D Γ C γ₀ G g j d₂ (overlapIdeal K S X g v) I ξ W X
            (coordinate τ)‖ ^ 2 := by
  unfold SecondPhysicalEnergy.positiveEnergy
  change (∑ v ∈ overlapPool K S X g, ‖(moebius v : ℂ)‖ * _) = _
  rw [← Finset.sum_coe_sort]
  rfl

theorem branchEnergy_integrable (hX : 0 < X) (hZ : 1 < C.base)
    (i : Index X) (v : overlapPool K S X g)
    (w : LogPlane → ℝ) (hw : Integrable w) (cw : Continuous w)
    (coordinate : LogPlane →L[ℝ] ℝ) :
    Integrable (fun τ : LogPlane => w τ *
      branchEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X i v (coordinate τ)) := by
  unfold branchEnergy
  simp only [Finset.mul_sum]
  apply integrable_finset_sum
  intro J hJ
  have hi := outer_energy_integrable K S D Γ C γ₀ G hG J (childScale X i)
    (appendResidual K γ₀ (residual K S g d₂).val.val)
    (finalLabel K S j d₂ (overlapIdeal K S X g v)).val.val (I.val.val,ξ)
    W hW hZ (childScale_pos X hX i) w hw cw coordinate
  convert hi.const_mul
    ((‖overlapZero K S g j (overlapIdeal K S X g v)‖ *
      (((C.survivors γ₀).powerset.card : ℝ) * mellinMass W hW)) *
      ‖assignedMark K S g (overlapIdeal K S X g v) C.primeLists C.primeWeights J‖ ^ 2) using 1
  funext τ
  ring

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
theorem sourceColumn_le_branchEnergy
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val)
    (hX : 0 < X) (hZ : 1 < C.base)
    (hprime : ∀ i ∈ C.survivors γ₀, ∀ p ∈ C.primeLists i, Prime p)
    (v : overlapPool K S X g) (τ : ℝ) :
    ‖sourceColumn K S D Γ C γ₀ G g j d₂ (overlapIdeal K S X g v) I ξ W X τ‖ ^ 2 ≤
      branchEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X
        (centerIndex K S X g v) v τ := by
  obtain ⟨hlo,hhi⟩ := centerIndex_bounds K S X g v
  exact sourceColumn_sq_le_mellin_with_zero K S D Γ hallowed C γ₀ G hG hcal
    g j d₂ (overlapIdeal K S X g v) I ξ hg hd₂ (overlapIdeal_squarefree K S X g v)
    W hW X τ (DyadicSourcePartition.center (centerIndex K S X g v).val)
    (childScale X (centerIndex K S X g v)) hX hZ
    (DyadicSourcePartition.center_pos _) (childScale_pos X hX _) hlo hhi
    (childScale_identity X _) hprime

include hallowed in
/-- Every positive source column has now entered its actual canonical
child integral. A later common-density estimate may replace the measure;
it does not supply any algebraic or energy conclusion used here. -/
theorem sourceEnergy_le_of_density_bound
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val)
    (hX : 0 < X) (hZ : 1 < C.base)
    (hprime : ∀ i ∈ C.survivors γ₀, ∀ p ∈ C.primeLists i, Prime p)
    (P : CanonicalFirstEnergy.Profile K S) (coordinate : LogPlane →L[ℝ] ℝ)
    (w : LogPlane → ℝ) (hw : Integrable w) (cw : Continuous w) (hw0 : ∀ τ, 0 ≤ w τ)
    (M : ℝ) (hM : 0 ≤ M)
    (hP : ∀ τ, ‖SecondPhysicalEnergy.density K S Γ P τ‖ ≤ M * w τ) :
    SecondPhysicalEnergy.positiveEnergy K S D Γ C γ₀ G g j d₂ I ξ W X P coordinate ≤
      M * centeredEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X w coordinate := by
  rw [sourceEnergy_eq K S D Γ, centeredEnergy_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hbound (τ : LogPlane) :
      ‖SecondPhysicalEnergy.density K S Γ P τ‖ *
        ‖sourceColumn K S D Γ C γ₀ G g j d₂ (overlapIdeal K S X g v) I ξ W X
          (coordinate τ)‖ ^ 2 ≤
      M * (w τ * branchEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X
        (centerIndex K S X g v) v (coordinate τ)) := by
    exact (mul_le_mul (hP τ)
      (sourceColumn_le_branchEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X
        hallowed hcal hg hd₂ hX hZ hprime v (coordinate τ))
      (sq_nonneg _) (mul_nonneg hM (hw0 τ))).trans_eq (mul_assoc _ _ _)
  have hr := (branchEnergy_integrable K S D Γ C γ₀ G hG g j d₂ I ξ W hW X
    hX hZ (centerIndex K S X g v) v w hw cw coordinate).const_mul M
  have hl := SecondPhysicalEnergy.column_energy_integrable K S D Γ C γ₀ G
    g j d₂ I ξ W X P v.val coordinate
  have hi := integral_mono hl hr hbound
  rw [integral_const_mul] at hi
  exact (mul_le_mul_of_nonneg_left hi (norm_nonneg (moebius v.val : ℂ))).trans_eq (by ring)

include hallowed in
theorem sourceEnergy_le_children
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val)
    (hX : 0 < X) (hZ : 1 < C.base)
    (hprime : ∀ i ∈ C.survivors γ₀, ∀ p ∈ C.primeLists i, Prime p)
    (P : CanonicalFirstEnergy.Profile K S) (coordinate : LogPlane →L[ℝ] ℝ) :
    SecondPhysicalEnergy.positiveEnergy K S D Γ C γ₀ G g j d₂ I ξ W X P coordinate ≤
      centeredEnergy K S D Γ C γ₀ G hG g j d₂ I ξ W hW X
        (fun τ => ‖SecondPhysicalEnergy.density K S Γ P τ‖) coordinate := by
  simpa only [one_mul] using sourceEnergy_le_of_density_bound
    K S D Γ C γ₀ G hG g j d₂ I ξ W hW X hallowed hcal hg hd₂ hX hZ hprime P coordinate
    (fun τ => ‖SecondPhysicalEnergy.density K S Γ P τ‖)
    (SecondPhysicalEnergy.density K S Γ P).integrable.norm
    (SecondPhysicalEnergy.density K S Γ P).continuous.norm (fun _ => norm_nonneg _)
    1 zero_le_one (fun _ => by rw [one_mul])

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondPositiveChildren

end
