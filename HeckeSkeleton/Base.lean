import HeckeGeneral.Analysis.TIPClosure
import HeckeAxiom.SignalAdapter
import HeckeAxiom.MeasureAdapter
import HeckeAxiom.ProbeTestChoice
import HeckeAxiom.ProbeNormalization
import HeckeGeneral.Analysis.HeckeConjugateZeros
import HeckeGeneral.Analysis.HeckeNormTwistZeros
import HeckeGeneral.Characters.RadialNormalization
import HeckePort.Schedule.MomentMesh
import ArithmeticRowCharacterInput
import HeckeSkeleton.ExpansionModels.Core
import ExpansionInterfaces.ParameterChoices
import Expansion.ActualProbeContext
import Expansion.ActualRecipeData
import ThetaGlobal.GlobalChoice

/-! Exploratory, intentionally incomplete proof skeleton. This library is
separate from HeckeGeneral and its verified declaration count. Every admitted
construction or theorem has an obligation ID; no claim of a proved endpoint
is made by this library. -/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global

variable (K : Type) [Field K] [NumberField K]

/-- All family and real parameters fixed before choosing the slot system
or a later target. The upper boundary is ONE, not eleven twelfths. -/
structure FamilyContext where
  root12 : K
  primitive12 : IsPrimitiveRoot root12 12
  omega : HeckeCharacter K
  B : ℝ
  B_lower : 7 / 8 < B
  B_upper : B ≤ 1
  boundary : ∀ χ : HeckePacketIndex K omega, ∀ r ∈ heckePacketZeros K omega χ,
    1 / 2 ≤ r → r ≤ 1 → r ≤ B
  lamA : ℝ
  lamA_pos : 0 < lamA
  lamA_small : lamA ≤ 1 / 1000

-- D-MESH | revised §4.2, §4.9, §8 (pp.17–18,33–34,49–51).
-- One positive mesh for the bounded real box, BEFORE geometry or target: the
-- openai width-schedule mesh `fineMesh 2 0 1 1 lamA` (HeckePort.Schedule).
def momentMesh (c : FamilyContext K) : {m : ℝ // 0 < m} :=
  ⟨HeckePort.Schedule.momentMeshValue c.lamA, HeckePort.Schedule.momentMeshValue_pos c.lamA_pos⟩

/-- The type enforces the outer order: family/loss, mesh, geometry,
remaining loss, target. No analytic estimate is a field. -/
structure TargetContext where
  family : FamilyContext K
  geometry : PrimeWindowGeometry
  mesh_fine : (1 / 3 : ℝ) / geometry.slots ≤ (momentMesh K family).val
  lamB : ℝ
  lamB_pos : 0 < lamB
  target : HeckePacketIndex K family.omega

theorem exists_normTwistParameter (c : TargetContext K) :
    ∃ t : ℝ, ∃ θ : HeckeCharacter K, FiniteOrder θ ∧ ∃ e : ℤ, PacketExponent e ∧
      c.target.val = θ * c.family.omega ^ e * heckeNormTwist K t := by
  obtain ⟨θ, hθ, e, he, t, ht⟩ := c.target.property
  exact ⟨t, θ, hθ, e, he, ht⟩

/-- The full global norm parameter, including any norm factor in omega.
It is fixed canonically by one field-dependent infinite place. -/
def normTwistParameter (c : TargetContext K) : ℝ :=
  -heckeRadialParameter K (normNormalizationPlace K) c.target.val

/-- The target with its global norm twist removed (revised §6, first sentence). -/
def untwisted (c : TargetContext K) : HeckePacketIndex K c.family.omega :=
  ⟨c.target.val * heckeNormTwist K (-normTwistParameter K c),
    heckePacket_mul_normTwist K c.family.omega c.target.property _⟩

/-- The untwisted target uses the normalized packet generator; an arbitrary
generator may itself carry a global norm twist. -/
theorem untwisted_eq (c : TargetContext K) :
    ∃ θ : HeckeCharacter K, FiniteOrder θ ∧ ∃ e : ℤ, PacketExponent e ∧
      (untwisted K c).val =
        θ * radialNormalization K (normNormalizationPlace K) c.family.omega ^ e := by
  obtain ⟨θ, hθ, e, he, t, ht⟩ := c.target.property
  refine ⟨θ, hθ, e, he, ?_⟩
  have hnorm : (untwisted K c).val =
      radialNormalization K (normNormalizationPlace K) c.target.val := by
    simp only [untwisted, normTwistParameter, neg_neg, radialNormalization_apply]
  rw [hnorm, ht]
  exact radialNormalization_packet K (normNormalizationPlace K) c.family.omega θ hθ e t

theorem untwisted_radial_zero (c : TargetContext K) :
    heckeRadialParameter K (normNormalizationPlace K) (untwisted K c).val = 0 := by
  simpa only [untwisted, normTwistParameter, neg_neg, radialNormalization_apply] using
    radialParameter_radialNormalization K (normNormalizationPlace K) c.target.val

theorem untwisted_zeros (c : TargetContext K) :
    heckePacketZeros K c.family.omega (untwisted K c) =
      heckePacketZeros K c.family.omega c.target :=
  zeroRealParts_heckeContinuation_normTwist K c.target.val _

/-- The primes where the untwisted target ramifies. Conjugation does not
change them, so the representative below ramifies at the same primes. -/
def targetRamifiedPlaces (c : TargetContext K) :
    Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  (finite_ramifiedPlaces K (untwisted K c).val).toFinset

/-- Align the family's root before making the one shared arithmetic choice. -/
def complexEmbedding (c : TargetContext K) : K →+* ℂ :=
  ThetaGlobal.GlobalEmbedding.alignedEmbedding c.family.root12 c.family.primitive12

/-- ONE Axiom arithmetic choice for the target: it contains the target's
ramified primes, uses the family's twelfth root, and is shared by every
base datum below, so no second independent choice is made. -/
def axiomChoice (c : TargetContext K) :
    HeckeAxiom.ArithmeticChoice K (targetRamifiedPlaces K c) c.family.root12
      (complexEmbedding K c) :=
  ThetaGlobal.GlobalChoice.alignedChoice (targetRamifiedPlaces K c)
    c.family.root12 c.family.primitive12

theorem axiomChoice_modulus_top (c : TargetContext K) :
    (axiomChoice K c).A.modulus = ⊤ :=
  ThetaGlobal.GlobalChoice.alignedChoice_modulus (targetRamifiedPlaces K c)
    c.family.root12 c.family.primitive12

theorem axiomChoice_rootAligned (c : TargetContext K) :
    complexEmbedding K c (axiomChoice K c).A.zeta12 =
      ThetaGlobal.GlobalEmbedding.canonicalTwelfthRoot :=
  ThetaGlobal.GlobalProjectEmbedding.choice_root12 (axiomChoice K c)

theorem axiomChoice_coefficientEmbedding (c : TargetContext K) (z : rootsOfUnity 6 K) :
    complexEmbedding K c ((z : Kˣ) : K) =
      (DedekindZetaZeroFree.KPLocalCover.coefficientEmbedding K
        (axiomChoice K c).A.zeta12 (axiomChoice K c).A.primitive_zeta12 z : ℂ) :=
  ThetaGlobal.GlobalProjectEmbedding.choice_coefficientEmbedding (axiomChoice K c) z

-- OBLIGATION D-S | revised Proposition 3.1, §6.1 (pp.3–4,35–36).
-- The final set of the Axiom choice: target ramification, the different,
-- primes over six, class-group killing and trace-bad places.
def excludedPlaces (c : TargetContext K) :
    Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  (axiomChoice K c).places

abbrev places (c : TargetContext K) :=
  (excludedPlaces K c : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))

-- OBLIGATION D-ARITHMETIC | revised Proposition 3.1 (pp.3–4).
-- Same-S allowed generators of the context, the family root, the chosen
-- embedding and the different inside S.
def arithmeticData (c : TargetContext K) : ThetaArithmeticData K (places K c) :=
  (axiomChoice K c).thetaData

-- OBLIGATION D-SIGNALS | revised Proposition 3.1(iv) (p.4).
-- The continuous correction characters Lambda and finite-order G.
def signalCharacters (c : TargetContext K) : HeckeCharacter K × HeckeCharacter K :=
  ((axiomChoice K c).Lambda, (axiomChoice K c).G)

theorem untwisted_unramified_outside (c : TargetContext K)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) :
    UnramifiedAt K (untwisted K c).val p := by
  by_contra h
  apply hp
  apply Finset.mem_coe.mpr
  exact (axiomChoice K c).initial_subset
    ((finite_ramifiedPlaces K (untwisted K c).val).mem_toFinset.mpr h)

/-- The orientation condition of revised §3 (before Proposition 3.2) for the
untwisted target: the period conj(Λ)·conj(G)·ψ has a nonzero angular weight at
some complex place. -/
def AngularlyOriented (c : TargetContext K) : Prop :=
  ∃ (v : InfinitePlace K) (hv : v.IsComplex), heckeComplexWeight K v hv
    (conjugate (signalCharacters K c).1 * conjugate (signalCharacters K c).2 *
      (untwisted K c).val) ≠ 0

-- OBLIGATION D-REP | revised §6.1, §8 (pp.35–36,49–51).
-- Remove the norm twist and select the angular/conjugate representative.
-- The exact zero-real-part identity is retained in the returned subtype.
-- The conjugate is taken exactly when the untwisted target is not oriented.
open Classical in
def representative (c : TargetContext K) :
    {ψ : HeckePacketIndex K c.family.omega //
      heckePacketZeros K c.family.omega ψ = heckePacketZeros K c.family.omega c.target} :=
  if AngularlyOriented K c then ⟨untwisted K c, untwisted_zeros K c⟩
  else ⟨⟨(untwisted K c).val⁻¹, heckePacket_inv K c.family.omega (untwisted K c).property⟩,
    (zeroRealParts_heckeContinuation_inv K (untwisted K c).val).trans (untwisted_zeros K c)⟩

theorem representative_val (c : TargetContext K) :
    (representative K c).val.val = (untwisted K c).val ∨
      (representative K c).val.val = (untwisted K c).val⁻¹ := by
  unfold representative
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem target_unramified_outside (c : TargetContext K)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) :
    UnramifiedAt K (representative K c).val.val p := by
  rcases representative_val K c with h | h <;> rw [h]
  · exact untwisted_unramified_outside K c p hp
  · exact UnramifiedAt.inv K (untwisted_unramified_outside K c p hp)

/-- Every infinite place is complex: the family root has order twelve. -/
theorem isComplex_of_family (c : TargetContext K) (w : InfinitePlace K) : w.IsComplex := by
  classical
  apply InfinitePlace.not_isReal_iff_isComplex.mp
  intro hw
  have hcard := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
    (by decide : 2 < 12) c.family.primitive12
  have hempty : IsEmpty {w : InfinitePlace K // w.IsReal} := Fintype.card_eq_zero_iff.mp hcard
  exact hempty.false ⟨w, hw⟩

/-- The orientation of revised §3: if Λ has angular weight `b = ±1` at every
complex place and G has finite order, `k − b` and `−k − b` cannot both vanish,
so the representative's period has a nonzero angular weight somewhere. -/
theorem representative_angular (c : TargetContext K)
    (hΛ : ∀ (v : InfinitePlace K) (hv : v.IsComplex),
      heckeComplexWeight K v hv (signalCharacters K c).1 = 1 ∨
        heckeComplexWeight K v hv (signalCharacters K c).1 = -1)
    (hG : FiniteOrder (signalCharacters K c).2) :
    ∃ (v : InfinitePlace K) (hv : v.IsComplex), heckeComplexWeight K v hv
      (conjugate (signalCharacters K c).1 * conjugate (signalCharacters K c).2 *
        (representative K c).val.val) ≠ 0 := by
  unfold representative
  split_ifs with h
  · exact h
  · obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hv : v.IsComplex := isComplex_of_family K c v
    refine ⟨v, hv, ?_⟩
    have h0 : heckeComplexWeight K v hv (conjugate (signalCharacters K c).1 *
        conjugate (signalCharacters K c).2 * (untwisted K c).val) = 0 := by
      by_contra hne
      exact h ⟨v, hv, hne⟩
    have hG0 : heckeComplexWeight K v hv (signalCharacters K c).2 = 0 :=
      heckeComplexWeight_finiteOrder K v hv hG
    simp only [conjugate, heckeComplexWeight_mul, heckeComplexWeight_inv, hG0] at h0 ⊢
    rcases hΛ v hv with hb | hb <;> omega

-- OBLIGATION D-TESTS | revised §6.1–6.2 (pp.35–37).
-- The Fourier-zero additive test and positive denominator; normalization
-- properties are separately stated in Principal, not assumed here.
-- The additive test is Axiom's fixed weight for the same choice, scaled so that its
-- additive Mellin value at 1/6 is a positive real; the denominator is Axiom's bump.
def probeTests (c : TargetContext K) :
    AdditiveProbeTest K (places K c) × DenominatorTest :=
  (Classical.choose (HeckeAxiom.ProbeTestChoice.exists_probeTest (axiomChoice K c).A
      (axiomChoice K c).hS),
    HeckeAxiom.denominatorTest DedekindZetaZeroFree.probeRealBumpWeight)

def probeData (c : TargetContext K) : ProbeData K (places K c) where
  arithmetic := arithmeticData K c
  Lambda := (signalCharacters K c).1
  G := (signalCharacters K c).2
  additive := (probeTests K c).1
  denominator := (probeTests K c).2

-- OBLIGATION D-MEASURES | revised Proposition 3.1(i), §6.1 (pp.3,35).
-- Compatible Borel and self-dual Haar choices for the SAME probe.
-- Borel structures and Axiom's self-dual local Haar measures on S.
def probeMeasures (c : TargetContext K) : ProbeMeasures K (places K c) :=
  HeckeAxiom.selfDualProbeMeasures K (places K c)

-- OBLIGATION D-RAY | revised §3.1, §4.3, §6.1 (pp.3–4,18–20,35).
-- Finite character filter for the actual permitted ray/sector conditions.
-- Revised §6.1: all primes outside S are allowed, so no character filters the
-- windows; the fixed finite-ray restrictions permitted in §4.3 are not used.
def rayFilter (_c : TargetContext K) : Finset (HeckeCharacter K) := ∅

abbrev targetCharacter (c : TargetContext K) : HeckeCharacter K :=
  (representative K c).val.val

/-- Inversion for angular orientation preserves the normalized radial slice. -/
theorem targetCharacter_radial_zero (c : TargetContext K) :
    heckeRadialParameter K (normNormalizationPlace K) (targetCharacter K c) = 0 := by
  rcases representative_val K c with h | h <;> rw [show targetCharacter K c = _ from h]
  · exact untwisted_radial_zero K c
  · rw [heckeRadialParameter_inv, untwisted_radial_zero, neg_zero]

theorem targetCharacter_ne_normTwist (c : TargetContext K)
    (hne : targetCharacter K c ≠ 1) (t : ℝ) :
    targetCharacter K c ≠ heckeNormTwist K t :=
  ne_normTwist_of_radial_zero K (normNormalizationPlace K) _
    (targetCharacter_radial_zero K c) hne t

/-- The same shell allowance is used by the raw schedule and all consumers. -/
def expansionShellAllowance (c : TargetContext K) : ℝ :=
  ExpansionInterfaces.shellAllowance c.family.lamA

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance expansionNormOneSpace (c : TargetContext K) :
    MeasurableSpace (sLocalNormOneGroup K (places K c)) :=
  (probeMeasures K c).normOneSpace

local instance expansionNormOneBorel (c : TargetContext K) :
    BorelSpace (sLocalNormOneGroup K (places K c)) :=
  (probeMeasures K c).normOneBorel

local instance expansionLocalHaar (c : TargetContext K) (p : places K c) :
    ((probeMeasures K c).haar p).IsAddHaarMeasure :=
  (probeMeasures K c).haar_isAddHaar p

theorem expansionBoundary_lower (c : TargetContext K) : 51 / 100 ≤ c.family.B := by
  linarith [c.family.B_lower]

/-- One positive cap controls the internal displacement for both external
losses. The retained shell allowance still depends only on lamA. -/
def expansionInternalCap (c : TargetContext K) : ℝ :=
  min c.family.lamA c.lamB / 1000

theorem expansionInternalCap_pos (c : TargetContext K) : 0 < expansionInternalCap K c :=
  div_pos (lt_min c.family.lamA_pos c.lamB_pos) (by norm_num)

/-- The actual detector chooses its width, alphabet and height ceiling
once, before any analytic height exponent or original scale. -/
def expansionPhysicalParameters (c : TargetContext K) :
    Expansion.Project.PhysicalRecipeParameters K (places K c) (probeData K c)
      c.family.omega (targetCharacter K c) c.geometry
      (HighBinActualEuler.arithmeticHighEulerData K (places K c) (probeData K c)
        (targetCharacter K c))
      (representative K c).val.property (expansionBoundary_lower K c) c.family.B_upper
      c.family.boundary (probeMeasures K c).haar ∅ c.family.lamA
      (expansionShellAllowance K c) (expansionInternalCap K c) := by
  letI : ∀ p : places K c, ((probeMeasures K c).haar p).IsAddHaarMeasure :=
    (probeMeasures K c).haar_isAddHaar
  exact Expansion.Project.choosePhysicalRecipeParameters K (places K c) (probeData K c)
    c.family.omega (targetCharacter K c) c.geometry
    (HighBinActualEuler.arithmeticHighEulerData K (places K c) (probeData K c)
      (targetCharacter K c))
    (representative K c).val.property (expansionBoundary_lower K c) c.family.B_upper
    c.family.boundary (probeMeasures K c).haar ∅ (isComplex_of_family K c)
    c.family.lamA (expansionShellAllowance K c) (expansionInternalCap K c)
    c.family.lamA_pos (by linarith [c.family.lamA_small])
    (ExpansionInterfaces.shellAllowance_spec c.family.lamA_pos).2.2
    (expansionInternalCap_pos K c)

theorem expansionPhysicalParameters_e_losses (c : TargetContext K) :
    (expansionPhysicalParameters K c).e ≤ min c.family.lamA c.lamB / 100 := by
  have hcap := (expansionPhysicalParameters K c).e_cap
  have hmin : 0 < min c.family.lamA c.lamB :=
    lt_min c.family.lamA_pos c.lamB_pos
  dsimp only [expansionInternalCap] at hcap
  linarith

theorem expansionPhysicalParameters_e_sweep (c : TargetContext K) :
    (expansionPhysicalParameters K c).e ≤ 1 / 10000 := by
  have hcap := (expansionPhysicalParameters K c).e_cap
  dsimp only [expansionInternalCap] at hcap
  linarith [min_le_left c.family.lamA c.lamB, c.family.lamA_small]

-- D-EXPANSION | revised Proposition 6.3, §7.1–7.2 (pp.41–44).
-- The literal four components and all scheduled shifted blocks share the
-- same actual detector parameters. The constructor has no target estimate
-- or assumed expansion identity as an input.
def expansionRecipeRaw (c : TargetContext K) :
    ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c) :=
  Expansion.Project.actualPhysicalRecipe K (excludedPlaces K c)
    (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c)
    c.family.omega (targetCharacter K c) c.geometry (representative K c).val.property
    (expansionBoundary_lower K c) c.family.B_upper c.family.boundary c.family.lamA
    (expansionShellAllowance K c) (expansionInternalCap K c) (expansionPhysicalParameters K c)

/-- The original raw item itself has uniform geometry, including every
inactive amplitude label and every empty row fiber. -/
theorem expansionRecipeRaw_geometry (c : TargetContext K) :
    (expansionRecipeRaw K c).MomentGeometry 22 :=
  Expansion.Project.actualPhysicalRecipe_geometry K (excludedPlaces K c)
    (Expansion.ActualProbeContext.allLocalMeasures K) (probeData K c)
    c.family.omega (targetCharacter K c) c.geometry (representative K c).val.property
    (expansionBoundary_lower K c) c.family.B_upper c.family.boundary c.family.lamA
    (expansionShellAllowance K c) (expansionInternalCap K c) (expansionPhysicalParameters K c)

/-- Actual finite-polynomial values are projections of the one raw recipe. -/
def highExpansion (c : TargetContext K) : ℝ → ℝ →
    HighExpansion (FrequencyRow K (places K c)) c.geometry.slots :=
  (expansionRecipeRaw K c).toHigh (P := probeData K c)
    (R := arithmeticRowCharacterInput K (places K c) (probeData K c))
    (ω := c.family.omega)

theorem highExpansion_scale_of_block (c : TargetContext K) (Z T : ℝ)
    (b : Fin (highExpansion K c Z T).blockCount) :
    (2 : ℝ) ^ (16 : ℕ) ≤ Z ∧ 1 ≤ T :=
  (expansionRecipeRaw K c).active_of_index Z T b

theorem highExpansion_blockCount_le_schedule (c : TargetContext K) (Z T : ℝ) :
    (highExpansion K c Z T).blockCount ≤ (expansionRecipeRaw K c).scheduledCount Z :=
  (expansionRecipeRaw K c).toHigh_blockCount_le (P := probeData K c)
    (R := arithmeticRowCharacterInput K (places K c) (probeData K c))
    (ω := c.family.omega) Z T

theorem highExpansion_shell_lower (c : TargetContext K) (Z T : ℝ)
    (b : Fin (highExpansion K c Z T).blockCount) :
    1 / 16 ≤ ((highExpansion K c Z T).block b).shell :=
  ((expansionRecipeRaw K c).shell_range Z T b).1

theorem highExpansion_shell_range (c : TargetContext K) (Z T : ℝ)
    (b : Fin (highExpansion K c Z T).blockCount) :
    1 / 16 ≤ ((highExpansion K c Z T).block b).shell ∧
      ((highExpansion K c Z T).block b).shell < 13 / 16 + expansionShellAllowance K c :=
  (expansionRecipeRaw K c).shell_range Z T b

theorem highExpansion_shell_pos (c : TargetContext K) (Z T : ℝ)
    (b : Fin (highExpansion K c Z T).blockCount) :
    0 < ((highExpansion K c Z T).block b).shell :=
  (by norm_num : (0 : ℝ) < 1 / 16).trans_le (highExpansion_shell_lower K c Z T b)

-- OBLIGATION D-SUPPORT | revised §7.1 (pp.42–43).
theorem rows_in_norm_envelope (c : TargetContext K) :
    ∀ Z T₁ : ℝ, 1 ≤ Z → 1 ≤ T₁ →
    ∀ b : Fin (highExpansion K c Z T₁).blockCount,
    ∀ ℓ : ((highExpansion K c Z T₁).block b).Label,
      (((highExpansion K c Z T₁).block b).amplitudeSet ℓ).rows ⊆
        frequencyRows K (places K c) (2 * Z ^ ((highExpansion K c Z T₁).block b).shell) := by
  intro Z T₁ _hZ _hT b ℓ
  exact (expansionRecipeRaw K c).toHigh_rows_in_norm_envelope
    (P := probeData K c)
    (R := arithmeticRowCharacterInput K (places K c) (probeData K c))
    (ω := c.family.omega) Z T₁ b ℓ

def targetData (c : TargetContext K) : TargetData K c.geometry where
  S := excludedPlaces K c
  probe := probeData K c
  measures := probeMeasures K c
  rayFilter := rayFilter K c
  expansion := highExpansion K c
  rows_in_norm_envelope := rows_in_norm_envelope K c

end HeckeSkeleton
