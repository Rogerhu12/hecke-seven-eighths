import HeckeGeneral.Analysis.TIPClosure
import HeckeAxiom.SignalAdapter
import HeckeAxiom.MeasureAdapter
import HeckeAxiom.ProbeTestChoice
import HeckeAxiom.ProbeNormalization
import HeckeGeneral.Analysis.HeckeConjugateZeros
import HeckeGeneral.Analysis.HeckeNormTwistZeros
import HeckePort.Schedule.MomentMesh

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

/-- The global norm twist `N^{it}` of a decomposition `θ ω^e N^{it}` of the target. -/
def normTwistParameter (c : TargetContext K) : ℝ :=
  Classical.choose (exists_normTwistParameter K c)

/-- The target with its global norm twist removed (revised §6, first sentence). -/
def untwisted (c : TargetContext K) : HeckePacketIndex K c.family.omega :=
  ⟨c.target.val * heckeNormTwist K (-normTwistParameter K c),
    heckePacket_mul_normTwist K c.family.omega c.target.property _⟩

/-- The untwisted target is `θ ω^e` with `θ` of finite order. -/
theorem untwisted_eq (c : TargetContext K) :
    ∃ θ : HeckeCharacter K, FiniteOrder θ ∧ ∃ e : ℤ, PacketExponent e ∧
      (untwisted K c).val = θ * c.family.omega ^ e := by
  obtain ⟨θ, hθ, e, he, ht⟩ := Classical.choose_spec (exists_normTwistParameter K c)
  have ht' : c.target.val = θ * c.family.omega ^ e * heckeNormTwist K (normTwistParameter K c) :=
    ht
  refine ⟨θ, hθ, e, he, ?_⟩
  change c.target.val * heckeNormTwist K (-normTwistParameter K c) = _
  rw [ht']
  unfold heckeNormTwist
  rw [normTwist_neg, mul_inv_cancel_right]

theorem untwisted_zeros (c : TargetContext K) :
    heckePacketZeros K c.family.omega (untwisted K c) =
      heckePacketZeros K c.family.omega c.target :=
  zeroRealParts_heckeContinuation_normTwist K c.target.val _

/-- The primes where the untwisted target ramifies. Conjugation does not
change them, so the representative below ramifies at the same primes. -/
def targetRamifiedPlaces (c : TargetContext K) :
    Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  (finite_ramifiedPlaces K (untwisted K c).val).toFinset

/-- A complex embedding of `K`; the arithmetic choice below is made for it. -/
def complexEmbedding : K →+* ℂ := Classical.arbitrary (K →+* ℂ)

/-- ONE Axiom arithmetic choice for the target: it contains the target's
ramified primes, uses the family's twelfth root, and is shared by every
base datum below, so no second independent choice is made. -/
def axiomChoice (c : TargetContext K) :
    HeckeAxiom.ArithmeticChoice K (targetRamifiedPlaces K c) c.family.root12
      (complexEmbedding K) :=
  Classical.choice (HeckeAxiom.exists_arithmeticChoice K _ c.family.root12
    c.family.primitive12 _)

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

-- OBLIGATION D-EXPANSION | revised Proposition 6.3, §7.1–7.2 (pp.41–44).
-- Buffered blocks, true slot values and actual detector witness subdivisions.
-- Values are data only; exact identity and all bounds occur downstream.
def highExpansion (c : TargetContext K) : ℝ → ℝ →
    HighExpansion (FrequencyRow K (places K c)) c.geometry.slots := by
  sorry

-- OBLIGATION D-SUPPORT | revised §7.1 (pp.42–43).
theorem rows_in_norm_envelope (c : TargetContext K) :
    ∀ Z T₁ : ℝ, 1 ≤ Z → 1 ≤ T₁ →
    ∀ b : Fin (highExpansion K c Z T₁).blockCount,
    ∀ ℓ : ((highExpansion K c Z T₁).block b).Label,
      (((highExpansion K c Z T₁).block b).amplitudeSet ℓ).rows ⊆
        frequencyRows K (places K c) (2 * Z ^ ((highExpansion K c Z T₁).block b).shell) := by
  sorry

def targetData (c : TargetContext K) : TargetData K c.geometry where
  S := excludedPlaces K c
  probe := probeData K c
  measures := probeMeasures K c
  rayFilter := rayFilter K c
  expansion := highExpansion K c
  rows_in_norm_envelope := rows_in_norm_envelope K c

abbrev targetCharacter (c : TargetContext K) : HeckeCharacter K :=
  (representative K c).val.val

end HeckeSkeleton
