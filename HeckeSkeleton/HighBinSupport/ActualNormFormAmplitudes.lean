import HeckeSkeleton.HighBinSupport.ActualNormFormSlotCap
import HeckeSkeleton.HighBinSupport.ActualBoundaryIntegrability
import HeckeSkeleton.HighBinSupport.HighNormFormAmplitude

/-!
Actual full-slot maxima on the fixed three-height contour box.

Every selected local denominator is made nonzero by the same large-scale
cutoff. This gives continuity of the literal complete correction slot,
including all regular and ramified terms. Compactness then produces an
actual maximizing contour point in every row and slot. The detector cap
is applied to those points rather than supplied as a new analytic input.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinVerified.NormFormAmplitudes

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.ActualIntegrability
open NormFormActual NormFormFullCorrection
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def actualSlotHeightProfile (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z a e : ℝ) (i : Fin g.slots)
    (q : ℝ × (ℝ × ℝ)) : ℂ :=
  actualFullCorrectionSlot K S P psi g T u Z
    (sLine (a + 16 * e) q) (wLine (1 - a - 6 * e) q) (zLine q) i

theorem actual_localFactor_continuousOn
    (P : ProbeData K S) (psi : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    {a e : ℝ} (ha : 51 / 100 ≤ a) (he : 0 ≤ e) (p : ExteriorPrime K S) :
    ContinuousOn (localFactor K S P psi Q u p) (sweptTube a e) := by
  have hc := (explicitLocalEuler_analyticOnNhd (exteriorSupport K S u.ideal) Q
    (fun p : ExteriorPrime K S => (p.val.asIdeal.absNorm : ℝ))
    (rowW K S P u) (rowD K S P psi u) (rowE K S P psi)
    (rowPhaseData K S P psi u) (rowIndex K S u)
    (exteriorPrime_norm_two_le K S) ha he (rowD_norm K S P psi u)
    (rowE_norm K S P psi) p).continuousOn
  exact hc.congr (fun v hv => localFactor_eq_explicit K S P psi Q u ha he p v hv)

/-- One cutoff gives continuity for every actual complete slot on the
entire real three-height space. Only its compact restriction is used to
choose amplitudes. -/
theorem exists_actualSlotHeightProfile_continuous (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K)
        (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (a : ℝ),
      51 / 100 ≤ a → a ≤ 1 → ∀ i : Fin g.slots,
        Continuous (actualSlotHeightProfile K S P psi g T u Z a e i) := by
  obtain ⟨Z0, hZ0, hnonzero⟩ := exists_window_unmarked_nonzero K S g he he1
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ P psi T u a ha ha1 i
  let F : (ℝ × (ℝ × ℝ)) → ℂ × ℂ × ℂ :=
    fun q => (sLine (a + 16 * e) q, wLine (1 - a - 6 * e) q, zLine q)
  have hF : Continuous F := (continuous_sLine _).prodMk
    ((continuous_wLine _).prodMk continuous_zLine)
  have hFmem : ∀ q, F q ∈ sweptTube a e := by
    intro q
    apply swept_contour_mem_tube he le_rfl
    · simp [F, sLine]
    · simp [F, wLine]
    · norm_num [F, zLine]
  have hlocal (Q : Finset (ExteriorPrime K S)) (p : ExteriorPrime K S) :
      Continuous (fun q => localFactor K S P psi Q u p (F q)) :=
    (actual_localFactor_continuousOn K S P psi Q u ha he.le p).comp_continuous hF hFmem
  unfold actualSlotHeightProfile actualFullCorrectionSlot
  apply continuous_finsetSum
  intro p hp
  have hq0 : (0 : ℝ) < p.val.asIdeal.absNorm := by
    exact_mod_cast lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)
  have hqC : (p.val.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)).ne'
  have hmarked : Continuous (fun q => slotMarkedScalar K S psi
      (sLine (a + 16 * e) q) (zLine q) p) := by
    unfold slotMarkedScalar
    exact ((((continuous_sLine _).add continuous_zLine).sub (continuous_const (y := (1 : ℂ)))).const_cpow
      (Or.inl hqC)).const_mul _
  have hselected : Continuous (fun q => slotSelectedScalar K S
      (wLine (1 - a - 6 * e) q) (zLine q) p) := by
    unfold slotSelectedScalar
    exact ((continuous_zLine.sub (continuous_wLine _)).sub (continuous_const (y := (1 : ℂ)))).const_cpow (Or.inl hqC)
  have hH : Continuous (fun q => actualLocalUnmarked K S P psi u
      (sLine (a + 16 * e) q) (wLine (1 - a - 6 * e) q) (zLine q) p) := hlocal ∅ p
  have hM : Continuous (fun q => actualLocalMarked K S P psi u
      (sLine (a + 16 * e) q) (wLine (1 - a - 6 * e) q) (zLine q) p) := hlocal {p} p
  have hn : ∀ q, actualLocalUnmarked K S P psi u
      (sLine (a + 16 * e) q) (wLine (1 - a - 6 * e) q) (zLine q) p ≠ 0 := by
    intro q
    exact hnonzero Z hZ P psi T u a ha ha1 _ _ _ (hFmem q) i p hp
  exact (((hmarked.mul hM).sub (hselected.mul hH)).div hH hn).const_mul _

/-- Each actual full slot attains its height maximum. The selected
contour point can depend on the row and slot, while the scale cutoff
was chosen uniformly before both. -/
theorem exists_actual_fullSlot_maximizers (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K)
        (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S) (a H : ℝ),
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H →
      ∃ q : Fin g.slots → ℝ × (ℝ × ℝ),
        (∀ i, q i ∈ heightBox H) ∧ ∀ i, ∀ x ∈ heightBox H,
          ‖actualSlotHeightProfile K S P psi g T u Z a e i x‖ ≤
            ‖actualSlotHeightProfile K S P psi g T u Z a e i (q i)‖ := by
  obtain ⟨Z0, hZ0, hc⟩ := exists_actualSlotHeightProfile_continuous K S g he he1
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ P psi T u a H ha ha1 hH
  have hne : (heightBox H).Nonempty := by
    refine ⟨(0, 0, 0), ?_⟩
    change ((-H ≤ (0 : ℝ) ∧ 0 ≤ H) ∧ (-H ≤ (0 : ℝ) ∧ 0 ≤ H) ∧
      (-H ≤ (0 : ℝ) ∧ 0 ≤ H))
    constructor
    · constructor <;> linarith
    · constructor <;> constructor <;> linarith
  have hm (i : Fin g.slots) : ∃ q ∈ heightBox H, ∀ x ∈ heightBox H,
      ‖actualSlotHeightProfile K S P psi g T u Z a e i x‖ ≤
        ‖actualSlotHeightProfile K S P psi g T u Z a e i q‖ :=
    (heightBox_isCompact H).exists_isMaxOn hne (hc Z hZ P psi T u a ha ha1 i).norm.continuousOn
  choose q hq hmax using hm
  exact ⟨q, hq, hmax⟩

/-- The maximizing values of the complete actual slots obey the proved
detector cap. Thus neither compact maximizers nor a uniform prime-sum
estimate remains an abstract input to the later finite amplitude grid. -/
theorem exists_actual_fullSlot_maximizers_with_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val)
    {e eps eta kappa : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a H U : ℝ, 51 / 100 ≤ a → a ≤ 1 → 0 ≤ H →
      NormForm.internalHeight Z T kappa + H + 2 ≤ U →
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u U (a + 2 * e) →
      ∃ q : Fin g.slots → ℝ × (ℝ × ℝ),
        (∀ i, q i ∈ heightBox H) ∧
        (∀ i, ∀ x ∈ heightBox H,
          ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i x‖ ≤
            ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i (q i)‖) ∧
        ∀ i, ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i (q i)‖ ≤
          C * frequencyRowNorm K S u ^ (eps + eta) *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) *
            (primeScale g Z) ^ (a - 33 / 50 + 8 * e + eta) := by
  obtain ⟨ZM, hZM, hmax⟩ := exists_actual_fullSlot_maximizers K S g he he1
  obtain ⟨C, ZC, hC, hZC, hcap⟩ := NormFormSlotCap.exists_actualFullCorrectionSlot_power_cap
    K S psi companions hcomp P g hcal hpsi he he1 heps heta hkappa
  refine ⟨C, max ZM ZC, hC, hZM.trans (le_max_left _ _), ?_⟩
  intro Z T hZ d hd u hu a H U ha ha1 hH hU hbelow
  obtain ⟨q, hq, hqmax⟩ := hmax Z ((le_max_left _ _).trans hZ) P psi ∅ u a H ha ha1 hH
  refine ⟨q, hq, hqmax, ?_⟩
  intro i
  have hzi : |(zLine (q i)).im| ≤ H := by
    have h := abs_le.mpr (hq i).2.2
    simpa [zLine] using h
  exact hcap Z T ((le_max_right _ _).trans hZ) d hd u hu a U ha ha1
    (sLine (a + 16 * e) (q i)) (wLine (1 - a - 6 * e) (q i)) (zLine (q i))
    (by simp [sLine]) (by simp [wLine]) (by norm_num [zLine])
    (by linarith) hbelow i

end HighBinVerified.NormFormAmplitudes

#print axioms HighBinVerified.NormFormAmplitudes.exists_actualSlotHeightProfile_continuous
#print axioms HighBinVerified.NormFormAmplitudes.exists_actual_fullSlot_maximizers
#print axioms HighBinVerified.NormFormAmplitudes.exists_actual_fullSlot_maximizers_with_cap
