import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedPacket

/-!
# Uniform energy of the whole original marked ideal source

The original common-slot decomposition, fixed annular partition, actual
complete-row initial estimate, and literal common-tuple count are all
consumed here.  In particular the sum over extracted ideals is paid by
the exact original square-root normalization.  No initial or terminal
source energy is an additional premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedRawBound

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP AssignedMarkSource
open SourceActualArithmetic ProviderNodes ProviderMarkedSlots ProviderMarkedReindex
  ProviderMarkedTupleSplit ProviderMarkedAnnuli ProviderMarkedPacket
  ProviderMarkedSourceSplit ProviderMarkedTests
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "S" => excludedPlaces K c
local notation "Sset" => places K c
local notation "P" => probeData K c
local notation "D" => (probeData K c).arithmetic
local notation "Γ" => sixthPowerSUnitSubgroup K Sset
local notation "Θ" => twists K c
local notation "ψ" => targetCharacter K c

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar

local instance normOneSpace : MeasurableSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneSpace
local instance normOneBorel : BorelSpace (sLocalNormOneGroup K Sset) :=
  (probeMeasures K c).normOneBorel
local instance principal : IsPrincipalIdealRing (Set.integer Sset K) :=
  (axiomChoice K c).C.principal

/-- All constants, including the Fourier order, precede the original
source and its rowwise radial parameters.  The only analytic input is
the already proved uniform actual canonical estimate. -/
theorem exists_raw_bound
    (slotCap : ℕ) (gap eps : ℝ) (hgap : 0 < gap) (heps : 0 < eps)
    (t : Finset (ℕ × ℕ)) (Cih Zih : ℝ) (hCih : 1 ≤ Cih) (hZih : 2 ≤ Zih)
    (hih : ∀ Z : ℝ, Zih ≤ Z → ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      UniformBound.{0} (Γ := Γ) (Θ := Θ) (ψ := ψ) D P.Lambda P.G slotCap Z 2
        (3 * gap / 4) z (1 / 2) 2 (eps / 2) 2 Cih t) :
    ∃ degree : ℕ, ∃ C Z₀ : ℝ, 0 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ (d : MomentData K c.family.omega ψ) (sector : SixthUnitClasses K Sset),
      d.direction = 1 →
      d.rowCharacter = completeIdealRowCharacter K Sset P (momentRowCharacters K c) sector →
      d.commonMask = completeIdealCommonMask K Sset →
      d.allowedRow = completeIdealIsExterior K Sset →
      BackgroundCycle.Admissible K Θ ψ d.inverseBackground⁻¹ →
      ∀ (Z T m r z : ℝ), Z₀ ≤ Z → 0 ≤ T → 0 ≤ m → m ≤ 2 → z ≤ 1 →
      r + 2 * z ≤ m - 2 * gap → 2 * r + 8 * z ≤ 3 * m - 2 * gap →
      ∀ (s : Slots K S slotCap Z z) (good : HeightOneSpectrum (𝓞 K) → Prop),
      (∀ u ∈ d.rows (Z ^ m), ∀ n, maskValue d u n = ProviderMarkedMask.value good u.val n) →
      (∀ u ∈ d.rows (Z ^ m), ∀ n : NonzeroIdeal K, d.commonMask u n.val = true →
        ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ n.val → UnramifiedAt K d.inverseBackground p) →
      ∀ (baseParam scaleParam ar ni xi : NonzeroIdeal K → ℝ),
      (∀ u ∈ d.rows (Z ^ m), 0 < baseParam u) →
      (∀ u ∈ d.rows (Z ^ m), 0 ≤ scaleParam u) →
      (∀ u ∈ d.rows (Z ^ m), |ar u| ≤ 8) →
      (∀ u ∈ d.rows (Z ^ m), |ni u| ≤
        |(expansionRecipeRaw K c).family.frequencyScale| * (1 + T)) →
      (∀ u ∈ d.rows (Z ^ m), ∀ y : ℝ, 0 < y →
        ProviderMarkedLogMellin.profile
          (actualInverseLogProfile (baseParam u) (scaleParam u) (ar u) (ni u) (xi u)) y ≠ 0 →
        1 / 2 ≤ y ∧ y ≤ 2) →
      Z ^ (-r - z) * (∑ u ∈ d.rows (Z ^ m),
        ‖rawSource (d.inverseBackground * d.rowCharacter u) s.lists s.weight good u.val
          (Z ^ r) (ProviderMarkedLogMellin.profile
            (actualInverseLogProfile (baseParam u) (scaleParam u) (ar u) (ni u) (xi u)))‖ ^ 2) ≤
        C * ((1 + T) ^ (degree + 2)) ^ 2 * Z ^ (m + eps) := by
  obtain ⟨q, CP, Z₀, hCP, hZ₀, hphysical⟩ :=
    SourceMarkedComplete.annular_bound_of_uniform K c slotCap gap eps
      (supportConstant slotCap) hgap heps (supportConstant_ge_one slotCap)
      t Cih Zih hCih hZih hih
  obtain ⟨degree, CT, hCT, htest⟩ := piece_polynomial_seminorm q
  obtain ⟨CF, hCF, hfourier⟩ := SourceMarkedBlockEnergy.exists_block_bound K c degree
  obtain ⟨A, hA, hcount⟩ := ProviderMarkedCount.exists_original_tuple_count (K := K)
  let M : ℝ := supportConstant slotCap * (A * (2 : ℝ) ^ slotCap) ^ 2
  let C : ℝ := ((2 : ℝ) ^ slotCap) ^ 2 * ((blocks slotCap).card : ℝ) ^ 2 *
    M * CF * CP * CT ^ 2
  have hM : 0 ≤ M := mul_nonneg (by linarith [supportConstant_ge_one slotCap]) (sq_nonneg _)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨degree, C, Z₀, hC, hZ₀, ?_⟩
  intro d sector hdir hchar hmask₀ hrows hbackground Z T m r z hZ hT hm0 hm2 hz1 hf hg
    s good hmask hν baseParam scaleParam ar ni xi hbase hscale har hni hprofile
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := zero_lt_one.trans_le hZ1
  have hR (G : ℝ) : 0 < Z ^ ProviderMarkedScale.columnLength r z G :=
    Real.rpow_pos_of_pos hZp _
  have hX : 0 < Z ^ r := Real.rpow_pos_of_pos hZp _
  let rows := d.rows (Z ^ m)
  let F : NonzeroIdeal K → SchwartzMap ℝ ℂ := fun u =>
    actualInverseLogProfile (baseParam u) (scaleParam u) (ar u) (ni u) (xi u)
  let Y : Finset (Fin s.count) → ℝ := fun J =>
    supportConstant slotCap * Z ^ ProviderMarkedScale.columnLength r z (s.commonLength J)
  let E₀ : ℝ := CP * CT ^ 2 * Z ^ (m + eps)
  let E : ℝ := CF * ((1 + T) ^ (degree + 2)) ^ 2 * E₀
  let w : ∀ J : Finset (Fin s.count), (Fin J.card → HeightOneSpectrum (𝓞 K)) → ℂ :=
    fun J q => choiceWeight (fun i => s.weight (slot J i)) q
  let f : ∀ J : Finset (Fin s.count), (Fin J.card → HeightOneSpectrum (𝓞 K)) →
      ℕ → NonzeroIdeal K → ℂ := fun J q k u =>
    SourceMarkedBlockEnergy.block d (s.residualLists J) (s.residualWeight J) good
      (primeProduct Finset.univ q) (Z ^ r)
      (scale slotCap k * Z ^ ProviderMarkedScale.columnLength r z (s.commonLength J)) F u
  have hY (J : Finset (Fin s.count)) : 0 < Y J := by
    dsimp only [Y]
    exact mul_pos (zero_lt_one.trans_le (supportConstant_ge_one slotCap)) (hR _)
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hFupper (u : NonzeroIdeal K) (hu : u ∈ rows) :
      Function.support (ProviderMarkedLogMellin.profile (F u)) ⊆ Set.Iic 2 := by
    intro y hy
    by_cases hy0 : 0 < y
    · exact (hprofile u hu y hy0 hy).2
    · exact (le_of_not_gt hy0).trans (by norm_num)
  have hblock (J : Finset (Fin s.count))
      (q₀ : Fin J.card → HeightOneSpectrum (𝓞 K)) (hq₀ : q₀ ∈ s.commonTuples J)
      (k : ℕ) (hk : k ∈ blocks slotCap) :
      (∑ u ∈ rows, ‖f J q₀ k u‖ ^ 2) ≤ Y J * E := by
    let j := primeProduct Finset.univ q₀
    let G := s.commonLength J
    let U := scale slotCap k * Z ^ ProviderMarkedScale.columnLength r z G
    let Pcap := Y J * ProviderMarkedPools.norm j / Z ^ r
    have hj : Squarefree j := s.common_squarefree J q₀ hq₀
    have hjp := ProviderMarkedPools.norm_pos hj.ne_zero
    have hU : 0 < U := mul_pos (scale_pos slotCap k) (hR G)
    have hPcap (p : Fin (remaining J).card → HeightOneSpectrum (𝓞 K))
        (hp : p ∈ tuples (s.residualLists J)) :
        ProviderMarkedPools.norm (primeProduct Finset.univ p) ≤ Pcap :=
      product_cap slotCap Z r z G (ProviderMarkedPools.norm j)
        (ProviderMarkedPools.norm (primeProduct Finset.univ p)) hZp
        (s.common_window hZp J q₀ hq₀).1 (s.residual_window hZp J p hp).2
    have hYeq : Z ^ r * Pcap / ProviderMarkedPools.norm j = Y J := by
      dsimp only [Pcap]
      field_simp [hX.ne', hjp.ne']
    have hUi (i : SchwartzTestPartition.Index) :
        SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U ≤ Y J := by
      simpa only [columnScale, SourceScaleBudget.annularScale, U, G, Y, mul_assoc] using
        columnScale_upper slotCap k hk i Z r z (s.commonLength J) hZp
    have hpieces (t₀ : ℝ) (i : SchwartzTestPartition.Index) :
        (∑ u ∈ rows, ‖SourceMarkedPhysical.polynomial K d
          (SourceMarkedPhysical.mark Finset.univ
            (fun a => (s.residualLists J a).image HeightOneSpectrum.asIdeal)
            (ProviderMarkedMellin.primeWeight (s.residualWeight J) t₀) j)
          u (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U)
          (piece t₀ i)‖ ^ 2) ≤ E₀ * ((1 + |t₀|) ^ degree) ^ 2 := by
      have hb := hphysical d sector hdir hchar hmask₀ hrows hbackground Finset.univ
        (fun a => (s.residualLists J a).image HeightOneSpectrum.asIdeal)
        (ProviderMarkedMellin.primeWeight (s.residualWeight J) t₀) (s.residualLength J)
        j hj.ne_zero Z (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U)
        m r z G hZ (mul_pos (SchwartzTestPartition.scale_pos _) hU) hm0 hm2
        (s.commonLength_nonneg J) (s.commonLength_le J) hz1 hf hg
        (s.common_norm_le hZp J q₀ hq₀) (hUi i) (s.residual_marks J t₀)
        (piece t₀ i) (piece_support t₀ i)
      calc
        _ ≤ CP * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (piece t₀ i)) ^ 2 *
            Z ^ (m + eps) := hb
        _ ≤ CP * (CT * (1 + |t₀|) ^ degree) ^ 2 * Z ^ (m + eps) := by
          gcongr
          exact htest t₀ i
        _ = _ := by dsimp only [E₀]; ring
    have hb := hfourier d rows hdir good hmask hν (s.residualLists J)
      (s.residual_disjoint J) (s.residualWeight J) j hj
      (fun p hp => s.common_coprime J q₀ hq₀ p hp)
      (Z ^ r) U Pcap (Y J) T E₀ hX hU (hY J).le hT hE₀ hPcap hYeq hUi
      baseParam scaleParam ar ni xi hbase hscale har hni hFupper hpieces
    exact hb.trans_eq (by dsimp only [E]; ring)
  have hmass (J : Finset (Fin s.count)) :
      Z ^ (-r - z) * ((s.commonTuples J).card : ℝ) ^ 2 * Y J ≤ M := by
    have hn := hcount J.card (restrictedLists J s.lists)
      (fun i => s.length (slot J i)) Z (restrictedLists_disjoint J s.lists s.disjoint)
      hZ1 (fun i => s.length_nonneg (slot J i))
      (fun i p hp => (s.window (slot J i) p hp).2)
    have hn' : ((s.commonTuples J).card : ℝ) ≤
        (A * (2 : ℝ) ^ slotCap) * Z ^ s.commonLength J := by
      rw [ProviderMarkedWindows.restriction_sum] at hn
      exact hn.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) (s.subset_card J)) (zero_le_one.trans hA))
        (Real.rpow_nonneg hZp.le _))
    exact ProviderMarkedMass.normalization_mass Z r z (s.commonLength J)
      (A * (2 : ℝ) ^ slotCap) ((s.commonTuples J).card : ℝ)
      (supportConstant slotCap) hZp (Nat.cast_nonneg _)
      (zero_le_one.trans (supportConstant_ge_one slotCap)) hn'
  have hraw (u : NonzeroIdeal K) (hu : u ∈ rows) :
      rawSource (d.inverseBackground * d.rowCharacter u) s.lists s.weight good u.val
        (Z ^ r) (ProviderMarkedLogMellin.profile (F u)) =
        ∑ J ∈ (Finset.univ : Finset (Fin s.count)).powerset,
          ∑ q₀ ∈ s.commonTuples J, w J q₀ * ∑ k ∈ blocks slotCap, f J q₀ k u := by
    rw [source_eq_selected _ s.lists s.disjoint]
    apply Finset.sum_congr rfl
    intro J hJ
    apply Finset.sum_congr rfl
    intro q₀ hq₀
    congr 1
    exact selected_eq_blocks slotCap d u (s.residualLists J) (s.residualWeight J) good
      (primeProduct Finset.univ q₀) F Z r z (s.commonLength J) hZp
      (s.common_window hZp J q₀ hq₀) (s.residual_window hZp J)
      (fun p hp => (s.residual_squarefree J p hp).ne_zero) (hprofile u hu)
  have hsum := ProviderMarkedMass.selected_sum_energy rows
    (Finset.univ : Finset (Fin s.count)).powerset s.commonTuples (blocks slotCap) w f
    (Z ^ (-r - z)) M E Y (Real.rpow_nonneg hZp.le _) hM hE
    (fun J _ => (hY J).le) (fun J _ q₀ hq₀ => s.common_weight_norm J q₀ hq₀)
    (fun J _ => hmass J) (fun J _ q₀ hq₀ k hk => hblock J q₀ hq₀ k hk)
  have hcard : (((Finset.univ : Finset (Fin s.count)).powerset).card : ℝ) ≤
      (2 : ℝ) ^ slotCap := by
    simp only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) s.count_le
  calc
    _ = Z ^ (-r - z) * (∑ u ∈ rows,
        ‖∑ J ∈ (Finset.univ : Finset (Fin s.count)).powerset,
          ∑ q₀ ∈ s.commonTuples J, w J q₀ * ∑ k ∈ blocks slotCap, f J q₀ k u‖ ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      rw [hraw u hu]
    _ ≤ (((Finset.univ : Finset (Fin s.count)).powerset).card : ℝ) ^ 2 *
        ((blocks slotCap).card : ℝ) ^ 2 * M * E := hsum
    _ ≤ ((2 : ℝ) ^ slotCap) ^ 2 * ((blocks slotCap).card : ℝ) ^ 2 * M * E := by
      gcongr
    _ = _ := by dsimp only [C, E, E₀]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedRawBound

end
