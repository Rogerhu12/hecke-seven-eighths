import ActualSexticOriginalChartMean
import HeckeGeneral.Analysis.SIntegerAnnularColumnFinite
import HeckeGeneral.Analysis.SIntegerAnnularSexticCosets

/-! UNCOMPILED / native 0. An exact finite outer chart decomposition of
the original two-column coefficient with its actual annular cutoffs.
The joint profile is never split. No coprimality or sum identity is an input.
The fixed S period is refined by the S-prime product so the verified
disjoint annular-coset theorem applies without dropping its refinement. -/

noncomputable section
namespace HeckeGeneral.Characters.ActualGramFamilyDraft
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open ActualGramJointChartDraft ActualGramJointChartCoverDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "MS" => sIntegerSexticSPlaceModulus K S ζ hζ

def chartPeriod : Ideal (𝓞 K) :=
  sIntegerAnnularSexticPeriod K S MS (⟨1, one_ne_zero⟩ : NZ)

def periodChart (b : NZ) : Set NZ :=
  {n | ∃ t : 𝓞 K, t ∈ chartPeriod K S ζ hζ ∧
    n.val - b.val = algebraMap (𝓞 K) (S.integer K) t}

theorem periodChart_subset_fixedSChart (b : NZ) :
    periodChart K S ζ hζ b ⊆ fixedSChart K S ζ hζ b := by
  rintro n ⟨t, ht, he⟩
  exact ⟨t, (Ideal.mul_le_right : chartPeriod K S ζ hζ ≤ MS) ht, he⟩

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "active" => fun n : NZ => Prod.snd (sLocalNonzeroIntegerDiagonal K S n) ∈
  finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)

/-- One fixed finite family partitions ALL active actual S-integers.
Its centers are chosen before the divisor, frequency, joint profile or scale. -/
theorem exists_disjoint_periodChart_family :
    ∃ T : Finset NZ,
      (∀ b ∈ T, active b) ∧
      (∀ n : NZ, active n ↔ ∃ b ∈ T, n ∈ periodChart K S ζ hζ b) ∧
      (∀ b ∈ T, ∀ c ∈ T, ∀ n : NZ,
        n ∈ periodChart K S ζ hζ b → n ∈ periodChart K S ζ hζ c → b = c) := by
  obtain ⟨T, hdisjoint, hcover⟩ :=
    exists_finite_sIntegerAnnular_period_representatives K S Γ MS
      (sIntegerSexticSPlaceModulus_ne_bot K S ζ hζ) (⟨1, one_ne_zero⟩ : NZ)
  refine ⟨T, ?_, hcover, ?_⟩
  · intro b hb
    exact (hcover b).mpr ⟨b, hb, 0, Ideal.zero_mem _, by simp⟩
  · intro b hb c hc n hn hc'
    by_contra hbc
    obtain ⟨t, ht, he⟩ := hn
    obtain ⟨u, hu, he'⟩ := hc'
    apply hdisjoint b hb c hc hbc
    refine ⟨u - t, (chartPeriod K S ζ hζ).sub_mem hu ht, ?_⟩
    rw [map_sub]
    linear_combination he' - he

/-- Multiplication by the actual nonzero divisor keeps every original
column index distinct; no unit or surjectivity is asserted. -/
theorem divisorColumn_injective (d : NZ) :
    Function.Injective (divisorColumn K S d) := by
  intro m n h
  apply Subtype.ext
  exact mul_left_cancel₀ d.property (congrArg Subtype.val h)

/-- Actual finite support after pulling the original annular column back
along the divisor. This does not replace its finite-place coordinate. -/
theorem finite_support_divisor_annularColumn (d : NZ)
    (a : ℝ → ℝ) (a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (ha : tsupport a ⊆ Set.Icc a₀ b₀) (r : ℝ) (hr : r ≠ 0) :
    Set.Finite (Function.support (fun m : NZ =>
      sIntegerAnnularColumn K S Γ a r (divisorColumn K S d m))) := by
  exact (finite_support_sIntegerAnnularColumn K S Γ a a₀ b₀ ha₀ ha r hr).preimage
    (divisorColumn_injective K S d).injOn

variable (σ : K →+* ℂ) (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- The original raw times actual R correction times residual extension,
with the TWO original annular factors and one unsplit joint profile. -/
def annularOriginalSummand (c k d : NZ) (a₁ a₂ : ℝ → ℝ) (r₁ r₂ : ℝ)
    (H : NZ × NZ → ℂ) (m : NZ × NZ) : ℂ :=
  originalChartCoefficient K S ζ hζ σ hS6 c k d m.1 m.2 *
    (sIntegerAnnularColumn K S Γ a₁ r₁ (divisorColumn K S d m.1) : ℂ) *
    (sIntegerAnnularColumn K S Γ a₂ r₂ (divisorColumn K S d m.2) : ℂ) * H m

/-- The whole literal two-column sum is a finite outer sum of its actual
chart restrictions. All inner sums have finite support, including for
arbitrary joint H; the theorem therefore uses no conditional tsum rearrangement.
The chart family precedes all moving data and preserves every zero mask. -/
theorem exists_sum_annularOriginal_eq_finite_charts :
    ∃ T : Finset NZ,
      (∀ b ∈ T, active b) ∧
      ∀ (c k d : NZ) (a₁ a₂ : ℝ → ℝ) (a₀ b₀ : ℝ),
        0 < a₀ → tsupport a₁ ⊆ Set.Icc a₀ b₀ → tsupport a₂ ⊆ Set.Icc a₀ b₀ →
        ∀ (r₁ r₂ : ℝ), r₁ ≠ 0 → r₂ ≠ 0 → ∀ H : NZ × NZ → ℂ,
        let F := annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a₁ a₂ r₁ r₂ H
        Summable F ∧
        (∀ b₁ ∈ T, ∀ b₂ ∈ T, Summable (fun m : NZ × NZ =>
          if divisorColumn K S d m.1 ∈ periodChart K S ζ hζ b₁ ∧
             divisorColumn K S d m.2 ∈ periodChart K S ζ hζ b₂ then F m else 0)) ∧
        (∑' m, F m) = ∑ b₁ ∈ T, ∑ b₂ ∈ T, ∑' m : NZ × NZ,
          if divisorColumn K S d m.1 ∈ periodChart K S ζ hζ b₁ ∧
             divisorColumn K S d m.2 ∈ periodChart K S ζ hζ b₂ then F m else 0 := by
  obtain ⟨T, hT, hcover, hdisjoint⟩ := exists_disjoint_periodChart_family K S ζ hζ Γ
  refine ⟨T, hT, ?_⟩
  intro c k d a₁ a₂ a₀ b₀ ha₀ ha₁ ha₂ r₁ r₂ hr₁ hr₂ H
  let F := annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a₁ a₂ r₁ r₂ H
  let A₁ := fun m : NZ => sIntegerAnnularColumn K S Γ a₁ r₁ (divisorColumn K S d m)
  let A₂ := fun m : NZ => sIntegerAnnularColumn K S Γ a₂ r₂ (divisorColumn K S d m)
  have hf₁ := finite_support_divisor_annularColumn K S Γ d a₁ a₀ b₀ ha₀ ha₁ r₁ hr₁
  have hf₂ := finite_support_divisor_annularColumn K S Γ d a₂ a₀ b₀ ha₀ ha₂ r₂ hr₂
  let R : Finset (NZ × NZ) := hf₁.toFinset ×ˢ hf₂.toFinset
  have hzero (m : NZ × NZ) (hm : m ∉ R) : F m = 0 := by
    by_cases hz : A₁ m.1 = 0
    ·
      change sIntegerAnnularColumn K S Γ a₁ r₁ (divisorColumn K S d m.1) = 0 at hz
      simp only [F, annularOriginalSummand, hz, Complex.ofReal_zero, mul_zero, zero_mul]
    · by_cases hz₂ : A₂ m.2 = 0
      · change sIntegerAnnularColumn K S Γ a₂ r₂ (divisorColumn K S d m.2) = 0 at hz₂
        simp only [F, annularOriginalSummand, hz₂, Complex.ofReal_zero, mul_zero, zero_mul]
      · exact False.elim (hm (Finset.mem_product.mpr
          ⟨hf₁.mem_toFinset.mpr hz, hf₂.mem_toFinset.mpr hz₂⟩))
  have hsupp : Function.support F ⊆ (R : Set (NZ × NZ)) := by
    intro m hm
    by_contra hn
    exact hm (hzero m hn)
  have hfinite : (Function.support F).Finite := R.finite_toSet.subset hsupp
  have hchartzero (b₁ b₂ : NZ) (m : NZ × NZ) (hm : m ∉ R) :
      (if divisorColumn K S d m.1 ∈ periodChart K S ζ hζ b₁ ∧
          divisorColumn K S d m.2 ∈ periodChart K S ζ hζ b₂ then F m else 0) = 0 := by
    simp only [hzero m hm, ite_self]
  refine ⟨summable_of_hasFiniteSupport hfinite, ?_, ?_⟩
  · intro b₁ _ b₂ _
    apply summable_of_hasFiniteSupport
    apply R.finite_toSet.subset
    intro m hm
    by_contra hn
    exact hm (hchartzero b₁ b₂ m hn)
  · have hpartition (m : NZ × NZ) :
        F m = ∑ b₁ ∈ T, ∑ b₂ ∈ T,
          if divisorColumn K S d m.1 ∈ periodChart K S ζ hζ b₁ ∧
              divisorColumn K S d m.2 ∈ periodChart K S ζ hζ b₂ then F m else 0 := by
      by_cases hF : F m = 0
      · simp [hF]
      have hA₁ : A₁ m.1 ≠ 0 := by
        intro hz
        change sIntegerAnnularColumn K S Γ a₁ r₁ (divisorColumn K S d m.1) = 0 at hz
        exact hF (by simp only [F, annularOriginalSummand, hz, Complex.ofReal_zero,
          mul_zero, zero_mul])
      have hA₂ : A₂ m.2 ≠ 0 := by
        intro hz
        change sIntegerAnnularColumn K S Γ a₂ r₂ (divisorColumn K S d m.2) = 0 at hz
        exact hF (by simp only [F, annularOriginalSummand, hz, Complex.ofReal_zero,
          mul_zero, zero_mul])
      have hactive {a : ℝ → ℝ} {r : ℝ} {n : NZ}
          (hn : sIntegerAnnularColumn K S Γ a r n ≠ 0) : active n := by
        by_contra hnot
        exact hn (congrFun (sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box
          K S Γ a _ hnot) _)
      obtain ⟨b₁, hb₁, h₁⟩ := (hcover _).mp (hactive hA₁)
      obtain ⟨b₂, hb₂, h₂⟩ := (hcover _).mp (hactive hA₂)
      rw [Finset.sum_eq_single_of_mem b₁ hb₁]
      · rw [Finset.sum_eq_single_of_mem b₂ hb₂]
        · simp only [h₁, h₂, and_self, ite_true]
        · intro b hb hne
          have hn : divisorColumn K S d m.2 ∉ periodChart K S ζ hζ b := by
            intro hn
            exact hne (hdisjoint b hb b₂ hb₂ _ hn h₂)
          simp only [hn, and_false, ite_false]
      · intro b hb hne
        have hn : divisorColumn K S d m.1 ∉ periodChart K S ζ hζ b := by
          intro hn
          exact hne (hdisjoint b hb b₁ hb₁ _ hn h₁)
        simp only [hn, false_and, ite_false, Finset.sum_const_zero]
    rw [tsum_eq_sum hzero]
    have hts : ∀ b₁ b₂ : NZ,
        (∑' m : NZ × NZ, if divisorColumn K S d m.1 ∈ periodChart K S ζ hζ b₁ ∧
            divisorColumn K S d m.2 ∈ periodChart K S ζ hζ b₂ then annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a₁ a₂ r₁ r₂ H m else 0) =
          ∑ m ∈ R, if divisorColumn K S d m.1 ∈ periodChart K S ζ hζ b₁ ∧
            divisorColumn K S d m.2 ∈ periodChart K S ζ hζ b₂ then annularOriginalSummand K S ζ hζ Γ σ hS6 c k d a₁ a₂ r₁ r₂ H m else 0 :=
      fun b₁ b₂ => tsum_eq_sum (hchartzero b₁ b₂)
    simp only [hts]
    calc
      _ = ∑ m ∈ R, ∑ b₁ ∈ T, ∑ b₂ ∈ T,
          if divisorColumn K S d m.1 ∈ periodChart K S ζ hζ b₁ ∧
              divisorColumn K S d m.2 ∈ periodChart K S ζ hζ b₂ then F m else 0 :=
        Finset.sum_congr rfl (fun m _ => hpartition m)
      _ = _ := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _;
                  rw [Finset.sum_comm]

end HeckeGeneral.Characters.ActualGramFamilyDraft
