import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodeStep
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionLong

/-!
# Assemble the literal short and long contributions into a local step

This assembly lemma is separate from the analytic short-contribution
theorem. Its supplied estimate is explicitly on `TerminalNodes.shortEnergy`
of the same actual node; it is never an arbitrary terminal energy. The
long completed contribution and the nonterminal-label branch are supplied
here by their proved actual-provider theorems. The resulting implication
has precisely the constant, margin, capacity and row schedule consumed
by `ProviderInduction`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderLocalStep

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_INV_STEP
open ProviderNodes CubeCompletionGeometry
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
variable (Θ : Subgroup (HeckeCharacter K)) (ψ Λ G : HeckeCharacter K)

include hΓ hallowed μv ν μ in
/-- Convert the actual uniform short-contribution estimate and the
two proved provider branches into the exact backwards-induction local
implication. The original test is controlled by one finite seminorm
chosen before the node and before its scale vary. -/
theorem exists_uniform_local_step_of_short_contribution
    (hG : G ∈ Θ) (slotCap : ℕ) (A pi tauMin cLower z lo hi d Z₀ : ℝ)
    (hA : 1 ≤ A) (hpi : 0 < pi) (htauMin : 0 < tauMin)
    (qShort : Finset (ℕ × ℕ)) (CShort : ℝ) (hCShort : 0 ≤ CShort)
    (hshort : ∀ {σ : Type u} (Z Fcap c : ℝ) (x : Node K S Γ Θ ψ σ),
      Z₀ ≤ Z → Fcap ≤ A → cLower ≤ c →
      x.Admissible D Λ G slotCap Z Fcap c z lo hi → x.labelLength < d →
      TerminalNodes.shortEnergy K S Γ D slotCap x (Z ^ d) ≤
        CShort * (qShort.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 * Z ^ x.totalLength)
    (t : Finset (ℕ × ℕ)) :
    ∃ q : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Z Fcap c eta h tau eps Cih Rmax : ℝ),
      2 ≤ Z → Z₀ ≤ Z → Fcap ≤ A → cLower ≤ c → 0 ≤ c - eta / 2 → 0 ≤ z →
      h ∈ Set.Icc (0 : ℝ) 1 → tau ∈ Set.Icc (0 : ℝ) A → tauMin ≤ tau →
      2 ≤ Z ^ h → h ≤ eta / 128 → eta ≤ d / 16 →
      0 ≤ eps → 1 ≤ Cih →
      (∀ i : SchwartzTestPartition.Index, |Real.logb Z (annularScale i)| ≤ eta / 8) →
      UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
        (Fcap + 11 * eta) (c - 7 * eta) z lo hi eps (Rmax - d) Cih t →
      UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
        Fcap c z lo hi (eps + (40 * eta + tau + pi)) Rmax (3 * C * Cih) q := by
  obtain ⟨qLabel, CLabel, hCLabel, hlabel⟩ := ProviderNodeStep.exists_uniform_long_label_step
    K S D Γ hΓ hallowed μv ν μ slotCap A pi tauMin hA hpi htauMin t
  obtain ⟨qCube, CCube, hCCube, hcube⟩ := CubeCompletionLong.exists_uniform_long_cube_step
    K S D Γ hΓ hallowed μv ν μ slotCap A pi tauMin hA hpi htauMin t
  let q := qLabel ∪ qCube ∪ qShort
  let C := CLabel + CCube + CShort
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨q, C, hC, ?_⟩
  intro Z Fcap c eta h tau eps Cih Rmax hZ hZ₀ hFcap hcLower hc hz
    hh htau htau' hwidth hmesh hstepsize heps hCih hshift hih
  intro σ x hx hrow
  have hz1 : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hz0 := zero_lt_one.trans hz1
  have heta : 0 ≤ eta := by linarith [hh.1]
  have hc0 : 0 ≤ c := by linarith
  have hCih0 : 0 ≤ Cih := zero_le_one.trans hCih
  have hqLabel : qLabel.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left.trans Finset.subset_union_left)) _
  have hqCube : qCube.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right.trans Finset.subset_union_left)) _
  have hqShort : qShort.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test ≤
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) _
  have hexp : x.totalLength + eps + (40 * eta + tau + pi) =
      x.totalLength + 40 * eta + tau + pi + eps := by ring
  change x.energy D slotCap ≤ (3 * C * Cih) *
    (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
      Z ^ (x.totalLength + (eps + (40 * eta + tau + pi)))
  rw [show x.totalLength + (eps + (40 * eta + tau + pi)) =
    x.totalLength + 40 * eta + tau + pi + eps by ring]
  by_cases hlong : d ≤ x.labelLength
  · have hp := hlabel Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x
      hZ hFcap hc0 hz hx hrow hh htau htau' hwidth (by linarith) hstepsize hlong heps hCih hih
    apply hp.trans
    gcongr
    · dsimp only [C]; linarith
  · have hshort' := hshort Z Fcap c x hZ₀ hFcap hcLower hx (lt_of_not_ge hlong)
    have hcube' := hcube Θ ψ Λ G hG Z Fcap c z lo hi d eta h tau eps Cih Rmax x
      hZ hFcap hc hz hx hrow hh htau htau' hwidth hmesh hstepsize heps hCih hih hshift
    let E := (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
      Z ^ (x.totalLength + 40 * eta + tau + pi + eps)
    have hE : 0 ≤ E := by dsimp only [E]; positivity
    have hs : TerminalNodes.shortEnergy K S Γ D slotCap x (Z ^ d) ≤ CShort * Cih * E := by
      apply hshort'.trans
      calc
        _ ≤ (CShort * Cih) * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
            Z ^ (x.totalLength + 40 * eta + tau + pi + eps) := by
          gcongr
          · exact le_mul_of_one_le_right hCShort hCih
          · exact hz1.le
          · linarith [htau.1]
        _ = _ := by dsimp only [E]; ring
    have hl : TerminalNodes.longEnergy K S Γ D slotCap x (Z ^ d) ≤ CCube * Cih * E := by
      apply hcube'.trans
      dsimp only [E]
      rw [← mul_assoc]
      gcongr
    have hsplit := TerminalNodes.energy_le_short_long K S Γ D Λ G slotCap Z Fcap c z lo hi x hx hz0 (Z ^ d)
    apply hsplit.trans
    calc
      _ ≤ 2 * (CShort * Cih * E + CCube * Cih * E) := by gcongr
      _ = (2 * (CShort + CCube)) * Cih * E := by ring
      _ ≤ (3 * C) * Cih * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply mul_le_mul_of_nonneg_right _ hCih0
        dsimp only [C]
        linarith
      _ = _ := by dsimp only [E]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderLocalStep
