import HeckeGeneral.Analysis.TIPClosure
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import HeckeSkeleton.ActualHeckeNormPullback
import HeckeSkeleton.Descent.ArtinFactors
import HeckeSkeleton.Descent.PoleMatching
import HeckeGeneral.Analysis.HeckeEulerDeletion

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Descent
open NumberField Filter IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators Topology
variable (F : Type) [Field F] [NumberField F]

abbrev Extension := CyclotomicField 12 F
instance : FiniteDimensional F (Extension F) :=
  IsCyclotomicExtension.finiteDimensional ({12} : Set ℕ) F (Extension F)
instance : IsAbelianGalois F (Extension F) :=
  IsCyclotomicExtension.isAbelianGalois ({12} : Set ℕ) F (Extension F)
def root12 : Extension F := IsCyclotomicExtension.zeta 12 F (Extension F)
theorem primitive_root12 : IsPrimitiveRoot (root12 F) 12 :=
  IsCyclotomicExtension.zeta_spec 12 F (Extension F)

-- OBLIGATION DE-NORM-MIGRATION | revised Lemma 2.1, p.2.
-- The actual relative idele-class norm from the audited ActualHeckeNormPullback
-- (GeneratorInputs), compiled here over its registered CFT closure.
def normOnClasses : NumberField.IdeleClassGroup (𝓞 (Extension F)) (Extension F) →ₜ*
    NumberField.IdeleClassGroup (𝓞 F) F :=
  HeckeGeneral.Characters.NormPullbackDraft.mathlibIdeleClassNorm F (Extension F)

def normPullback : HeckeCharacter F →* HeckeCharacter (Extension F) :=
  pullbackHom (normOnClasses F)

-- OBLIGATION DE-ARTIN-CHARACTERS | revised Lemma 2.1, p.2.
-- Actual finite characters of Gal(F(zeta12)/F), viewed through CFT.
-- The full finite dual of the actual norm quotient, via global reciprocity.
def artinCharacters : Finset (HeckeCharacter F) :=
  Artin.artinCharacters F (Extension F)

-- OBLIGATION DE-TRIVIAL-FACTOR | revised Lemma 2.1, p.2.
theorem one_mem_artinCharacters : (1 : HeckeCharacter F) ∈ artinCharacters F := by
  exact Artin.one_mem_artinCharacters F (Extension F)

def factors (χ : HeckeCharacter F) : Finset (HeckeCharacter F) :=
  (artinCharacters F).image (fun δ => χ * δ)

theorem target_mem_factors (χ : HeckeCharacter F) : χ ∈ factors F χ := by
  exact Finset.mem_image.mpr ⟨1, one_mem_artinCharacters F, mul_one χ⟩

-- OBLIGATION DE-EULER-FACTORIZATION | revised (2.1), p.2.
-- The Euler product away from finite sets of places: the same set T of places
-- of F on every factor, a set T' of places of the extension upstairs. The deleted
-- finite Euler polynomials are nonvanishing on Re s > 0, so this suffices for the
-- descent; no exact local factor at a ramified place is asserted.
theorem deletedEulerFactorization (χ : HeckeCharacter F) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F)))
      (T' : Finset (HeightOneSpectrum (𝓞 (Extension F)))),
      ∀ s : ℂ, 1 < s.re →
        heckeDeletedContinuation (Extension F) (normPullback F χ) T' s =
          ∏ ψ ∈ factors F χ, heckeDeletedContinuation F ψ T s := by
  sorry

-- OBLIGATION DE-CONTINUATION | revised Lemma 2.1, p.2.
-- Meromorphic identity transfer; no zero-free input.
theorem continuedFactorization (χ : HeckeCharacter F)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (T' : Finset (HeightOneSpectrum (𝓞 (Extension F))))
    (hEuler : ∀ s : ℂ, 1 < s.re →
      heckeDeletedContinuation (Extension F) (normPullback F χ) T' s =
        ∏ ψ ∈ factors F χ, heckeDeletedContinuation F ψ T s) :
    ∀ s ∈ rightHalfPlane (7 / 8),
      heckeDeletedContinuation (Extension F) (normPullback F χ) T' =ᶠ[𝓝[≠] s]
        (fun w => ∏ ψ ∈ factors F χ, heckeDeletedContinuation F ψ T w) := by
  intro s _
  -- Both sides are meromorphic on all of ℂ and agree on Re > 1, so their
  -- difference has infinite order at 2, hence at every point of ℂ.
  have hd : MeromorphicOn (heckeDeletedContinuation (Extension F) (normPullback F χ) T' -
      fun w => ∏ ψ ∈ factors F χ, heckeDeletedContinuation F ψ T w) Set.univ :=
    (meromorphicOn_heckeDeletedContinuation (Extension F) (normPullback F χ) T').sub
      (MeromorphicOn.fun_prod fun ψ _ => meromorphicOn_heckeDeletedContinuation F ψ T)
  have hnear : ∀ᶠ w in 𝓝 (2 : ℂ),
      (heckeDeletedContinuation (Extension F) (normPullback F χ) T' -
        fun w => ∏ ψ ∈ factors F χ, heckeDeletedContinuation F ψ T w) w = 0 := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (2 : ℂ) ∈ {w : ℂ | 1 < w.re})] with w hw
    simp [hEuler w hw]
  have htop := hd.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 2) (Set.mem_univ s)
    (meromorphicOrderAt_eq_top_iff.mpr (hnear.filter_mono nhdsWithin_le_nhds))
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp htop] with w hw
  simpa [sub_eq_zero] using hw

-- OBLIGATION DE-POLE-MATCHING | revised Lemma 2.1, p.2.
-- A zero cannot be hidden by cancellation against an unmatched norm pole.
-- Pure norm twists have the same parameter after actual norm pullback;
-- the full Artin family lies in one pullback fiber.
theorem poleMatching (χ : HeckeCharacter F) :
    ∀ s ∈ rightHalfPlane (7 / 8),
      (∀ ψ ∈ factors F χ, AnalyticAt ℂ (heckeContinuation F ψ) s) ∨
      ∃ p ∈ factors F χ,
        meromorphicOrderAt (heckeContinuation F p) s = (-1 : ℤ) ∧
        meromorphicOrderAt (heckeContinuation (Extension F) (normPullback F χ)) s = (-1 : ℤ) ∧
        ∀ ψ ∈ factors F χ, ψ ≠ p → AnalyticAt ℂ (heckeContinuation F ψ) s := by
  intro s _
  refine PoleMatching.pole_matching_of_common_normPullback F (Extension F)
    (factors F χ) (normPullback F χ) ?_ s
  intro ψ hψ
  apply Artin.artinFactors_common_normPullback F (Extension F) χ
  rw [Artin.artinFactors_eq_image]
  exact hψ

/-- Deletion keeps analyticity and, on Re s > 0, the orders; so the pole
matching of the full continuations holds for the deleted ones. -/
theorem deletedPoleMatching (χ : HeckeCharacter F)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (T' : Finset (HeightOneSpectrum (𝓞 (Extension F)))) :
    ∀ s ∈ rightHalfPlane (7 / 8),
      (∀ ψ ∈ factors F χ, AnalyticAt ℂ (heckeDeletedContinuation F ψ T) s) ∨
      ∃ p ∈ factors F χ,
        meromorphicOrderAt (heckeDeletedContinuation F p T) s = (-1 : ℤ) ∧
        meromorphicOrderAt
          (heckeDeletedContinuation (Extension F) (normPullback F χ) T') s = (-1 : ℤ) ∧
        ∀ ψ ∈ factors F χ, ψ ≠ p → AnalyticAt ℂ (heckeDeletedContinuation F ψ T) s := by
  intro s hs
  have hs0 : 0 < s.re := lt_trans (by norm_num) (show (7 / 8 : ℝ) < s.re from hs)
  have han (ψ : HeckeCharacter F) (h : AnalyticAt ℂ (heckeContinuation F ψ) s) :
      AnalyticAt ℂ (heckeDeletedContinuation F ψ T) s :=
    (heckeEulerDeletionPolynomial_analyticAt F ψ T s).mul h
  rcases poleMatching F χ s hs with h | ⟨p, hp, h1, h2, h3⟩
  · exact Or.inl fun ψ hψ => han ψ (h ψ hψ)
  · refine Or.inr ⟨p, hp, ?_, ?_, fun ψ hψ hne => han ψ (h3 ψ hψ hne)⟩
    · rw [meromorphicOrderAt_heckeDeletedContinuation F p T hs0]
      exact h1
    · rw [meromorphicOrderAt_heckeDeletedContinuation (Extension F) (normPullback F χ) T' hs0]
      exact h2

theorem descend (hTIP : ∀ ω : HeckeCharacter (Extension F), TIPInput (Extension F) ω) :
    HeckeSevenEighths F := by
  intro χ
  obtain ⟨T, T', hEuler⟩ := deletedEulerFactorization F χ
  have hup : MeromorphicZeroFreeOn
      (heckeDeletedContinuation (Extension F) (normPullback F χ) T') (rightHalfPlane (7 / 8)) :=
    (heckeDeletedContinuation_zeroFreeOn_iff (Extension F) (normPullback F χ) T'
      (by norm_num)).mpr (heckeSevenEighths_of_TIP hTIP (normPullback F χ))
  have hdown := meromorphicZeroFreeOn_of_factorization (factors F χ)
    (fun ψ => heckeDeletedContinuation F ψ T)
    (heckeDeletedContinuation (Extension F) (normPullback F χ) T') (rightHalfPlane (7 / 8))
    (fun ψ _ z _ => meromorphicOn_heckeDeletedContinuation F ψ T z (Set.mem_univ _))
    hup (continuedFactorization F χ T T' hEuler) (deletedPoleMatching F χ T T')
    (target_mem_factors F χ)
  exact (heckeDeletedContinuation_zeroFreeOn_iff F χ T (by norm_num)).mp hdown

end HeckeSkeleton.Descent
