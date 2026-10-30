import HeckeGeneral.Arithmetic.IdealFourierProjection
import HeckeGeneral.Arithmetic.ResidueFourier

/-!
# General-ideal residue masks and their dual support

The image of `I` in `R/J` is the actual ideal supporting its membership
mask. Its annihilator is tested by the concrete condition `k * I ⊆ J`.
This connects finite ideal orthogonality to the moving-mask quotient
without a principal-ideal assumption. A primitive additive character is
still required when the modulus is not one of our constructed squarefree
moduli.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.ResidueIdealProjection

open PeriodicFourier IdealMobiusMask ResidueFourier IdealFourierOrthogonality
  IsDedekindDomain
open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

def residueIdeal (J I : Ideal R) : Ideal (R ⧸ J) := I.map (Ideal.Quotient.mk J)

theorem mk_mem_residueIdeal (J I : Ideal R) (hJI : J ≤ I) (k : R) :
    Ideal.Quotient.mk J k ∈ residueIdeal J I ↔ k ∈ I := by
  exact Ideal.mem_quotient_iff_mem hJI

theorem quotientIndicator_eq_residue (J I : Ideal R) (hJI : J ≤ I) (x : R ⧸ J) :
    quotientIndicator J I hJI x = membershipIndicator (residueIdeal J I) x := by
  induction x using Quotient.inductionOn' with
  | h k =>
    change quotientIndicator J I hJI (Ideal.Quotient.mk J k) =
      membershipIndicator (residueIdeal J I) (Ideal.Quotient.mk J k)
    rw [quotientIndicator_mk]
    simp only [membershipIndicator, mk_mem_residueIdeal J I hJI]

theorem mk_mem_residue_annihilator (J I : Ideal R) (k : R) :
    Ideal.Quotient.mk J k ∈ annihilatorIdeal (residueIdeal J I) ↔
      ∀ a ∈ I, k * a ∈ J := by
  constructor
  · intro hk a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    exact hk (Ideal.Quotient.mk J a) (Ideal.mem_map_of_mem _ ha)
  · intro hk a ha
    obtain ⟨b, hb, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).mp ha
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hk b hb)

section Finite

variable (J : Ideal R) [Fintype (R ⧸ J)]

theorem fourier_quotientIndicator (I : Ideal R) (hJI : J ≤ I)
    (ψ : AddChar (R ⧸ J) ℂ) (hψ : ψ.IsPrimitive) (h : R ⧸ J) :
    fourier ψ (quotientIndicator J I hJI) h =
      if h ∈ annihilatorIdeal (residueIdeal J I) then (idealCard (residueIdeal J I) : ℂ) else 0 := by
  have hf : quotientIndicator J I hJI = membershipIndicator (residueIdeal J I) := by
    funext a
    exact quotientIndicator_eq_residue J I hJI a
  rw [hf]
  exact fourier_indicator ψ hψ _ h

theorem fourier_quotientIndicator_mk (I : Ideal R) (hJI : J ≤ I)
    (ψ : AddChar (R ⧸ J) ℂ) (hψ : ψ.IsPrimitive) (k : R) :
    fourier ψ (quotientIndicator J I hJI) (Ideal.Quotient.mk J k) =
      if ∀ a ∈ I, k * a ∈ J then (idealCard (residueIdeal J I) : ℂ) else 0 := by
  rw [fourier_quotientIndicator J I hJI ψ hψ, mk_mem_residue_annihilator]

theorem fourier_generalIdealMask (I : Ideal R) (hJI : J ≤ I)
    (ψ : AddChar (R ⧸ J) ℂ) (hψ : ψ.IsPrimitive) (f : (R ⧸ J) → ℂ) (h : R ⧸ J) :
    fourier ψ (fun a => f a * quotientIndicator J I hJI a) h =
      dualIdealAverage (residueIdeal J I) (fourier ψ f) h := by
  have hf : (fun a => f a * quotientIndicator J I hJI a) = idealMask (residueIdeal J I) f := by
    funext a
    rw [quotientIndicator_eq_residue]
    rfl
  rw [hf]
  exact fourier_idealMask ψ hψ _ f h

theorem energy_generalIdealMask_le (I : Ideal R) (hJI : J ≤ I) (f : (R ⧸ J) → ℂ) :
    energy (fun a => f a * quotientIndicator J I hJI a) ≤ energy f := by
  have hf : (fun a => f a * quotientIndicator J I hJI a) = idealMask (residueIdeal J I) f := by
    funext a
    rw [quotientIndicator_eq_residue]
    rfl
  rw [hf]
  exact energy_idealMask_le _ f

section MovingMask

variable [IsDedekindDomain R]

theorem fourier_movingMask_dualAverages (S : Finset (HeightOneSpectrum R))
    (hJS : J ≤ primeProduct S) (ψ : AddChar (R ⧸ J) ℂ) (hψ : ψ.IsPrimitive)
    (f : (R ⧸ J) → ℂ) (h : R ⧸ J) :
    fourier ψ (fun a => f a * quotientMask J S hJS a) h =
      ∑ T : S.powerset, (UniqueFactorizationMonoid.moebius (primeProduct T.val) : ℂ) *
        dualIdealAverage (residueIdeal J (primeProduct T.val)) (fourier ψ f) h := by
  rw [fourier_quotientMask]
  apply Finset.sum_congr rfl
  intro T _
  congr 1
  exact fourier_generalIdealMask J _ _ ψ hψ f h

end MovingMask
end Finite

end HeckeGeneral.Arithmetic.ResidueIdealProjection
