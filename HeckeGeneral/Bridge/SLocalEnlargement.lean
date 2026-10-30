import HeckeGeneral.Bridge.SLocalIdeleAssembly
import HeckeGeneral.Arithmetic.SIntegerLocalDiagonal

/-!
# Enlarging the additive test set while keeping the original unit quotient

Coordinates at newly inserted finite places are one. This continuous group
embedding preserves the actual assembled idele and the product norm, so
additive adelic Poisson may use a larger exceptional set without changing
the multiplicative integration domain. The diagonal discrepancy is retained
explicitly: at every new place its value is the original global unit.
No finite-index claim for the old subgroup inside a larger unit group is made.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S U : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] [Fintype U]

/-- Enlarge the local ambient group by inserting multiplicative identities. -/
def sLocalEnlargement (hSU : S ⊆ U) :
    sLocalMultiplicativeGroup K S →* sLocalMultiplicativeGroup K U where
  toFun p := (p.1, fun v => if hv : v.val ∈ S then p.2 ⟨v.val, hv⟩ else 1)
  map_one' := by
    apply Prod.ext
    · rfl
    funext v
    by_cases hv : v.val ∈ S <;> simp [hv]
  map_mul' p q := by
    apply Prod.ext
    · rfl
    funext v
    by_cases hv : v.val ∈ S <;> simp [hv]

@[simp] theorem sLocalEnlargement_arch (hSU : S ⊆ U)
    (p : sLocalMultiplicativeGroup K S) :
    (sLocalEnlargement K S U hSU p).1 = p.1 := rfl

@[simp] theorem sLocalEnlargement_finite_mem (hSU : S ⊆ U)
    (p : sLocalMultiplicativeGroup K S) (v : U) (hv : v.val ∈ S) :
    (sLocalEnlargement K S U hSU p).2 v = p.2 ⟨v.val, hv⟩ := by
  simp [sLocalEnlargement, hv]

@[simp] theorem sLocalEnlargement_finite_new (hSU : S ⊆ U)
    (p : sLocalMultiplicativeGroup K S) (v : U) (hv : v.val ∉ S) :
    (sLocalEnlargement K S U hSU p).2 v = 1 := by
  simp [sLocalEnlargement, hv]

theorem continuous_sLocalEnlargement (hSU : S ⊆ U) :
    Continuous (sLocalEnlargement K S U hSU) := by
  change Continuous (fun p : sLocalMultiplicativeGroup K S =>
    (p.1, fun v : U => if hv : v.val ∈ S then p.2 ⟨v.val, hv⟩
      else (1 : (v.val.adicCompletion K)ˣ)))
  apply continuous_fst.prodMk
  apply continuous_pi
  intro v
  by_cases hv : v.val ∈ S
  · simp only [dif_pos hv]
    fun_prop
  · simpa only [dif_neg hv] using
      (continuous_const : Continuous (fun _ : sLocalMultiplicativeGroup K S =>
        (1 : (v.val.adicCompletion K)ˣ)))

/-- Both ambient descriptions represent exactly the same actual idele. -/
theorem sLocalIdeleAssembly_enlargement (hSU : S ⊆ U)
    (p : sLocalMultiplicativeGroup K S) :
    sLocalIdeleAssembly K U (sLocalEnlargement K S U hSU p) =
      sLocalIdeleAssembly K S p := by
  apply Units.ext
  apply Prod.ext
  · apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    simp only [sLocalIdeleAssembly_arch, sLocalEnlargement_arch]
  · apply DFunLike.ext
    intro v
    by_cases hvS : v ∈ S
    · calc
        _ = ((sLocalEnlargement K S U hSU p).2 ⟨v, hSU hvS⟩).val :=
          sLocalIdeleAssembly_finite_mem K U _ ⟨v, hSU hvS⟩
        _ = (p.2 ⟨v, hvS⟩).val := by rw [sLocalEnlargement_finite_mem]
        _ = _ := (sLocalIdeleAssembly_finite_mem K S p ⟨v, hvS⟩).symm
    · by_cases hvU : v ∈ U
      · calc
          _ = ((sLocalEnlargement K S U hSU p).2 ⟨v, hvU⟩).val :=
            sLocalIdeleAssembly_finite_mem K U _ ⟨v, hvU⟩
          _ = 1 := by rw [sLocalEnlargement_finite_new K S U hSU p _ hvS]; rfl
          _ = _ := (sLocalIdeleAssembly_finite_not_mem K S p v hvS).symm
      · rw [sLocalIdeleAssembly_finite_not_mem K U _ v hvU,
          sLocalIdeleAssembly_finite_not_mem K S p v hvS]

theorem sLocalEnlargement_injective (hSU : S ⊆ U) :
    Function.Injective (sLocalEnlargement K S U hSU) := by
  intro p q hpq
  apply sLocalIdeleAssembly_injective K S
  simpa only [sLocalIdeleAssembly_enlargement] using
    congrArg (sLocalIdeleAssembly K U) hpq

@[simp] theorem sLocalProductNorm_enlargement (hSU : S ⊆ U)
    (p : sLocalMultiplicativeGroup K S) :
    sLocalProductNorm K U (sLocalEnlargement K S U hSU p) = sLocalProductNorm K S p := by
  rw [← idelicNorm_sLocalIdeleAssembly, sLocalIdeleAssembly_enlargement,
    idelicNorm_sLocalIdeleAssembly]

@[simp] theorem sLocalEnlargement_section (hSU : S ⊆ U) (r : {r : ℝ // 0 < r}) :
    sLocalEnlargement K S U hSU (sLocalNormSection K S r) =
      sLocalNormSection K U r := by
  apply Prod.ext
  · rfl
  funext v
  by_cases hv : v.val ∈ S <;> simp [sLocalEnlargement, sLocalNormSection, hv]

/-- The discrepancy between a global diagonal and extension by one. -/
def sLocalEnlargementDiagonalDefect (hSU : S ⊆ U) (u : S.unit K) :
    sLocalMultiplicativeGroup K U :=
  sLocalFieldUnitDiagonal K U (u : Kˣ) *
    (sLocalEnlargement K S U hSU (sLocalDiagonal K S u))⁻¹

theorem sLocalFieldUnitDiagonal_eq_defect_mul_enlargement (hSU : S ⊆ U)
    (u : S.unit K) :
    sLocalFieldUnitDiagonal K U (u : Kˣ) =
      sLocalEnlargementDiagonalDefect K S U hSU u *
        sLocalEnlargement K S U hSU (sLocalDiagonal K S u) := by
  unfold sLocalEnlargementDiagonalDefect
  group

@[simp] theorem sLocalEnlargementDiagonalDefect_arch (hSU : S ⊆ U) (u : S.unit K) :
    (sLocalEnlargementDiagonalDefect K S U hSU u).1 = 1 := by
  change Units.map (mixedEmbedding K).toMonoidHom (u : Kˣ) *
    (Units.map (mixedEmbedding K).toMonoidHom (u : Kˣ))⁻¹ = 1
  exact mul_inv_cancel _

@[simp] theorem sLocalEnlargementDiagonalDefect_finite_mem (hSU : S ⊆ U)
    (u : S.unit K) (v : U) (hv : v.val ∈ S) :
    (sLocalEnlargementDiagonalDefect K S U hSU u).2 v = 1 := by
  simp [sLocalEnlargementDiagonalDefect, sLocalEnlargement, sLocalFieldUnitDiagonal,
    sLocalDiagonal, hv]

/-- At a newly introduced place the discrepancy is the genuine local unit. -/
@[simp] theorem sLocalEnlargementDiagonalDefect_finite_new (hSU : S ⊆ U)
    (u : S.unit K) (v : U) (hv : v.val ∉ S) :
    (sLocalEnlargementDiagonalDefect K S U hSU u).2 v =
      Units.map (algebraMap K (v.val.adicCompletion K)).toMonoidHom (u : Kˣ) := by
  simp [sLocalEnlargementDiagonalDefect, sLocalEnlargement, sLocalFieldUnitDiagonal,
    sLocalDiagonal, hv]

end HeckeGeneral.Bridge
