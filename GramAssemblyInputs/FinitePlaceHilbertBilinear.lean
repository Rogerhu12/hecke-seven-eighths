import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.Core
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing

/-! SOURCE ONLY, UNRUN. Public bilinear and quotient bridges for the actual
finite-place Hilbert symbol. Both inputs are arbitrary global field units;
the completion and roots-of-unity transport are the upstream definitions.
No reciprocity, integrality, or prime-avoidance assumptions are introduced. -/

noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity LocalClassFieldTheory.Kummer
open LocalFieldTheory

variable (K : Type) [Field K] [NumberField K]
variable (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
variable (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
variable (p : HeightOneSpectrum (𝓞 K))

theorem finitePlaceHilbertSymbol_mul_left (a b c : Kˣ) :
    finitePlaceHilbertSymbol K n hnK hmu p (a * b) c =
      finitePlaceHilbertSymbol K n hnK hmu p a c *
        finitePlaceHilbertSymbol K n hnK hmu p b c := by
  let C := (HeightOneSpectrum.adicAbv K p).Completion
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel p
  let : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField p
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [map_mul, finitePlaceHilbertSymbol_map_eq_localHilbertSymbol,
    finitePlaceHilbertSymbol_map_eq_localHilbertSymbol,
    finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  change localHilbertSymbol C n _ _
      (finitePlaceHilbert_completionUnit K p (a * b))
      (finitePlaceHilbert_completionUnit K p c) = _
  have hmap : finitePlaceHilbert_completionUnit K p (a * b) =
      finitePlaceHilbert_completionUnit K p a * finitePlaceHilbert_completionUnit K p b :=
    map_mul (Units.map (algebraMap K C).toMonoidHom) a b
  rw [hmap]
  exact (localHilbertSymbolHom C n
    (finitePlaceHilbert_natCast_ne_zero K n hnK p)
    (finitePlaceHilbert_primitiveRoots_nonempty K n hmu p)
    (finitePlaceHilbert_completionUnit K p c)).map_mul _ _

theorem finitePlaceHilbertSymbol_mul_right (a b c : Kˣ) :
    finitePlaceHilbertSymbol K n hnK hmu p a (b * c) =
      finitePlaceHilbertSymbol K n hnK hmu p a b *
        finitePlaceHilbertSymbol K n hnK hmu p a c := by
  let C := (HeightOneSpectrum.adicAbv K p).Completion
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel p
  let : IsNonarchimedeanLocalField C := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField p
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [map_mul, finitePlaceHilbertSymbol_map_eq_localHilbertSymbol,
    finitePlaceHilbertSymbol_map_eq_localHilbertSymbol,
    finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  change localHilbertSymbol C n _ _
      (finitePlaceHilbert_completionUnit K p a)
      (finitePlaceHilbert_completionUnit K p (b * c)) = _
  have hmap : finitePlaceHilbert_completionUnit K p (b * c) =
      finitePlaceHilbert_completionUnit K p b * finitePlaceHilbert_completionUnit K p c :=
    map_mul (Units.map (algebraMap K C).toMonoidHom) b c
  rw [hmap]
  exact LocalClassFieldTheory.Kummer.localHilbertSymbol_mul_right C n
    (finitePlaceHilbert_natCast_ne_zero K n hnK p)
    (finitePlaceHilbert_primitiveRoots_nonempty K n hmu p) _ _ _

/-- The actual finite-place symbol as a homomorphism in its first entry. -/
def finitePlaceHilbertFirstHom (b : Kˣ) : Kˣ →* nthRootsSubgroup K (n : ℕ) where
  toFun a := finitePlaceHilbertSymbol K n hnK hmu p a b
  map_mul' := fun a c => finitePlaceHilbertSymbol_mul_left K n hnK hmu p a c b
  map_one' := by
    have h := finitePlaceHilbertSymbol_mul_left K n hnK hmu p 1 1 b
    apply mul_left_cancel (a := finitePlaceHilbertSymbol K n hnK hmu p 1 b)
    simpa only [one_mul, mul_one] using h.symm

/-- The actual finite-place symbol as a homomorphism in its second entry. -/
def finitePlaceHilbertSecondHom (a : Kˣ) : Kˣ →* nthRootsSubgroup K (n : ℕ) where
  toFun b := finitePlaceHilbertSymbol K n hnK hmu p a b
  map_mul' := finitePlaceHilbertSymbol_mul_right K n hnK hmu p a
  map_one' := by
    have h := finitePlaceHilbertSymbol_mul_right K n hnK hmu p a 1 1
    apply mul_left_cancel (a := finitePlaceHilbertSymbol K n hnK hmu p a 1)
    simpa only [one_mul, mul_one] using h.symm

theorem finitePlaceHilbertSymbol_div_left (a b c : Kˣ) :
    finitePlaceHilbertSymbol K n hnK hmu p (a / b) c =
      finitePlaceHilbertSymbol K n hnK hmu p a c /
        finitePlaceHilbertSymbol K n hnK hmu p b c :=
  map_div (finitePlaceHilbertFirstHom K n hnK hmu p c) a b

theorem finitePlaceHilbertSymbol_div_right (a b c : Kˣ) :
    finitePlaceHilbertSymbol K n hnK hmu p a (b / c) =
      finitePlaceHilbertSymbol K n hnK hmu p a b /
        finitePlaceHilbertSymbol K n hnK hmu p a c :=
  map_div (finitePlaceHilbertSecondHom K n hnK hmu p a) b c

end HeckeGeneral.Arithmetic
