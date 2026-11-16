module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.SdltAdjointPair
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedLcThreefold
public import MMP.AlgebraicGeometry.MMP.Abundance.SdltThreefoldRelativeGluing
public import MMP.AlgebraicGeometry.MMP.Abundance.Curve.SlcPrescribedSections
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy

/-!
# Complemented relative abundance for projective sdlt threefolds

Let `(T, Δ; L)` be a projective sdlt adjoint pair of pure dimension three over `ℂ`, with
normalization components `νᵢ : Tᵢ ⟶ T` and boundaries `Θᵢ = Cᵢ + Δᵢ`, so that
`ν^*L|_{Tᵢ} = K_{Tᵢ} + Θᵢ`, and let `f : T ⟶ Z` be a morphism to a projective complex variety.
Suppose `L` is `f`-nef and `L + A ∼_ℚ f^*H` for an effective rational Cartier divisor `A` on `T`,
containing no component of the conductor, and a rational Cartier divisor `H` on `Z`, and that
every `(Tᵢ, Θᵢ + Aᵢ)` is log canonical, `Aᵢ = νᵢ^*A`. Then `L` is `f`-semiample on the whole union
`T`: in some degree `m`, near every fibre of `f` the sheaf `𝒪_T(mL)` has sections generating it at
any given point. These are sections of the invertible sheaf on `T` itself, so they glue, with the
residue identification, across the conductor.

The proof makes each `K_{Tᵢ} + Θᵢ` semiample over `Z` by
`MMP.Fourfold.isRelativelySemiample_of_isLogCanonicalPair_add_of_qLinearlyEquivalent` and then
glues by
`MMP.Fourfold.IsSdltAdjointPair.exists_isAdjointGeneratorOn_of_isRelativelySemiample_comp`.

## Main results

All names below are in the namespace `MMP.Fourfold`.

* `IsSdltAdjointPair.exists_isAdjointGeneratorOn_of_add_qLinearlyEquivalent_of_isLogCanonicalPair`:
  `L` is `f`-semiample when it is `f`-nef and admits a log canonical complement as above.

## Implementation notes

* As in `MMP.Fourfold.IsSdltAdjointPair`, the adjoint `L = K_T + Δ` is not a divisor on `T`; a
  section of `𝒪_T(mL)` over an open `W` is a family `t = (tᵢ)ᵢ` of rational `m`-canonical forms
  on the `Tᵢ` which near every point `y ∈ W` is `ν^*a · g` for a function `a` and a local
  generator `g` of `𝒪_T(mL)` (`MMP.Fourfold.IsAdjointGeneratorOn`); it generates at `y` when `a`
  can be taken to be a unit. `f`-semiampleness of `L` is surjectivity of
  `f^* f_* 𝒪_T(mL) → 𝒪_T(mL)` for some `m > 0`, that is, for every `x ∈ T` a section over
  `f⁻¹(V)`, `V` a neighbourhood of `f(x)`, generating at `x`.
* Nefness and the complement are read on the normalization, where they are statements about
  `ℚ`-divisors: `L` is `f`-nef if and only if every `K_{Tᵢ} + Θᵢ` is `(νᵢ ≫ f)`-nef, `ν` being
  finite and surjective; the complement enters through effective `ℚ`-Cartier `Aᵢ` with
  `K_{Tᵢ} + Θᵢ + Aᵢ ∼_ℚ (νᵢ ≫ f)^*H`, which are not required to come from one divisor on `T`.
  That `A` contains no conductor component says that `Aᵢ` has coefficient zero at every prime
  divisor of `Tᵢ` lying over the double locus of `T`. The pull-back of `H` is that of the
  invertible sheaf `M = 𝒪_Z(mH)`, so `Z` need not be normal; one `M` and one `m` serve every
  component.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

namespace Proof_thm_fourfold_projective_complemented_sdlt_threefold_good

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold MMP.Mori MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A finite morphism is quasi-projective: the structure sheaf of its source is relatively ample,
the inverse image of an affine open being affine. -/
private theorem isQuasiProjective_of_isFinite {X S : Scheme.{0}} (f : X ⟶ S) [IsFinite f] :
    IsQuasiProjective f := by
  refine ⟨⟨inferInstance, inferInstance⟩, Stacks.Ample.unitModule X,
    Stacks.Ample.isInvertibleModule_unit X, ?_⟩
  refine (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f
    (Stacks.Ample.unitModule X)).mp ?_
  refine (Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff f).mpr ?_
  intro V hV
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  infer_instance

/-- A finite morphism into a scheme projective over `ℂ` is projective over `ℂ`. -/
private theorem isProjectiveMorphism_comp_of_isFinite {Y' Y : Scheme.{0}} (g : Y' ⟶ Y)
    [IsFinite g] (sY : Y ⟶ Spec (.of ℂ)) (hY : IsProjectiveMorphism sY) :
    IsProjectiveMorphism (g ≫ sY) := by
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sY
    (Stacks.Ample.unitModule (Spec (.of ℂ)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sY hY.isHQuasiProjective)
  have hg : IsProjectiveMorphism g :=
    isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
      ⟨isHQuasiProjective_of_isQuasiProjective g L hLa
        (isQuasiProjective_of_isFinite g), inferInstance⟩
  exact hg.comp hY

private theorem solution :
    ∀ {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 3 Δ Θ)
    [∀ i, QuasiCompact (N.n i ≫ sT)] [∀ i, CompactSpace (N.X i)]
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    {K : ∀ i, Divisor (N.X i)} (hK : ∀ i, (K i).IsCanonicalDivisor (N.n i ≫ sT) 3)
    (hnef : ∀ i, (Divisor.toQDivisor (K i) + Θ i).IsRelativelyNef (N.n i ≫ sT) (N.n i ≫ f))
    {A : ∀ i, QDivisor (N.X i)} (hA : ∀ i, 0 ≤ A i) (hAq : ∀ i, (A i).IsQCartier)
    (hAC : ∀ i (P : Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) → (A i).coeff P = 0)
    (hlc : ∀ i, MMP.Intersection.IsLogCanonicalPair (N.n i ≫ sT) (Θ i + A i))
    {G : ∀ i, QDivisor (N.X i)}
    (hDG : ∀ i, (Divisor.toQDivisor (K i) + Θ i + A i).QLinearlyEquivalent (G i))
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ L : Divisor (N.X i), Divisor.toQDivisor L = (m : ℤ) • G i ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback (N.n i ≫ f)).obj M)),
    ∃ m : ℕ, 0 < m ∧ ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V)
      (t : ∀ i, RationalPluriForms (N.n i ≫ sT) 3 m),
      ∀ y ∈ f ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ f ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 3 m) (a : Γ(T, U)),
          IsAdjointGeneratorOn N 3 m Θ U g ∧ (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U a) • g i := by
  intro T sT hT N Δ Θ h _ _ Z sZ hZ f hf K hK hnef A hA hAq hAC hlc G hDG M _ hGM
  obtain ⟨m₀, hm₀, hL₀⟩ := hGM
  refine h.exists_isAdjointGeneratorOn_of_isRelativelySemiample_comp hZ f hf fun i => ⟨K i, hK i, ?_⟩
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  haveI := N.isFinite_n i
  haveI : MMP.Mori.IsVariety ℂ (N.n i ≫ sT) := (N.isNormalVariety i).1
  have hproj : Mori.IsProjectiveVariety ℂ (N.n i ≫ sT) :=
    ⟨isProjectiveMorphism_comp_of_isFinite (N.n i) sT h.isProjectiveMorphism⟩
  obtain ⟨K', hK'⟩ := h.exists_isDltPair i
  have hlcΘ : MMP.Intersection.IsLogCanonicalPair (N.n i ≫ sT) (Θ i) :=
    ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair _ hK'.1.2.1 _).mpr hK').1
  exact isRelativelySemiample_of_isLogCanonicalPair_add_of_qLinearlyEquivalent (N.n i ≫ sT) sZ
    hproj (hK i).1 (hK i) hlcΘ hZ (N.n i ≫ f) (by rw [Category.assoc, hf]) (hnef i) (hA i)
    (hAq i) (hlc i) (hDG i) M ⟨m₀, hm₀, hL₀ i⟩

end Proof_thm_fourfold_projective_complemented_sdlt_threefold_good

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Complemented relative abundance for projective sdlt threefolds.** Let `(T, Δ; L)` be a
projective sdlt adjoint pair of dimension three over `ℂ` (`MMP.Fourfold.IsSdltAdjointPair`) with
normalization components `νᵢ : Tᵢ ⟶ T`, boundaries `Θᵢ` and canonical divisors `Kᵢ`, and let
`f : T ⟶ Z` be a morphism to a projective complex variety. Suppose `L` is `f`-nef, i.e. every
`Kᵢ + Θᵢ` is `(νᵢ ≫ f)`-nef, and that `L + A ∼_ℚ f^*H` with `A` effective rational Cartier and
containing no conductor component: there are effective `ℚ`-Cartier `Aᵢ` on the `Tᵢ`, with
coefficient zero at every prime divisor over the double locus of `T`, `ℚ`-divisors
`Gᵢ ∼_ℚ Kᵢ + Θᵢ + Aᵢ`, an invertible `𝒪_Z`-module `M` and `m > 0` with
`𝒪_{Tᵢ}(mGᵢ) ≅ (νᵢ ≫ f)^*M` for every `i`. Suppose also that every `(Tᵢ, Θᵢ + Aᵢ)` is log
canonical. Then `L` is `f`-semiample: there is `m > 0` such that for every `x ∈ T` there are an
open `V ∋ f(x)` of `Z` and a section `t` of `𝒪_T(mL)` over `f⁻¹(V)` generating `𝒪_T(mL)` at `x`;
near each point of `f⁻¹(V)`, `t` is `ν^*a · g` for a function `a` (a unit near `x`) and a local
generator `g` of `𝒪_T(mL)` (`MMP.Fourfold.IsAdjointGeneratorOn`). -/
@[mmp "thm_fourfold_projective_complemented_sdlt_threefold_good"]
public theorem
    IsSdltAdjointPair.exists_isAdjointGeneratorOn_of_add_qLinearlyEquivalent_of_isLogCanonicalPair
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 3 Δ Θ)
    [∀ i, QuasiCompact (N.n i ≫ sT)] [∀ i, CompactSpace (N.X i)]
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    {K : ∀ i, Divisor (N.X i)} (hK : ∀ i, (K i).IsCanonicalDivisor (N.n i ≫ sT) 3)
    (hnef : ∀ i, (Divisor.toQDivisor (K i) + Θ i).IsRelativelyNef (N.n i ≫ sT) (N.n i ≫ f))
    {A : ∀ i, QDivisor (N.X i)} (hA : ∀ i, 0 ≤ A i) (hAq : ∀ i, (A i).IsQCartier)
    (hAC : ∀ i (P : Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) → (A i).coeff P = 0)
    (hlc : ∀ i, MMP.Intersection.IsLogCanonicalPair (N.n i ≫ sT) (Θ i + A i))
    {G : ∀ i, QDivisor (N.X i)}
    (hDG : ∀ i, (Divisor.toQDivisor (K i) + Θ i + A i).QLinearlyEquivalent (G i))
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ L : Divisor (N.X i), Divisor.toQDivisor L = (m : ℤ) • G i ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback (N.n i ≫ f)).obj M)) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V)
      (t : ∀ i, RationalPluriForms (N.n i ≫ sT) 3 m),
      ∀ y ∈ f ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ f ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 3 m) (a : Γ(T, U)),
          IsAdjointGeneratorOn N 3 m Θ U g ∧ (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U a) • g i :=
              by revert T sT hT N Δ Θ h Z sZ hZ f hf K hK hnef A hA hAq hAC hlc G hDG M hGM; first | exact Proof_thm_fourfold_projective_complemented_sdlt_threefold_good.solution | exact Proof_thm_fourfold_projective_complemented_sdlt_threefold_good.solution _ | exact Proof_thm_fourfold_projective_complemented_sdlt_threefold_good.solution _ _ | exact Proof_thm_fourfold_projective_complemented_sdlt_threefold_good.solution _ _ _ | exact Proof_thm_fourfold_projective_complemented_sdlt_threefold_good.solution _ _ _ _

end MMP.Fourfold

