module

public import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
public import MMP.AlgebraicGeometry.Positivity.FreePencilCrepant
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
public import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
public import MMP.AlgebraicGeometry.Bertini.FreeLinearSystem
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso

/-!
# Nodal boundaries on smooth surface germs, and reduced Cartier divisors through a closed set

This file holds two results used in the classification of log terminal surface pairs (FA
Ch. 3) and in the construction of log resolutions (FA 18.12).

**A node is not log terminal.** Let `(X, P; B)` be a surface germ with reduced boundary `B`
whose minimal resolution has no exceptional curves (`n = 0`), and suppose `(X, P; B)` is of
type (9) of FA Fig. 3 (`MMP.Flips.IsFig3Type9`): `mult_P B = 2` and the birational transform of
`B` on the blow-up of `P` meets the exceptional curve in two distinct points. If `B` has exactly
one component (an irreducible curve with a node at `P`), then `(X, B)` is not log terminal on
any open neighbourhood of `P`: the exceptional curve `F` of the blow-up of `P` has log
discrepancy `a_ℓ(F, B) = 2 - mult_P B = 0`. Since `B` is singular at `P`, every log resolution
factors through the blow-up of `P`, and the strict transform of `F` is an exceptional divisor
of log discrepancy zero on it.

**A reduced Cartier divisor through a prescribed closed subset.** Let `Z` be a normal
quasi-projective variety over an algebraically closed field `k` of characteristic zero, let
`T₀ ⊊ Z` be a proper closed subset and let `S` be a finite set of points of `Z ∖ T₀`. Then there
is a reduced effective Cartier divisor `H'` on `Z` whose support contains `T₀` and misses every
point of `S`, which is smooth at every point of `Supp H' ∖ (T₀ ∪ Sing Z)`, and which has
multiplicity one along every prime divisor contained in `T₀`: it is the divisor of a general
member of `|𝓘_{T₀} ⊗ L^D|`, for `L` ample and `D ≫ 0`.

## Main results

* `MMP.Flips.IsFig3Type9.not_isLogTerminal_near`: a type (9) germ with `n = 0` and irreducible
  reduced boundary is not log terminal near `P`.
* `MMP.Mori.exists_isCartier_reduced_supp_superset`: the existence of `H'`.

## Implementation notes

As in Kollár–Mori, a Cartier divisor on the normal variety `Z` is a Weil divisor
`H' : MMP.Mori.Divisor Z` that is locally principal (`MMP.Mori.Divisor.IsCartier`); it is
reduced and effective when each coefficient is `0` or `1`. On a normal scheme such a divisor
has as its closed subscheme the reduced structure on its support, so smoothness of `H'` at a
point `z` is smoothness over `k` of the reduced subscheme `H'.suppIdeal` at the point over `z`.
The singular locus `Sing Z` is the complement of the smooth locus of the structure morphism.

The sections of `L ^ D` are produced from ampleness directly rather than from the global
generation of `𝓘_{T₀} ⊗ L ^ D`. Off `T₀` the nonvanishing loci `X_s ⊆ Z ∖ T₀` of sections of
positive powers of `L` form a basis of the topology ([Stacks, Tag 01Q3]); finitely many cover
`Z ∖ T₀`. Along a prime divisor `E ⊆ T₀`, near its generic point `T₀` is `E`, so a uniformizer
of the discrete valuation ring `𝒪_{Z,E}` is a function `h` vanishing along `T₀` near `η_E`; on
an `X_s` around `η_E` it is a ratio `t / σ` of two sections ([Stacks, Tag 01PW]), and `t s`
vanishes along `T₀` and has order one along `E`. Powers bring all these sections into one
degree `D`. On `Z ∖ T₀` the zero scheme of the general member is reduced and smooth by Bertini's
theorem, hence equal to the reduced structure on its support; along `T₀` its order is one along
every prime divisor by the choice of the sections.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Ex. 2.14,
  Fig. 3 (9), and 18.12.1
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

/-! ### A node on a smooth surface germ -/

namespace MMP.Flips

open MMP.Mori MMP.Threefold.Resolution

/-- The identity of a smooth surface germ is a resolution of the germ. -/
private theorem isGermResolution_id {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} {P : S} (hP : IsClosed ({P} : Set S))
    (hG : IsSurfaceGerm sS P) (hsm : IsSmoothScheme sS) :
    IsGermResolution sS P (𝟙 S) := by
  refine ⟨hG, ⟨inferInstance, isBirationalMorphism_of_isIso _, by rwa [Category.id_comp]⟩,
    hG.2.1, ⟨⟨{P}ᶜ, hP.isOpen_compl⟩, rfl, ?_⟩⟩
  rw [morphismRestrict_id]; exact IsIso.id _

/-- The identity of a scheme has no exceptional curves over a point. -/
private theorem not_isGermExceptionalCurve_id {S : Scheme.{u}} {P : S}
    (E : MMP.Mori.PrimeDivisor S) (h : IsGermExceptionalCurve (𝟙 S) P E) : False := by
  obtain ⟨⟨⟨hirr, hsub⟩, -⟩, hint, hdim⟩ := h
  have hsub' : ∀ x ∈ E.support, x = P := fun x hx => hsub hx
  have : Subsingleton E.idealSheaf.subscheme := by
    refine ⟨fun a b => ?_⟩
    apply E.idealSheaf.subschemeι.isEmbedding.injective
    have ha : E.idealSheaf.subschemeι a ∈ E.support := by
      rw [PrimeDivisor.support, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨a, rfl⟩
    have hb : E.idealSheaf.subschemeι b ∈ E.support := by
      rw [PrimeDivisor.support, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨b, rfl⟩
    rw [hsub' _ ha, hsub' _ hb]
  haveI := hint
  have : Nonempty E.idealSheaf.subscheme := inferInstance
  rw [topologicalKrullDim_eq_zero_of_discreteTopology_nonempty] at hdim
  simp at hdim

private theorem isExceptionalCurveEnumeration_id {S : Scheme.{u}} {P : S} :
    IsExceptionalCurveEnumeration (𝟙 S) P (Fin.elim0 : Fin 0 → MMP.Mori.PrimeDivisor S) :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun C hC => (not_isGermExceptionalCurve_id C hC).elim⟩

/-- A smooth surface germ with boundary of multiplicity two has an exceptional prime of the
point blow-up of log discrepancy zero. -/
private theorem exists_logDiscrepancy_zero_blowUp {k : Type u} [Field k] [IsAlgClosed k]
    {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] [CompactSpace S] [LocallyOfFiniteType sS] {P : S} {B : QDivisor S}
    (hB : IsSurfaceGermWithBoundary sS P B) (hsm : IsSmoothScheme sS)
    (hmult : DivisorWithCoeffs.multiplicityAt B P = 2)
    {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    (hKB : HoldsOnGerm {P} fun U : S.Opens =>
      IsCartierCombination
        (DivisorWithCoeffs.restrictOpen U (Divisor.toRDivisor K + QDivisor.toRDivisor B)))
    (hP : IsClosed ({P} : Set S))
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{P}, hP⟩ : Closeds S)))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{P}, hP⟩)) :
    ∃ (hY : IsNormalVariety k (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{P}, hP⟩ : Closeds S)) ≫ sS))
      (hg : IsBirationalMorphism (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{P}, hP⟩ : Closeds S))))
      (hp : IsProper (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{P}, hP⟩ : Closeds S))))
      (hd : topologicalKrullDim (blowUp (Scheme.IdealSheafData.vanishingIdeal
        (⟨{P}, hP⟩ : Closeds S))) = 2),
      IsLogDiscrepancy sS 2 K (QDivisor.toRDivisor B)
        (ProperDivisorOver.mk ⟨_, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{P}, hP⟩ : Closeds S)), hY, hg, F⟩ hp).valuation 0 := by
  have hX : IsNormalVariety k sS := hB.1.1
  have : QuasiCompact (𝟙 S ≫ sS) := by rw [Category.id_comp]; exact hX.1.toQuasiCompact
  have hres : IsGermResolution sS P (𝟙 S) := isGermResolution_id hP hB.1 hsm
  have hE := isExceptionalCurveEnumeration_id (S := S) (P := P)
  obtain ⟨a, ha, -⟩ := existsUnique_isGermLogDiscrepancyVector hB hres hE
  obtain ⟨hres', E', -, -, hiff⟩ := isGermLogDiscrepancyVector_snoc_blowUp_iff ha hP
    (show (𝟙 S) P = P from rfl) hF
  have hΘ : DivisorWithCoeffs.multiplicityAt
      (logPullbackBoundary (𝟙 S) B (Fin.elim0 : Fin 0 → MMP.Mori.PrimeDivisor S) a) P = 2 := by
    rw [logPullbackBoundary, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    have h1 : inverseTransformDivisor (𝟙 S) B = B := by
      have : inverseTransformDivisor (R := ℚ) (𝟙 S) = AddMonoidHom.id _ := by
        refine Finsupp.addHom_ext fun P r ↦ ?_
        rw [AddMonoidHom.id_apply]
        exact inverseTransformDivisor_single_of_eq_some
          (inverseTransformPrimeDivisor_eq_some_of_map_genericPoint (g := 𝟙 S) (D := P) (E := P)
            rfl (MMP.Mori.le_biregularLocus (V := ⊤) (by
              rw [MMP.Mori.isBiregular_top_iff]; exact IsIso.id _) trivial)) r
      exact DFunLike.congr_fun this B
    rw [h1]
    exact hmult
  have hvec := (hiff (Fin.snoc a (2 - DivisorWithCoeffs.multiplicityAt
    (logPullbackBoundary (𝟙 S) B (Fin.elim0 : Fin 0 → MMP.Mori.PrimeDivisor S) a) P))).mpr rfl
  rw [hΘ] at hvec
  have key : ∀ g' : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{P}, hP⟩ : Closeds S)) ⟶ S,
      g' = blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{P}, hP⟩ : Closeds S)) ≫ 𝟙 S →
      ∃ (hY : IsNormalVariety k (g' ≫ sS)) (hg : IsBirationalMorphism g')
        (hp : IsProper g') (hd : topologicalKrullDim (blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨{P}, hP⟩ : Closeds S))) = 2),
        IsLogDiscrepancy sS 2 K (QDivisor.toRDivisor B)
          (ProperDivisorOver.mk ⟨_, g', hY, hg, F⟩ hp).valuation 0 := by
    intro g' hg'
    subst hg'
    haveI := hres'.quasiCompact_comp
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      hres'.isSmoothResolution.isSmoothScheme).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      hres'.isSmoothResolution.isSmoothScheme).2
    have hY : IsNormalVariety k ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{P}, hP⟩ : Closeds S)) ≫ 𝟙 S) ≫ sS) := ⟨hres'.isVariety, inferInstance⟩
    have hg := hres'.isSmoothResolution.isBirationalMorphism
    have hp := hres'.isSmoothResolution.isProper
    refine ⟨hY, hg, hp, hres'.topologicalKrullDim_eq, ?_⟩
    have := hvec.isLogDiscrepancy hK hKB (Fin.last 0) hY hg hp
    rw [Fin.snoc_last, Fin.snoc_last] at this
    simpa using this
  exact key _ (Category.comp_id _).symm

/-- On a surface integral and locally of finite type over `k`, the generic point of a prime
divisor is not a closed point. -/
private theorem not_isClosed_singleton_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 2) (Γ : MMP.Mori.PrimeDivisor Y) :
    ¬ IsClosed ({Γ.genericPoint} : Set Y) := fun hcl => by
  have h := topologicalKrullDim_closure_singleton_add_coheight sY Γ.genericPoint
  rw [Γ.coheight_genericPoint, hdim] at h
  have h1 : topologicalKrullDim (closure {Γ.genericPoint} : Set Y) = 1 := by
    generalize topologicalKrullDim (closure {Γ.genericPoint} : Set Y) = d at h ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h
    | coe d =>
      induction d using ENat.recTopCoe with
      | top => exact absurd h (by decide)
      | coe d =>
        have h' : ((d + 1 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) :=
          WithBot.coe_injective (by push_cast; exact h)
        have : d = 1 := by have := Nat.cast_injective h'; omega
        subst this; rfl
  rw [hcl.closure_eq] at h1
  have := topologicalKrullDim_zero_of_discreteTopology ({Γ.genericPoint} : Set Y)
  rw [h1] at this
  exact absurd this (by decide)

/-- A proper birational morphism from a surface to an integral normal surface is an isomorphism
over the generic point of every prime divisor of the target, which therefore has a birational
transform. -/
private theorem exists_primeDivisor_map_genericPoint {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace Y] [NoetherianSpace Y]
    (hX : topologicalKrullDim X = 2)
    (f : Y ⟶ X) [IsProper f] (hb : IsBirational f) (hdim : topologicalKrullDim Y ≤ 2)
    (F : MMP.Mori.PrimeDivisor X) :
    ∃ F' : MMP.Mori.PrimeDivisor Y, f F'.genericPoint = F.genericPoint ∧
      F.genericPoint ∈ biregularLocus f := by
  have hV := MMP.Mori.mem_biregularLocus_of_not_isClosed f hb hdim
    (not_isClosed_singleton_genericPoint sX hX F)
  obtain ⟨F', -, hη⟩ := exists_inverseTransformPrimeDivisor_eq_some (g := f) F hV
  exact ⟨F', hη, hV⟩

/-- The divisorial valuation of a prime divisor at which a dominant morphism is a local
isomorphism is its image under the morphism. -/
private theorem valuationOver_comp_eq_of_biregular {X Y Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    (g : Z ⟶ Y) (π : Y ⟶ X) [IsDominant g] [IsDominant π] [IsDominant (g ≫ π)]
    (F'' : MMP.Mori.PrimeDivisor Z) (F : MMP.Mori.PrimeDivisor Y)
    (hη : g F''.genericPoint = F.genericPoint) (hV : F.genericPoint ∈ biregularLocus g) :
    F''.valuationOver (g ≫ π) = F.valuationOver π := by
  haveI : IsIso (g.stalkMap F''.genericPoint) :=
    MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus g (hη ▸ hV)
  refine Valuation.ext fun t => ?_
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
    ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g π t]
  generalize functionFieldMap π t = b
  by_cases hb : b = 0
  · subst hb; simp
  · have hb' : functionFieldMap g b ≠ 0 := by
      intro h0
      exact hb ((functionFieldMap g).injective (by rw [h0, map_zero]))
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hb',
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hb,
      MMP.Positivity.ord_functionFieldMap_of_isIso g F'' F hη b]

open MMP.Resolution.Bridges in
/-- If `g ≫ π` and `π` are proper birational morphisms of integral schemes with normal target,
then `g` is birational. -/
private theorem isBirational_of_comp_of_isBirational {X Y Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] [IsNormal X] [IsLocallyNoetherian X]
    (g : Z ⟶ Y) (π : Y ⟶ X) [IsProper g] [IsProper π]
    (hgπ : IsBirational (g ≫ π)) (hπ : IsBirational π) : IsBirational g := by
  obtain ⟨hU, hiso⟩ := (isOpen_finiteFibreLocus_and_isIso π hπ).1 inferInstance
  set W : X.Opens := ⟨_, hU⟩ with hW
  have hηY : π (genericPoint Y) = genericPoint X := map_genericPoint_eq π hπ
  have hηZ : π (g (genericPoint Z)) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply]
    exact map_genericPoint_eq (g ≫ π) hgπ
  have hWη : genericPoint X ∈ W := hηY ▸ map_genericPoint_mem_finiteFibreLocus π hπ
  have hgη : g (genericPoint Z) = genericPoint Y := by
    have hinj : Function.Injective (π ∣_ W) := (Scheme.homeoOfIso (asIso (π ∣_ W))).injective
    have hz : g (genericPoint Z) ∈ π ⁻¹ᵁ W := show π (g (genericPoint Z)) ∈ W from hηZ ▸ hWη
    have hy : genericPoint Y ∈ π ⁻¹ᵁ W := show π (genericPoint Y) ∈ W from hηY ▸ hWη
    exact congrArg Subtype.val (hinj (Subtype.ext
      ((morphismRestrict_base_coe π W ⟨g (genericPoint Z), hz⟩).trans
        ((hηZ.trans hηY.symm).trans (morphismRestrict_base_coe π W ⟨genericPoint Y, hy⟩).symm))))
  refine ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hgη]
    exact Set.bijOn_singleton.mpr rfl
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    have h1 : IsIso (π.stalkMap (g (genericPoint Z))) := by
      rw [hgη]
      exact MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus π
        (le_biregularLocus hiso (by rwa [hηY]))
    have h2 : IsIso ((g ≫ π).stalkMap (genericPoint Z)) :=
      hgπ.isIso_stalkMap _ (by rw [genericPoints_eq_singleton]; rfl)
    rw [Scheme.Hom.stalkMap_comp] at h2
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (π.stalkMap (g (genericPoint Z)))
      (g.stalkMap (genericPoint Z)) h1 h2

/-- **Strict transform of a prime divisor of the point blow-up.** Let `h : Z ⟶ S` be a proper
birational morphism of smooth surfaces over `k` which is an isomorphism over no neighbourhood of
the closed point `P`. Then `h` factors through the blow-up of `P` (Stacks 0C5R), and every prime
divisor `F` of the blow-up has a strict transform `F''` on `Z`, defining the same valuation of
the function field of `S`. -/
private theorem exists_primeDivisor_valuation_eq_of_not_isIso {k : Type u} [Field k]
    {S Z : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsIntegral S]
    (hS : AlgebraicGeometry.IsVariety k sS) (hSs : IsSmoothScheme sS)
    (hSd : topologicalKrullDim S = 2) (hZ : AlgebraicGeometry.IsVariety k sZ)
    (hZs : IsSmoothScheme sZ) (hZd : topologicalKrullDim Z = 2)
    (h : Z ⟶ S) (hh : h ≫ sS = sZ) [IsProper h] (hb : IsBirationalMorphism h)
    {P : S} (hP : IsClosed ({P} : Set S))
    (hPh : ∀ W : S.Opens, P ∈ W → ¬ IsIso (h ∣_ W))
    (hBl : IsNormalVariety k (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{P}, hP⟩ : Closeds S)) ≫ sS))
    (hπ : IsBirationalMorphism (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{P}, hP⟩ : Closeds S))))
    (hpπ : IsProper (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{P}, hP⟩ : Closeds S))))
    (hZn : IsNormalVariety k (h ≫ sS))
    (hBld : topologicalKrullDim (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{P}, hP⟩ : Closeds S))) = 2)
    (F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{P}, hP⟩ : Closeds S)))) :
    ∃ F'' : MMP.Mori.PrimeDivisor Z,
      (DivisorOver.mk (k := k) (sX := sS) Z h hZn hb F'').valuation =
        (DivisorOver.mk (k := k) (sX := sS) _ (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{P}, hP⟩ : Closeds S))) hBl hπ F).valuation ∧
      h F''.genericPoint = blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{P}, hP⟩ : Closeds S)) F.genericPoint := by
  have hZi : IsIntegral Z := hZ.toIsIntegral
  have hSf : LocallyOfFiniteType sS := hS.toLocallyOfFiniteType
  haveI : IsDominant h := hb.isDominant
  have hb' : IsBirational h := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb
  obtain ⟨h'', hh''⟩ := MMP.Resolution.Bridges.exists_comp_eq_pointBlowUpToBase_of_isSmoothSurface
    k hS hSs hSd hZ hZs hZd h hh hb' hP hPh
  subst hh
  subst hh''
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{P}, hP⟩ : Closeds S))
  haveI : IsProper π := hpπ
  haveI : IsProper h'' := IsProper.of_comp h'' π
  haveI hBli : IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal
    (⟨{P}, hP⟩ : Closeds S))) := hBl.1.toIsIntegral
  haveI : IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal
    (⟨{P}, hP⟩ : Closeds S))) := hBl.2
  haveI : LocallyOfFiniteType (π ≫ sS) := hBl.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal
    (⟨{P}, hP⟩ : Closeds S))) := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sS)
  haveI : IsNormal S := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hSs).2
  haveI : IsLocallyNoetherian S := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hSs).1
  have hπb : IsBirational π := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hπ
  have hbh : IsBirational h'' := isBirational_of_comp_of_isBirational h'' π hb' hπb
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace ((h'' ≫ π) ≫ sS)
  haveI : IsLocallyNoetherian Z := hZn.1.toLocallyOfFiniteType.isLocallyNoetherian ((h'' ≫ π) ≫ sS)
  haveI : NoetherianSpace Z := (haveI : IsNoetherian Z := {}; inferInstance)
  obtain ⟨F'', hη, hV⟩ := exists_primeDivisor_map_genericPoint (sX := π ≫ sS) hBld h'' hbh
    hZd.le F
  haveI : IsDominant π := hπ.isDominant
  haveI : IsDominant (h'' ≫ π) := hb.isDominant
  haveI : IsDominant h'' := by
    refine ⟨?_⟩
    rw [denseRange_iff_closure_range]
    refine Set.eq_univ_of_univ_subset ?_
    have h1 : h'' (genericPoint Z) = genericPoint _ := MMP.Mori.map_genericPoint_eq h'' hbh
    rw [← (genericPoint_spec (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{P}, hP⟩ : Closeds S)))).def, ← h1]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)
  haveI : IsNormal Z := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hZs).2
  exact ⟨F'', valuationOver_comp_eq_of_biregular h'' π F'' F hη hV,
    by rw [Scheme.Hom.comp_apply, hη]⟩

/-- A partial isomorphism representing the rational map of `f` agrees with `f` on its source. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A partial map representing the inverse of the rational map of `f` is a right inverse of `f`
on its domain. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- For a proper birational morphism `f : Y ⟶ X` of normal varieties, the transform of a prime
divisor `P` of `X` under `f⁻¹` is the prime divisor `E` of `Y` with `f(η_E) = η_P`. -/
private theorem transformPrimeDivisor_inverse_eq_some {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor X) (E : MMP.Mori.PrimeDivisor Y)
    (h : f E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsDominant f := hf.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = (f ≫ sX) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  set g := MMP.Mori.RationalMap.IsBirational.inverse hf
  have hdef : MMP.Mori.RationalMap.DefinedAt g P.genericPoint := by
    by_contra hnd
    have hcodim := MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hX f hY.1 hf
    have h2 := le_closedsCodimension_iff.mp hcodim
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom g).compl.isClosed)
    have h3 : codimension (IrreducibleCloseds.closureSingleton P.genericPoint) = 1 := by
      rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
        (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
        Order.coheight_orderIso, P.coheight_genericPoint]
    rw [h3] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

open IsLocalRing in
private theorem map_le_pow_maximalIdeal_iff {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R →+* S) (he : Function.Bijective e) (I : Ideal R) (k : ℕ) :
    I.map e ≤ maximalIdeal S ^ k ↔ I ≤ maximalIdeal R ^ k := by
  have hm : (maximalIdeal R).map e = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv (RingEquiv.ofBijective e he))
  rw [← hm, ← Ideal.map_pow]
  refine ⟨fun h => ?_, Ideal.map_mono⟩
  have := Ideal.comap_mono (f := e) h
  rwa [Ideal.comap_map_of_bijective e he, Ideal.comap_map_of_bijective e he] at this

/-- The multiplicity of a prime divisor of an open subscheme at a point is that of its closure. -/
private theorem multiplicityAt_primeDivisorMap {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (E' : MMP.Mori.PrimeDivisor V) (v : V) :
    E'.multiplicityAt v =
      MMP.Mori.PrimeDivisor.multiplicityAt (OpenWeilRestriction.primeDivisorMap j E') (j v) := by
  unfold PrimeDivisor.multiplicityAt
  simp only [Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  rw [← MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap j E',
    MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map]
  have hiso : IsIso (j.stalkMap v) := (IsOpenImmersion.iff_isIso_stalkMap.mp ‹_›).2 v
  have hbij := ConcreteCategory.bijective_of_isIso (j.stalkMap v)
  refine iSup_congr fun k => iSup_congr_Prop ?_ fun _ => rfl
  exact map_le_pow_maximalIdeal_iff (j.stalkMap v).hom hbij _ k

/-- A morphism `f : Y ⟶ X` which is an isomorphism over an open `W` preserves incidence and
multiplicity of prime divisors corresponding under it (`f(η_{C'}) = η_C`), at points over `W`. -/
private theorem mem_support_iff_and_multiplicityAt_eq_of_isIso_restrict {X Y : Scheme.{u}}
    (f : Y ⟶ X) (W : X.Opens) [IsIso (f ∣_ W)] (C : MMP.Mori.PrimeDivisor X)
    (C' : MMP.Mori.PrimeDivisor Y) (hη : f C'.genericPoint = C.genericPoint)
    (hCW : C.genericPoint ∈ W) (y : Y) (hy : f y ∈ W) :
    (y ∈ C'.support ↔ f y ∈ C.support) ∧ C'.multiplicityAt y = C.multiplicityAt (f y) := by
  obtain ⟨CW, hCW'⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    W.ι C ⟨C.genericPoint, hCW⟩ (MMP.Flips.primeDivisor_genericPoint_mem_support C)
  have hC'V : f C'.genericPoint ∈ W := hη ▸ hCW
  obtain ⟨CV, hCV⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    (f ⁻¹ᵁ W).ι C' ⟨C'.genericPoint, hC'V⟩
    (MMP.Flips.primeDivisor_genericPoint_mem_support C')
  have hinj : Function.Injective W.ι := W.ι.isOpenEmbedding.injective
  have hres : ∀ v : (f ⁻¹ᵁ W).toScheme, W.ι ((f ∣_ W) v) = f ((f ⁻¹ᵁ W).ι v) := fun v =>
    morphismRestrict_base_coe f W v
  have hmap : OpenWeilRestriction.primeDivisorMap (f ∣_ W) CV = CW := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
    apply hinj
    rw [hres CV.genericPoint, ← OpenWeilRestriction.genericPoint_primeDivisorMap, hCV, hη,
      ← OpenWeilRestriction.genericPoint_primeDivisorMap, hCW']
  set v : (f ⁻¹ᵁ W).toScheme := ⟨y, hy⟩
  have hv : (f ⁻¹ᵁ W).ι v = y := rfl
  have hev : W.ι ((f ∣_ W) v) = f y := hres v
  constructor
  · rw [← hCV, ← hv, MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff,
      ← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff (f ∣_ W), hmap,
      ← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff W.ι, hCW', hev, hv]
  · rw [← hCV, ← hv, ← multiplicityAt_primeDivisorMap, multiplicityAt_primeDivisorMap (f ∣_ W),
      hmap, multiplicityAt_primeDivisorMap W.ι, hCW', hev, hv]

/-- A birational morphism of varieties preserves the dimension. -/
private theorem topologicalKrullDim_eq_of_isBirationalMorphism {k : Type u} [Field k]
    {T Y' : Scheme.{u}} {sT : T ⟶ Spec (.of k)} [IsIntegral T] [LocallyOfFiniteType sT]
    {h : Y' ⟶ T} [IsIntegral Y'] [LocallyOfFiniteType (h ≫ sT)] (hf : IsBirationalMorphism h) :
    topologicalKrullDim Y' = topologicalKrullDim T := by
  haveI : IsDominant h := hf.isDominant
  rw [← toENat_trdeg_functionField (sX := h ≫ sT),
    ← trdeg_functionField_eq_of_bijective sT h hf.functionFieldMap_bijective,
    toENat_trdeg_functionField (sX := sT)]

/-- A divisor supported on the single prime `C` with coefficient one there is `C`. -/
private theorem eq_single_of_support_eq_singleton {T : Scheme.{u}} {B : QDivisor T}
    {C : MMP.Mori.PrimeDivisor T} (hC : B.support = {C}) (hB1 : B C = 1) :
    B = Finsupp.single C 1 :=
  hB1 ▸ (Finsupp.support_eq_singleton.mp hC).2

/-- A log resolution of a smooth surface with a boundary curve of multiplicity two at `P` is an
isomorphism over no neighbourhood of `P`: otherwise the (smooth) components of the snc divisor
`G` through the preimage of `P` would exhibit the curve as smooth at `P`. -/
private theorem not_isIso_restrict_of_multiplicity_two {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] [LocallyOfFiniteType sT] {P : T}
    (hdim : topologicalKrullDim T = 2) {B : QDivisor T}
    {C : MMP.Mori.PrimeDivisor T} (hC : B.support = {C}) (hB1 : B C = 1) (hPC : P ∈ C.support)
    (hmult : C.multiplicityAt P = 2)
    {Y' : Scheme.{u}} {h : Y' ⟶ T} (hLR : MMP.Flips.IsLogResolution sT (QDivisor.toRDivisor B) h)
    (W : T.Opens) (hPW : P ∈ W) : ¬ IsIso (h ∣_ W) := by
  classical
  intro hiso
  obtain ⟨hlv, hYv, hYs, hp, hf, G, -, hGiff, hGsnc⟩ := hLR
  have hTv : IsNormalVariety k sT := hlv.isNormalVariety
  haveI := hYv.toIsIntegral
  haveI := hYv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sT)
  haveI : IsNormal Y' := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  haveI : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace h
  haveI : NoetherianSpace Y' := (haveI : IsNoetherian Y' := {}; inferInstance)
  have hY : IsNormalVariety k (h ≫ sT) := ⟨hYv, inferInstance⟩
  have hYd : topologicalKrullDim Y' = 2 :=
    (topologicalKrullDim_eq_of_isBirationalMorphism (sT := sT) hf).trans hdim
  have hb : IsBirational h := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf
  obtain ⟨C', hη, -⟩ := exists_primeDivisor_map_genericPoint (sX := sT) hdim h hb hYd.le C
  have hBR : QDivisor.toRDivisor B = Finsupp.single C (1 : ℝ) := Finsupp.ext fun C'' => by
    change (QDivisor.toRDivisor B).coeff C'' = _
    rw [QDivisor.coeff_toRDivisor, eq_single_of_support_eq_singleton hC hB1]
    change ((Finsupp.single C (1 : ℚ) C'' : ℚ) : ℝ) = _
    rw [Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  have htr := transformPrimeDivisor_inverse_eq_some hTv h hY hf C C' hη
  have hcoeff : (birationalInverseTransform h hf (QDivisor.toRDivisor B)).coeff C' ≠ 0 := by
    change (birationalInverseTransform h hf (QDivisor.toRDivisor B)) C' ≠ 0
    rw [hBR, birationalInverseTransform, MMP.Mori.RationalMap.transformDivisor,
      DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_some htr, Finsupp.single_eq_same]
    exact one_ne_zero
  have hG1 : G.coeff C' = 1 := (hGiff C').mpr (Or.inl hcoeff)
  have hmemG : C' ∈ G.support := Finsupp.mem_support_iff.mpr (by
    change G.coeff C' ≠ 0; rw [hG1]; exact one_ne_zero)
  have hCsm := hGsnc.2.1 C' hmemG
  obtain ⟨w, hw⟩ : ∃ w : W.toScheme, w.1 = P := ⟨⟨P, hPW⟩, rfl⟩
  set v := (inv (h ∣_ W)) w with hvdef
  have hPP : h ((h ⁻¹ᵁ W).ι v) = P := by
    have h1 : (h ∣_ W) v = w := by
      rw [hvdef, ← Scheme.Hom.comp_apply (inv (h ∣_ W)) (h ∣_ W), IsIso.inv_hom_id]; rfl
    exact (morphismRestrict_base_coe h W v).symm.trans ((congrArg Subtype.val h1).trans hw)
  have hCW : C.genericPoint ∈ W := by
    have hs : C.genericPoint ⤳ P := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hPC
      exact specializes_iff_mem_closure.mpr hPC
    exact hs.mem_open W.isOpen hPW
  obtain ⟨hmem, hmul⟩ := mem_support_iff_and_multiplicityAt_eq_of_isIso_restrict h W C C' hη hCW
    ((h ⁻¹ᵁ W).ι v) (hPP ▸ hPW)
  rw [hPP] at hmem hmul
  have hP'C' := hmem.mpr hPC
  have h1 : C'.multiplicityAt ((h ⁻¹ᵁ W).ι v) = 1 := by
    refine (multiplicityAt_eq_one_iff_exists_mem_smoothLocus hYv hYs hYd C' hP'C').mpr ?_
    have hr : (h ⁻¹ᵁ W).ι v ∈ Set.range C'.idealSheaf.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hP'C'
    obtain ⟨z, hz⟩ := hr
    refine ⟨z, hz, ?_⟩
    have h2 : Scheme.Hom.smoothLocus (C'.idealSheaf.subschemeι ≫ h ≫ sT) = ⊤ :=
      Scheme.Hom.smoothLocus_eq_top_iff.mpr ((isSmoothScheme_iff _).mp hCsm)
    rw [smoothLocus_eq_smoothLocus, h2]; trivial
  rw [hmul, hmult] at h1
  exact absurd h1 (by decide)

/-- On a smooth scheme every `ℝ`-divisor is an `ℝ`-combination of Cartier divisors. -/
private theorem isCartierCombination_of_isSmoothScheme {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [IsNormal Y] (hsm : IsSmoothScheme sY)
    (D : RDivisor Y) : IsCartierCombination D := by
  classical
  have hsum : D = ∑ C ∈ D.support, D C • Divisor.toRDivisor (Finsupp.single C (1 : ℤ)) := by
    conv_lhs => rw [← Finsupp.sum_single D]
    refine Finset.sum_congr rfl fun C _ => ?_
    ext Γ
    change (Finsupp.single C (D C)) Γ = D C * (Divisor.toRDivisor (Finsupp.single C 1)).coeff Γ
    rw [Divisor.coeff_toRDivisor]
    by_cases h : C = Γ <;> simp [DivisorWithCoeffs.coeff, h]
  rw [hsum]
  refine ⟨D.support.card, fun j => D (D.support.equivFin.symm j),
    fun j => Finsupp.single (D.support.equivFin.symm j).1 (1 : ℤ),
    fun j => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _, ?_⟩
  simp only [← toRDivisor_eq_mapCoeffs]
  rw [← Finset.sum_coe_sort D.support]
  exact (Equiv.sum_comp D.support.equivFin.symm
    (fun i : D.support => D i • Divisor.toRDivisor (Finsupp.single i.1 (1 : ℤ)))).symm

/-- **The geometric core.** A resolution of a smooth surface, with a reduced irreducible boundary
curve `C` of multiplicity two at `P`, has an exceptional prime divisor of log discrepancy zero:
the strict transform of the exceptional curve of the blow-up of `P`. -/
private theorem exists_exceptional_logDiscrepancy_zero {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] [LocallyOfFiniteType sT] {P : T} (hP : IsClosed ({P} : Set T))
    (hdim : topologicalKrullDim T = 2) (hsm : IsSmoothScheme sT) {B : QDivisor T}
    {C : MMP.Mori.PrimeDivisor T} (hC : B.support = {C}) (hB1 : B C = 1) (hPC : P ∈ C.support)
    (hmult : C.multiplicityAt P = 2) {K : Divisor T} (hK : K.IsCanonicalDivisor sT 2)
    {Y' : Scheme.{u}} {h : Y' ⟶ T} (hLR : MMP.Flips.IsLogResolution sT (QDivisor.toRDivisor B) h) :
    ∃ (hY : IsNormalVariety k (h ≫ sT)) (hf : IsBirationalMorphism h) (hp : IsProper h)
      (E : MMP.Mori.PrimeDivisor Y'),
      (ProperDivisorOver.mk ⟨Y', h, hY, hf, E⟩ hp).IsExceptional ∧
      IsLogDiscrepancy sT 2 K (QDivisor.toRDivisor B)
        (ProperDivisorOver.mk ⟨Y', h, hY, hf, E⟩ hp).valuation 0 := by
  classical
  have hnon := not_isIso_restrict_of_multiplicity_two hdim hC hB1 hPC hmult hLR
  obtain ⟨hlv, hYv, hYs, hp, hf, G, hG01, hGiff, hGsnc⟩ := hLR
  have hTv : IsNormalVariety k sT := hlv.isNormalVariety
  have hY : IsNormalVariety k (h ≫ sT) :=
    ⟨hYv, (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2⟩
  have hG' : IsSurfaceGerm sT P := by
    refine ⟨hTv, hdim, hP, fun y _ => ?_⟩
    have h1 : Scheme.Hom.smoothLocus sT = ⊤ :=
      Scheme.Hom.smoothLocus_eq_top_iff.mpr ((isSmoothScheme_iff _).mp hsm)
    rw [smoothLocus_eq_smoothLocus, h1]; trivial
  have hB : IsSurfaceGermWithBoundary sT P B := by
    refine ⟨hG', fun C' hC' => ?_, fun C' => ?_⟩
    · rw [hC, Finset.mem_singleton] at hC'
      exact hC' ▸ hPC
    · rw [eq_single_of_support_eq_singleton hC hB1, Finsupp.single_apply]
      split_ifs <;> norm_num
  have hmultB : DivisorWithCoeffs.multiplicityAt B P = 2 := by
    rw [eq_single_of_support_eq_singleton hC hB1, DivisorWithCoeffs.multiplicityAt_single, hmult]
    simp
  have hKB : HoldsOnGerm {P} fun U : T.Opens =>
      IsCartierCombination
        (DivisorWithCoeffs.restrictOpen U (Divisor.toRDivisor K + QDivisor.toRDivisor B)) := by
    refine ⟨⊤, by simp, ?_⟩
    have : IsSmoothScheme ((⊤ : T.Opens).ι ≫ sT) := by
      rw [isSmoothScheme_iff] at hsm ⊢
      infer_instance
    exact isCartierCombination_of_isSmoothScheme this _
  obtain ⟨F, hF⟩ : ∃ F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{P}, hP⟩ : Closeds T))), F.idealSheaf =
        exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{P}, hP⟩) := by
    have := hTv.1.toIsIntegral
    have := hTv.1.toLocallyOfFiniteType
    obtain ⟨F, hF, -⟩ :=
      (MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sT _
        (isSmoothBlowup_vanishingIdeal_singleton sT hsm hP)
        (isIrreducible_support_vanishingIdeal_singleton hP)
        (one_le_codimension_vanishingIdeal_singleton hdim hP)).2
    exact ⟨F, hF⟩
  obtain ⟨hBl, hπ, hpπ, hBld, hLD⟩ := exists_logDiscrepancy_zero_blowUp hB hsm hmultB hK hKB hP hF
  haveI := hYv.toIsIntegral
  haveI := hYv.toLocallyOfFiniteType
  have hYd : topologicalKrullDim Y' = 2 :=
    (topologicalKrullDim_eq_of_isBirationalMorphism (sT := sT) hf).trans hdim
  obtain ⟨F'', hval, hηF⟩ := exists_primeDivisor_valuation_eq_of_not_isIso hTv.1 hsm hdim hYv hYs
    hYd h rfl hf hP hnon hBl hπ hpπ hY hBld F
  refine ⟨hY, hf, hp, F'', ?_, ?_⟩
  · have hπP : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{P}, hP⟩ : Closeds T))
        F.genericPoint = P :=
      (mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hP hF F.genericPoint).mp
        (MMP.Flips.primeDivisor_genericPoint_mem_support F)
    have hhP : h F''.genericPoint = P := hηF.trans hπP
    have hc : (((ProperDivisorOver.mk ⟨Y', h, hY, hf, F''⟩ hp).center : IrreducibleCloseds T) :
        Set T) = {P} := by
      rw [ProperDivisorOver.center_eq_toDivisorOver_center]
      refine (DivisorOver.center_eq_closure_genericPoint
        (⟨Y', h, hY, hf, F''⟩ : DivisorOver k sT)).trans ?_
      change closure {h F''.genericPoint} = _
      rw [hhP]
      exact hP.closure_eq
    unfold ProperDivisorOver.IsExceptional
    rw [hc, hdim]
    have : Nonempty ({P} : Set T) := ⟨⟨P, rfl⟩⟩
    rw [topologicalKrullDim_eq_zero_of_discreteTopology_nonempty]
    norm_num
  · have hv : (ProperDivisorOver.mk ⟨Y', h, hY, hf, F''⟩ hp).valuation =
        (ProperDivisorOver.mk ⟨_, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{P}, hP⟩ : Closeds T)), hBl, hπ, F⟩ hpπ).valuation := hval
    rw [hv]
    exact hLD

/-- A surface germ which is smooth at `P`, with a reduced irreducible boundary curve of
multiplicity two at `P`, is not log terminal. -/
private theorem not_isLogTerminal_of_multiplicity_two {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} {sT : T ⟶ Spec (.of k)} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] [LocallyOfFiniteType sT] {P : T} (hP : IsClosed ({P} : Set T))
    (hdim : topologicalKrullDim T = 2) (hsm : IsSmoothScheme sT) {B : QDivisor T}
    {C : MMP.Mori.PrimeDivisor T} (hC : B.support = {C}) (hB1 : B C = 1) (hPC : P ∈ C.support)
    (hmult : C.multiplicityAt P = 2) (K : Divisor T) :
    ¬ IsLogTerminal sT 2 K (QDivisor.toRDivisor B) := by
  rintro ⟨-, hK, -, Y', h, hLR, hpos⟩
  obtain ⟨hY, hf, hp, E, hexc, hld⟩ :=
    exists_exceptional_logDiscrepancy_zero hP hdim hsm hC hB1 hPC hmult hK hLR
  exact lt_irrefl _ (hpos hY hf hp E hexc 0 hld)

/-- On an integral scheme of dimension two, locally of finite type over `k`, every curve is a
prime divisor. -/
private theorem exists_primeDivisor_of_isCurveIn {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 2) {C : Y.IdealSheafData} (hC : IsCurveIn C) :
    ∃ E : MMP.Mori.PrimeDivisor Y, E.idealSheaf = C := by
  haveI := hC.1
  set ζ := C.subschemeι (genericPoint C.subscheme)
  have hcl : closure ({ζ} : Set Y) = (C.support : Set Y) :=
    MMP.Resolution.closure_subschemeι_genericPoint C
  have h := topologicalKrullDim_closure_singleton_add_coheight sY ζ
  have h1 := hC.2
  rw [topologicalKrullDim_subscheme_eq] at h1
  rw [hcl, h1, hdim] at h
  have hc : Order.coheight ζ = 1 := by
    generalize Order.coheight ζ = d at h ⊢
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have h' : ((1 + d : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) :=
        WithBot.coe_injective (by push_cast; exact h)
      have : d = 1 := by have := Nat.cast_injective h'; omega
      subst this; rfl
  refine ⟨⟨C, hC.1, ?_⟩, rfl⟩
  change codimension (IrreducibleCloseds.closureSingleton ζ) = 1
  rw [Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight, hc]

/-- If `f` is an isomorphism over a neighbourhood of `P`, there is no exceptional curve over
`P`. -/
private theorem not_isGermExceptionalCurve_of_isIso {X Y : Scheme.{u}} {P : X} {f : Y ⟶ X}
    {W : X.Opens} (hPW : P ∈ W) [IsIso (f ∣_ W)] (E : MMP.Mori.PrimeDivisor Y)
    (h : IsGermExceptionalCurve f P E) : False := by
  apply h.2.not_subsingleton
  intro a ha b hb
  have ha' : f a = P := h.1.1.2 ha
  have hb' : f b = P := h.1.1.2 hb
  exact Stacks.Models.eq_of_isIso_morphismRestrict f W (show f a ∈ W by rw [ha']; exact hPW)
    (ha'.trans hb'.symm)

/-- A resolution of a surface germ is either an isomorphism over a neighbourhood of the point, or
has an exceptional curve. -/
private theorem exists_isIso_restrict_or_isGermExceptionalCurve {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {P : X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hres : IsGermResolution sX P f) :
    (∃ W : X.Opens, P ∈ W ∧ IsIso (f ∣_ W)) ∨
      ∃ E : MMP.Mori.PrimeDivisor Y, IsGermExceptionalCurve f P E := by
  classical
  haveI : IsIntegral Y := hres.isIntegral
  haveI : IsProper f := hres.isSmoothResolution.isProper
  have hb : IsBirational f := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    hres.isSmoothResolution.isBirationalMorphism
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : NoetherianSpace Y := (haveI : IsNoetherian Y := {}; inferInstance)
  have hdY : topologicalKrullDim Y ≤ 2 := hres.topologicalKrullDim_eq.le
  have hPcl : IsClosed ({P} : Set X) := hres.isSurfaceGerm.2.2.1
  by_cases hP : P ∈ MMP.Resolution.Bridges.finiteFibreLocus f
  · left
    obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1
      inferInstance
    exact ⟨⟨_, hU⟩, hP, hiso⟩
  · right
    set S := (MMP.Resolution.Bridges.finiteFibreLocus f)ᶜ
    have hPS : P ∈ S := hP
    have hT : IsClosed (f ⁻¹' {P}) := hPcl.preimage f.continuous
    have hTS : IsClosed (f ⁻¹' S) :=
      (isClosed_compl_finiteFibreLocus f hb).preimage f.continuous
    have hPS' : f ⁻¹' {P} ⊆ f ⁻¹' S := Set.preimage_mono (Set.singleton_subset_iff.mpr hPS)
    have hinf : ¬ (f ⁻¹' {P}).Finite := hP
    obtain ⟨Z, hZf, hZc, hZirr, hZ⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
    obtain ⟨W, hWZ, hWinf⟩ : ∃ W ∈ Z, ¬ W.Finite := by
      by_contra hcon
      push Not at hcon
      exact hinf (hZ ▸ hZf.sUnion hcon)
    obtain ⟨g, hg⟩ := QuasiSober.sober (hZirr W hWZ) (hZc W hWZ)
    have hWT : W ⊆ f ⁻¹' {P} := hZ ▸ Set.subset_sUnion_of_mem hWZ
    have hgW : g ∈ W := hg.mem
    have hgnc : ¬ IsClosed ({g} : Set Y) := fun hcl => hWinf (by
      rw [← hg.def, hcl.closure_eq]; exact Set.finite_singleton _)
    have hWne : W ≠ Set.univ := by
      intro hWu
      have hgen : genericPoint Y ∈ W := hWu ▸ Set.mem_univ _
      have : f (genericPoint Y) = P := hWT hgen
      exact hP (this ▸ map_genericPoint_mem_finiteFibreLocus f hb)
    have hWc : IsClosed W := hZc W hWZ
    obtain ⟨c, hcl, hgc, hne⟩ := exists_isClosed_singleton_specializes hgnc
    have hcW : c ∈ W := by
      rw [← hg.def]; exact specializes_iff_mem_closure.mp hgc
    have hdim1 : topologicalKrullDim W = 1 :=
      topologicalKrullDim_eq_one_of_ne_univ hdY hWc hWne hgW hcW hgc hne
    have hmaxgen : ∀ B : Set Y, IsIrreducible B → B ⊆ f ⁻¹' S → W ⊆ B → B ⊆ W := by
      intro B hB hBS hWB
      have h := closure_singleton_eq_of_subset_preimage f hb hdY hgnc hB.closure isClosed_closure
        (subset_closure (hWB hgW)) (closure_minimal hBS hTS)
      rw [hg.def] at h
      rw [h]; exact subset_closure
    have hmax : Maximal (fun Z : Set Y ↦ IsIrreducible Z ∧ Z ⊆ f.base ⁻¹' S) W :=
      ⟨⟨hZirr W hWZ, hWT.trans hPS'⟩, fun B hB hWB => hmaxgen B hB.1 hB.2 hWB⟩
    obtain ⟨C, hC, hCsupp⟩ := (maximal_and_topologicalKrullDim_eq_one_iff f hb hdY W).mp
      ⟨hmax, hdim1⟩
    haveI : LocallyOfFiniteType (f ≫ sX) :=
      (hres.isSmoothResolution.isNormalVariety hres.isSurfaceGerm.1).1.1.toLocallyOfFiniteType
    have hdimY : topologicalKrullDim Y = 2 := hres.topologicalKrullDim_eq
    obtain ⟨E, hE⟩ := exists_primeDivisor_of_isCurveIn (sY := f ≫ sX) hdimY hC.1
    have hEsupp : (E.support : Set Y) = W := by
      change (E.idealSheaf.support : Set Y) = W
      rw [hE]; exact hCsupp
    refine ⟨E, ?_, hE ▸ hC.1⟩
    rw [hEsupp]
    exact ⟨⟨hZirr W hWZ, hWT⟩, fun B hB hWB => hmaxgen B hB.1 (hB.2.trans hPS') hWB⟩

/-- A resolution that is an isomorphism over a neighbourhood of `P` shows `X` smooth at `P`. -/
private theorem mem_smoothLocus_of_isIso_restrict {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [LocallyOfFiniteType sX] {P : X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hres : IsGermResolution sX P f) {W : X.Opens} (hPW : P ∈ W) [IsIso (f ∣_ W)] :
    P ∈ smoothLocus sX := by
  rw [mem_smoothLocus_iff]
  refine ⟨W, hPW, ?_⟩
  haveI : LocallyOfFiniteType (f ≫ sX) :=
    (hres.isSmoothResolution.isNormalVariety hres.isSurfaceGerm.1).1.1.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation (f ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
  have hsm : Smooth (f ≫ sX) := by
    have := hres.isSmoothResolution.isSmoothScheme
    rwa [isSmoothScheme_iff] at this
  have h1 : W.ι = inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι ≫ f := by
    rw [← morphismRestrict_ι f W, IsIso.inv_hom_id_assoc]
  rw [h1, Category.assoc, Category.assoc]
  infer_instance

/-- If the minimal resolution of a surface germ has no exceptional curves (`n = 0`), the surface
is smooth at the point: the resolution is an isomorphism near it, by the finite-fibre
isomorphism theorem. -/
private theorem smooth_of_minimalWeightedDualGraph_fin_zero {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {P : X} {B : QDivisor X}
    (hn : ∃ Γ : WeightedGraph (Fin 0), IsMinimalWeightedDualGraph sX P B Γ) :
    P ∈ smoothLocus sX := by
  obtain ⟨Γ, Y, f, hqc, hln, hnm, E, hmin, hw⟩ := hn
  rcases exists_isIso_restrict_or_isGermExceptionalCurve hmin.1 with ⟨W, hPW, hiso⟩ | ⟨E', hE'⟩
  · exact mem_smoothLocus_of_isIso_restrict hmin.1 hPW
  · obtain ⟨j, -⟩ := hw.isExceptionalCurveEnumeration.exists_eq E' hE'
    exact j.elim0

/-- A point with infinite fibre under a resolution of a germ is the point of the germ. -/
private theorem eq_of_mem_compl_finiteFibreLocus {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X}
    (hres : IsGermResolution sX P f) {x : X}
    (hx : x ∈ (MMP.Resolution.Bridges.finiteFibreLocus f)ᶜ) : x = P := by
  by_contra hne
  obtain ⟨U, hU, hiso⟩ := hres.isIso_away
  have hxU : x ∈ U := by rw [← SetLike.mem_coe, hU]; exact hne
  apply hx
  refine Set.Subsingleton.finite fun a ha b hb => ?_
  have ha' : f a = x := ha
  have hb' : f b = x := hb
  exact Stacks.Models.eq_of_isIso_morphismRestrict f U (show f a ∈ U by rw [ha']; exact hxU)
    (ha'.trans hb'.symm)

/-- A minimal resolution of a surface germ is a minimal resolution of the surface. -/
private theorem isMinimalSurfaceResolution_of_isMinimalGermResolution {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {P : X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hmin : IsMinimalGermResolution sX P f) : IsMinimalSurfaceResolution sX f := by
  classical
  have hres := hmin.1
  refine ⟨hres.isSmoothResolution, ?_⟩
  rintro ⟨E, hEx, hsr, hint⟩
  haveI : IsIntegral Y := hres.isIntegral
  haveI : IsProper f := hres.isSmoothResolution.isProper
  have hb : IsBirational f := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    hres.isSmoothResolution.isBirationalMorphism
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : NoetherianSpace Y := (haveI : IsNoetherian Y := {}; inferInstance)
  haveI : LocallyOfFiniteType (f ≫ sX) :=
    (hres.isSmoothResolution.isNormalVariety hres.isSurfaceGerm.1).1.1.toLocallyOfFiniteType
  have hdimY : topologicalKrullDim Y = 2 := hres.topologicalKrullDim_eq
  have hdY : topologicalKrullDim Y ≤ 2 := hdimY.le
  set S := (MMP.Resolution.Bridges.finiteFibreLocus f)ᶜ
  have hTS : IsClosed (f ⁻¹' S) :=
    (isClosed_compl_finiteFibreLocus f hb).preimage f.continuous
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1
    inferInstance
  have hES : ∀ z ∈ (E.support : Set Y), f z ∈ S := fun z hz hfin => by
    have h1 : z ∈ (MMP.Mori.exceptionalSet f : Set Y) := hEx hz
    rw [SetLike.mem_coe, MMP.Mori.mem_exceptionalSet] at h1
    exact h1 (MMP.Mori.le_biregularLocus (f := f) (V := ⟨_, hU⟩) hiso hfin)
  have hEP : ∀ z ∈ (E.support : Set Y), f z = P := fun z hz =>
    eq_of_mem_compl_finiteFibreLocus hres (hES z hz)
  have hgen : E.genericPoint ∈ (E.support : Set Y) := primeDivisor_genericPoint_mem_support E
  have hPS : P ∈ S := by
    have h1 := hES _ hgen
    rwa [hEP _ hgen] at h1
  have hPS' : f ⁻¹' {P} ⊆ f ⁻¹' S := Set.preimage_mono (Set.singleton_subset_iff.mpr hPS)
  apply hmin.2
  refine ⟨E, ⟨?_, hsr.1.1⟩, hsr, hint⟩
  haveI := E.integral
  refine ⟨⟨isIrreducible_support_of_isIntegral E.idealSheaf, hEP⟩, fun B hB hEB => ?_⟩
  have hnc := not_isClosed_singleton_genericPoint (f ≫ sX) hdimY E
  have h := closure_singleton_eq_of_subset_preimage f hb hdY hnc hB.1.closure isClosed_closure
    (subset_closure (hEB hgen)) (closure_minimal (hB.2.trans hPS') hTS)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, h]
  exact subset_closure

/-- If `(X, P)` is smooth at `P`, the type (9) data of a germ is its `n = 0` branch: the
minimal resolution of a germ smooth at `P` is an isomorphism near `P`, so has no exceptional
curves, and `Fin n` is empty. -/
private theorem exists_multAt_sum_eq_two_of_isFig3Type9 {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {P : X} {B : QDivisor X}
    (h9 : IsFig3Type9 sX P B) (hsm : P ∈ smoothLocus sX) :
    ∃ (hP : IsClosed ({P} : Set X)) (m : MMP.Mori.PrimeDivisor X → ℕ),
        (∀ C ∈ B.support, MMP.Resolution.multAt C.idealSheaf P = m C) ∧
        ∑ C ∈ B.support, B C * m C = 2 ∧
        ((⋃ C ∈ B.support,
            SetLike.coe (MMP.Resolution.birationalTransform P hP C.idealSheaf).support) ∩
          SetLike.coe (exceptionalIdeal
            (Scheme.IdealSheafData.vanishingIdeal ⟨{P}, hP⟩)).support).ncard = 2 := by
  obtain ⟨hG, Y, f, hqc, hln, hnm, n, E, hmin, henum, hcase⟩ := h9
  rcases hcase with ⟨-, hP, m, hm, hsum, hnc⟩ | ⟨hn, -⟩
  · exact ⟨hP, m, hm, hsum, hnc⟩
  · exfalso
    have hiso := MMP.Mori.isIso_morphismRestrict_smoothLocus_of_isMinimalSurfaceResolution sX f
      hG.1.1 hG.1.2.1 (isMinimalSurfaceResolution_of_isMinimalGermResolution hmin)
    exact not_isGermExceptionalCurve_of_isIso (W := smoothLocus sX) hsm (E ⟨0, hn⟩)
      (henum.isGermExceptionalCurve _)

/-- The germ data of the type (9) hypothesis with `n = 0`: `X` is smooth at `P`, and the boundary
curve has multiplicity two at `P`. -/
private theorem mem_smoothLocus_and_multiplicityAt_of_isFig3Type9
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {P : X} {B : QDivisor X}
    (h9 : IsFig3Type9 sX P B) (hred : IsReducedBoundary B)
    (hn : ∃ Γ : WeightedGraph (Fin 0), IsMinimalWeightedDualGraph sX P B Γ)
    {C : MMP.Mori.PrimeDivisor X} (hC : B.support = {C}) :
    P ∈ smoothLocus sX ∧ C.multiplicityAt P = 2 := by
  have hsm := smooth_of_minimalWeightedDualGraph_fin_zero hn
  obtain ⟨hPcl, m, hm, hsum, -⟩ := exists_multAt_sum_eq_two_of_isFig3Type9 h9 hsm
  have hCmem : C ∈ B.support := by rw [hC]; exact Finset.mem_singleton_self C
  refine ⟨hsm, ?_⟩
  rw [hC, Finset.sum_singleton, hred C hCmem] at hsum
  have h2 : m C = 2 := by exact_mod_cast (by simpa using hsum : (m C : ℚ) = 2)
  have := hm C hCmem
  rw [PrimeDivisor.multiplicityAt, Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  rwa [h2] at this

/-- The boundary curve of a germ restricts to a boundary curve of the same multiplicity on an
open neighbourhood `U` of `P`. -/
private theorem exists_primeDivisor_restrictOpen_of_mem {X : Scheme.{u}} {P : X} {B : QDivisor X}
    {C : MMP.Mori.PrimeDivisor X} (hC : B.support = {C}) (hB1 : B C = 1) (hPC : P ∈ C.support)
    (hmult : C.multiplicityAt P = 2) (U : X.Opens) (hPU : P ∈ U) :
    ∃ CU : MMP.Mori.PrimeDivisor U, (DivisorWithCoeffs.restrictOpen U B).support = {CU} ∧
      (DivisorWithCoeffs.restrictOpen U B) CU = 1 ∧ (⟨P, hPU⟩ : U) ∈ CU.support ∧
      CU.multiplicityAt ⟨P, hPU⟩ = 2 := by
  obtain ⟨CU, hCU⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    U.ι C ⟨P, hPU⟩ hPC
  have hB1' : (DivisorWithCoeffs.restrictOpen U B) CU = 1 := by
    change B (OpenWeilRestriction.primeDivisorMap U.ι CU) = 1
    rwa [hCU]
  refine ⟨CU, ?_, hB1', ?_, ?_⟩
  · refine Finset.ext fun W => ?_
    rw [Finset.mem_singleton, Finsupp.mem_support_iff]
    constructor
    · intro h
      have h1 : OpenWeilRestriction.primeDivisorMap U.ι W ∈ B.support :=
        Finsupp.mem_support_iff.mpr h
      rw [hC, Finset.mem_singleton, ← hCU] at h1
      exact OpenWeilRestriction.primeDivisorMap_injective U.ι h1
    · rintro rfl; rw [hB1']; exact one_ne_zero
  · exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι CU ⟨P, hPU⟩).mp
      (by rwa [hCU])
  · rwa [multiplicityAt_primeDivisorMap U.ι CU ⟨P, hPU⟩, hCU]

/-- Restriction of the germ data to an open neighbourhood `U` of `P`. -/
private theorem restrictOpen_isGerm_of_mem_smoothLocus {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {P : X} {B : QDivisor X}
    (hG : IsSurfaceGerm sX P) (hsm : P ∈ smoothLocus sX)
    {C : MMP.Mori.PrimeDivisor X} (hC : B.support = {C}) (hB1 : B C = 1) (hPC : P ∈ C.support)
    (hmult : C.multiplicityAt P = 2) (U : X.Opens) (hPU : P ∈ U) :
    IsClosed ({(⟨P, hPU⟩ : U)} : Set U) ∧ topologicalKrullDim U = 2 ∧
      IsSmoothScheme (U.ι ≫ sX) ∧
      ∃ CU : MMP.Mori.PrimeDivisor U, (DivisorWithCoeffs.restrictOpen U B).support = {CU} ∧
        (DivisorWithCoeffs.restrictOpen U B) CU = 1 ∧ (⟨P, hPU⟩ : U) ∈ CU.support ∧
        CU.multiplicityAt ⟨P, hPU⟩ = 2 := by
  haveI : Nonempty U := ⟨⟨P, hPU⟩⟩
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨P, hPU⟩)
  refine ⟨?_, ?_, ?_, exists_primeDivisor_restrictOpen_of_mem hC hB1 hPC hmult U hPU⟩
  · have : ({(⟨P, hPU⟩ : U)} : Set U) = U.ι ⁻¹' {P} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
    rw [this]
    exact hG.2.2.1.preimage U.ι.continuous
  · have hbij := MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
      ⟨⟨P, hPU⟩, trivial⟩
    rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]
    exact hG.2.1
  · have h1 : Scheme.Hom.smoothLocus sX = ⊤ := by
      refine top_unique fun y _ => ?_
      by_cases hy : y = P
      · subst hy
        rwa [← smoothLocus_eq_smoothLocus]
      · rw [← smoothLocus_eq_smoothLocus]
        exact hG.2.2.2 y hy
    rw [isSmoothScheme_iff]
    have : Smooth sX := Scheme.Hom.smoothLocus_eq_top_iff.mp h1
    infer_instance

/-- **A node on a smooth surface germ is not log terminal** (FA Ex. 2.14, Fig. 3 (9)). Let
`(X, P; B)` have reduced boundary `B` with exactly one component `C`, let the minimal resolution
of `(X, P)` have no exceptional curves, and let `(X, P; B)` be of type (9). Then for every open
neighbourhood `U` of `P` and every divisor `K` on `X`, the pair `(U, B|_U)` with canonical divisor
`K|_U` is not log terminal. -/
@[mmp "lem_fa3_smooth_point_nodal_not_lt"]
public theorem IsFig3Type9.not_isLogTerminal_near {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {P : X} {B : QDivisor X}
    (h9 : IsFig3Type9 sX P B) (hred : IsReducedBoundary B)
    (hn : ∃ Γ : WeightedGraph (Fin 0), IsMinimalWeightedDualGraph sX P B Γ)
    {C : Mori.PrimeDivisor X} (hC : B.support = {C}) (K : Divisor X) :
    ¬ HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogTerminal (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) := by
  rintro ⟨U, hPU, hU⟩
  have hPU : P ∈ U := hPU rfl
  haveI : Nonempty U := ⟨⟨P, hPU⟩⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp
    (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
  obtain ⟨hsm, hmult⟩ := mem_smoothLocus_and_multiplicityAt_of_isFig3Type9 h9 hred hn hC
  have hCmem : C ∈ B.support := by rw [hC]; exact Finset.mem_singleton_self C
  have hPC : P ∈ C.support := h9.1.2.1 C hCmem
  have hB1 : B C = 1 := hred C hCmem
  obtain ⟨hcl, hdim, hsmU, CU, hCU, hBCU, hPCU, hmultU⟩ :=
    restrictOpen_isGerm_of_mem_smoothLocus h9.1.1 hsm hC hB1 hPC hmult U hPU
  have hBres : QDivisor.toRDivisor (DivisorWithCoeffs.restrictOpen U B) =
      DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B) :=
    Finsupp.ext fun W => by
      change (QDivisor.toRDivisor (DivisorWithCoeffs.restrictOpen U B)).coeff W = _
      rw [QDivisor.coeff_toRDivisor]
      rfl
  rw [← hBres] at hU
  exact not_isLogTerminal_of_multiplicity_two hcl hdim hsmU hCU hBCU hPCU hmultU _ hU

end MMP.Flips

/-! ### A reduced Cartier divisor through a prescribed closed subset -/

namespace MMP.Mori

/-! ### Generic points -/

/-- The generic point of a prime divisor specializes to every point of it. -/
private theorem genericPoint_specializes {X : Scheme.{u}} (E : MMP.Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ E.support) : E.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
  exact specializes_iff_mem_closure.mpr hx

/-- A prime divisor whose generic point lies in a closed set lies in it. -/
private theorem support_subset_of_genericPoint_mem {X : Scheme.{u}} (E : MMP.Mori.PrimeDivisor X)
    {T : Set X} (hT : IsClosed T) (h : E.genericPoint ∈ T) : E.support ⊆ T := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) hT

/-- The generic point of an integral scheme lies in no proper closed subset. -/
private theorem genericPoint_notMem {X : Scheme.{u}} [IsIntegral X] {T : Set X}
    (hT : IsClosed T) (hT' : T ≠ Set.univ) : genericPoint X ∉ T := fun h =>
  hT' <| Set.eq_univ_of_univ_subset <| ((genericPoint_spec X).mem_closed_set_iff hT).mp h

/-- On a Noetherian integral scheme, only finitely many prime divisors have their generic point
in a proper closed subset. -/
private theorem finite_setOf_genericPoint_mem_of_ne_univ {X : Scheme.{u}} [IsIntegral X]
    [TopologicalSpace.NoetherianSpace X] {T : Set X} (hT : IsClosed T) (hT' : T ≠ Set.univ) :
    {E : MMP.Mori.PrimeDivisor X | E.genericPoint ∈ T}.Finite :=
  MMP.Mori.finite_setOf_genericPoint_mem hT fun x hx h0 => genericPoint_notMem hT hT' <| by
    have hηx : genericPoint X ⤳ x := (genericPoint_spec X).specializes (Set.mem_univ x)
    exact (hηx.antisymm (Order.coheight_eq_zero.mp h0 hηx)).eq ▸ hx

/-! ### The zero scheme of a function -/

/-- The zero scheme of a function `g`, viewed as a section of `𝒪_X`, is cut out on every affine
open by the restriction of `g`. -/
private theorem zeroScheme_unitModule_ideal (X : Scheme.{u}) (U : X.affineOpens) (g : Γ(X, ⊤)) :
    (zeroScheme X (Stacks.Ample.unitModule X) g).ideal U =
      Ideal.span {X.presheaf.map (homOfLE le_top).op g} := by
  refine (zeroScheme_ideal X (Stacks.Ample.unitModule X) g U).trans ?_
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro a ⟨φ, rfl⟩
    have h1 : ((Stacks.Ample.unitModule X).presheaf.map (homOfLE le_top).op g :
        Γ(Stacks.Ample.unitModule X, U.1)) =
        (X.presheaf.map (homOfLE le_top).op g : Γ(X, U.1)) •
          (show Γ(Stacks.Ample.unitModule X, U.1) from (1 : Γ(X, U.1))) :=
      (mul_one (X.presheaf.map (homOfLE le_top).op g : Γ(X, U.1))).symm
    rw [h1, φ.map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨LinearMap.id, rfl⟩

/-- Every point of a scheme lies in an affine open. -/
private theorem exists_affineOpens_mem {X : Scheme.{u}} (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hx⟩

/-- A point lies on the zero scheme of a function exactly when the germ of the function there is
not a unit. -/
private theorem mem_support_zeroScheme_unitModule_iff (X : Scheme.{u}) (g : Γ(X, ⊤)) (x : X) :
    x ∈ (zeroScheme X (Stacks.Ample.unitModule X) g).support ↔
      ¬ IsUnit ((X.presheaf.germ ⊤ x trivial).hom g) := by
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, zeroScheme_unitModule_ideal,
    Scheme.mem_zeroLocus_iff]
  have hres : (X.presheaf.germ U.1 x hxU).hom (X.presheaf.map (homOfLE le_top).op g) =
      (X.presheaf.germ ⊤ x trivial).hom g :=
    X.presheaf.germ_res_apply (homOfLE le_top) x hxU g
  constructor
  · intro h
    have := h _ (Ideal.subset_span rfl)
    rwa [Scheme.mem_basicOpen _ _ _ hxU, hres] at this
  · intro h f hf hxf
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [Scheme.basicOpen_mul] at hxf
    have := (Scheme.mem_basicOpen _ _ _ hxU).mp hxf.2
    rw [hres] at this
    exact h this

/-- If the zero scheme of a function `g` is reduced, then at every point the germ of `g`
generates a radical ideal of the local ring. -/
private theorem isRadical_span_germ_of_isReduced (X : Scheme.{u}) (g : Γ(X, ⊤))
    [IsReduced (zeroScheme X (Stacks.Ample.unitModule X) g).subscheme] (x : X) :
    (Ideal.span {(X.presheaf.germ ⊤ x trivial).hom g}).IsRadical := by
  set I := zeroScheme X (Stacks.Ample.unitModule X) g with hIdef
  have hI : I = I.radical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    exact I.eq_vanishingIdeal_of_isReduced_subscheme I.support rfl
  obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
  have hrad : (Ideal.span {X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op g}).radical =
      Ideal.span {X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op g} := by
    rw [← zeroScheme_unitModule_ideal X U g, ← hIdef]
    have := congrArg (fun J => J.ideal U) hI
    simp only [Scheme.IdealSheafData.radical_ideal] at this
    exact this.symm
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U.1) ⟨x, hxU⟩
  have hloc := U.2.isLocalization_stalk ⟨x, hxU⟩
  have hspan : Ideal.span {(X.presheaf.germ ⊤ x trivial).hom g} =
      (Ideal.span {X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op g}).map
        (algebraMap Γ(X, U.1) (X.presheaf.stalk x)) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (X.presheaf.germ_res_apply (homOfLE le_top) x hxU g).symm
  rw [hspan, Ideal.IsRadical,
    ← IsLocalization.map_radical (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl, hrad]

/-! ### Uniformizers of a discrete valuation ring -/

/-- In a discrete valuation ring, a nonzero nonunit which generates a radical ideal, or which
does not lie in the square of the maximal ideal, is a uniformizer. -/
private theorem irreducible_of_isRadical_or_notMem_sq {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a : R} (ha0 : a ≠ 0) (hu : ¬ IsUnit a)
    (h : (Ideal.span {a}).IsRadical ∨ a ∉ (IsLocalRing.maximalIdeal R) ^ 2) : Irreducible a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  rcases n with _ | _ | n
  · exact absurd (by simp) hu
  · simpa [Units.isUnit, irreducible_units_mul] using hϖ
  · exfalso
    rcases h with hrad | hsq
    · have hmem : ϖ ^ (n + 2) ∈ Ideal.span {(v : R) * ϖ ^ (n + 2)} :=
        Ideal.mem_span_singleton'.mpr ⟨(v⁻¹ : Rˣ), by rw [← mul_assoc, Units.inv_mul, one_mul]⟩
      have hϖmem : ϖ ∈ Ideal.span {(v : R) * ϖ ^ (n + 2)} := hrad ⟨n + 2, hmem⟩
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hϖmem
      exact hϖ.not_isUnit (IsUnit.of_mul_eq_one ((v : R) * ϖ ^ n * c)
        (mul_left_cancel₀ hϖ.ne_zero (by linear_combination -hc)))
    · apply hsq
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton.mpr ⟨(v : R) * ϖ ^ n, by ring⟩

/-! ### Prime divisors through the zero locus of a function -/

/-- **Krull's principal ideal theorem, geometrically.** On a locally Noetherian scheme, if a
function `g` has a nonzero nonunit germ at `x`, then some prime divisor through `x` has its
generic point in the domain of `g`, with `g` vanishing there. -/
private theorem exists_primeDivisor_not_isUnit_germ {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsIntegral X] {V : X.Opens} (g : Γ(X, V)) {x : X} (hx : x ∈ V)
    (hg0 : (X.presheaf.germ V x hx).hom g ≠ 0) (hgu : ¬ IsUnit ((X.presheaf.germ V x hx).hom g)) :
    ∃ P : MMP.Mori.PrimeDivisor X, x ∈ P.support ∧ ∃ hP : P.genericPoint ∈ V,
      ¬ IsUnit ((X.presheaf.germ V P.genericPoint hP).hom g) := by
  set a := (X.presheaf.germ V x hx).hom g with ha
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le
    (J := IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    ((Ideal.span_singleton_le_iff_mem _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hgu))
  haveI hqp : q.IsPrime := hq.1.1
  have haq : a ∈ q := hq.1.2 (Ideal.subset_span rfl)
  have hheight : q.height = 1 := by
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq
    have hne : q ≠ ⊥ := fun h => hg0 (by rw [h] at haq; simpa using haq)
    refine le_antisymm h1 (ENat.one_le_iff_ne_zero.mpr ?_)
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    exact hne
  obtain ⟨P, hPx, hloc⟩ := MMP.Mori.exists_primeDivisor_isLocalization ⟨q, hqp⟩ hheight
  have hPV : P.genericPoint ∈ V := hPx.mem_open V.isOpen hx
  refine ⟨P, ?_, hPV, ?_⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hPx
  · letI := (X.presheaf.stalkSpecializes hPx).hom.toAlgebra
    have hgerm : (X.presheaf.germ V P.genericPoint hPV).hom g =
        algebraMap (X.presheaf.stalk x) (X.presheaf.stalk P.genericPoint) a := by
      rw [ha]
      exact (X.presheaf.germ_stalkSpecializes_apply hx hPx g).symm
    rw [hgerm, ← IsLocalRing.notMem_maximalIdeal, not_not]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q a).mpr haq

/-! ### Functions on an open subscheme -/

/-- The germ at `x` of a function on the open subscheme `V` is the germ at `x` of the
corresponding function on the open `V` of `X`. -/
private theorem stalkIso_germ_topIso_inv {X : Scheme.{u}} (V : X.Opens) (G : Γ(X, V)) (x : V) :
    (V.stalkIso x).hom.hom ((V.toScheme.presheaf.germ ⊤ x trivial).hom (V.topIso.inv G)) =
      (X.presheaf.germ V x.1 x.2).hom G := by
  have h1 := congrArg (fun φ => φ.hom (V.topIso.inv G))
    (Scheme.Opens.germ_stalkIso_hom V (V := ⊤) x trivial)
  simp only [CommRingCat.comp_apply] at h1
  refine h1.trans ?_
  rw [Scheme.Opens.topIso_inv]
  exact X.presheaf.germ_res_apply _ _ _ G

/-- The ring map `k → Γ(X, V)` of a scheme over `k`, on an open `V`. -/
private noncomputable def baseRing {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (V : X.Opens) : k →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom

/-- The member `∑ⱼ cⱼ gⱼ` of the linear system spanned by functions `g₀, …, g_N` on `V`. -/
private noncomputable def sysFun {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) {V : X.Opens} {N : ℕ} (g : Fin (N + 1) → Γ(X, V))
    (c : Fin (N + 1) → k) : Γ(X, V) :=
  ∑ j, baseRing s V (c j) * g j

private theorem germ_baseRing {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (V : X.Opens) {x : X} (hx : x ∈ V) (c : k) :
    (X.presheaf.germ V x hx).hom (baseRing s V c) =
      (X.presheaf.germ ⊤ x trivial).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom c) :=
  X.presheaf.germ_res_apply _ _ _ _

private theorem germ_sysFun {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) {V : X.Opens} {N : ℕ} (g : Fin (N + 1) → Γ(X, V))
    (c : Fin (N + 1) → k) {x : X} (hx : x ∈ V) :
    (X.presheaf.germ V x hx).hom (sysFun s g c) = ∑ j,
      (X.presheaf.germ ⊤ x trivial).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom (c j)) *
        (X.presheaf.germ V x hx).hom (g j) := by
  simp only [sysFun, map_sum, map_mul, germ_baseRing]

set_option backward.isDefEq.respectTransparency false in
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
attribute [local instance] globalSectionsModule in
/-- The germ of a member of the system on the open subscheme `V` is the germ of the
corresponding member on the open `V`. -/
private theorem stalkIso_germ_systemSection {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (V : X.Opens) {N : ℕ} (g : Fin (N + 1) → Γ(X, V))
    (c : Fin (N + 1) → k) (y : V) :
    letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
    (V.stalkIso y).hom.hom ((V.toScheme.presheaf.germ ⊤ y trivial).hom
      (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule V.toScheme)
        (fun j => V.topIso.inv (g j)) c)) =
      (X.presheaf.germ V y.1 y.2).hom (sysFun s g c) := by
  letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
  rw [MMP.Threefold.Bridges.systemSection_apply, germ_sysFun, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (V.stalkIso y).hom.hom ((V.toScheme.presheaf.germ ⊤ y trivial).hom
    (baseRingHom k V.toScheme (c j) * V.topIso.inv (g j))) = _
  rw [map_mul, map_mul, stalkIso_germ_topIso_inv]
  congr 1
  change (V.stalkIso y).hom.hom ((V.toScheme.presheaf.germ ⊤ y trivial).hom
    (V.ι.appTop (((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom (c j)))) = _
  set a := ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom (c j)
  have h := Scheme.Hom.germ_stalkMap_apply V.ι ⊤ y trivial a
  have h2 : (V.stalkIso y).hom.hom (V.ι.stalkMap y ((X.presheaf.germ ⊤ (V.ι y) trivial).hom a)) =
      (X.presheaf.germ ⊤ (V.ι y) trivial).hom a := by
    rw [← Scheme.Opens.stalkIso_inv]
    exact (V.stalkIso y).inv_hom_id_apply _
  exact (congrArg (V.stalkIso y).hom.hom h.symm).trans h2

/-! ### Bertini on an open subscheme -/

/-- A dense open of the coefficient space contains the nonvanishing locus of a nonzero
polynomial. -/
private theorem exists_poly_of_dense {k : Type u} [Field k] {N : ℕ}
    (U : (MMP.Threefold.Bridges.coefficientSpace k N).Opens)
    (hU : Dense (U : Set (MMP.Threefold.Bridges.coefficientSpace k N))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧
      ∀ c, MvPolynomial.eval c Q ≠ 0 → MMP.Threefold.Bridges.coefficientPoint c ∈ U := by
  haveI : Nonempty (MMP.Threefold.Bridges.coefficientSpace k N) :=
    ⟨MMP.Threefold.Bridges.coefficientPoint 0⟩
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.2
  refine ⟨f, ?_, fun c hc => hfU ?_⟩
  · rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hpf (Submodule.zero_mem _)
  · exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun h => hc ((RingHom.mem_ker).mp h)

/-- A ring isomorphism carries a radical principal ideal to a radical principal ideal. -/
private theorem isRadical_span_singleton_map {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {a : R} (h : (Ideal.span {a}).IsRadical) : (Ideal.span {e a}).IsRadical := by
  have : Ideal.span {e a} = (Ideal.span {a}).comap (e.symm : S →+* R) := by
    rw [Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
  rw [this]
  exact h.comap _

set_option backward.isDefEq.respectTransparency false in
/-- A function does not vanish at `x`, as a section of `𝒪_X`, exactly when its germ at `x` is a
unit. -/
private theorem mem_nonvanishingLocus_unitModule_iff (X : Scheme.{u}) (t : Γ(X, ⊤)) (x : X) :
    x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.unitModule X) t ↔
      IsUnit ((X.presheaf.germ ⊤ x trivial).hom t) := by
  rw [Stacks.Ample.mem_nonvanishingLocus_iff,
    Stacks.ComplementIdeal.mem_maximalSmul_iff_unitStalkFun_mem]
  change ¬ (Stacks.Ample.unitStalkFun X x
    (((Stacks.Ample.unitModule X).presheaf.germ ⊤ x trivial).hom t) ∈ _) ↔ _
  rw [Stacks.Ample.unitStalkFun_germ, IsLocalRing.notMem_maximalIdeal]

set_option backward.isDefEq.respectTransparency false in
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
attribute [local instance] globalSectionsModule in
/-- Functions on `V` without common zero generate `𝒪_V` as a linear system. -/
private theorem iSup_nonvanishingOpen_systemSection_eq_top {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (V : X.Opens) {N : ℕ} (g : Fin (N + 1) → Γ(X, V))
    (hgen : ∀ x (hx : x ∈ V), ∃ j, IsUnit ((X.presheaf.germ V x hx).hom (g j))) :
    letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
    ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen V.toScheme
      (Stacks.Ample.unitModule V.toScheme)
      (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule V.toScheme)
        (fun j => V.topIso.inv (g j)) c) = ⊤ := by
  letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨j, hj⟩ := hgen y.1 y.2
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single j 1, ?_⟩
  have hsingle : MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule V.toScheme)
      (fun j => V.topIso.inv (g j)) (Pi.single j (1 : k)) = V.topIso.inv (g j) := by
    simp [MMP.Threefold.Bridges.systemSection, Fintype.linearCombination_apply_single]
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen, hsingle, mem_nonvanishingLocus_unitModule_iff,
    ← isUnit_map_iff (V.stalkIso y).hom.hom, stalkIso_germ_topIso_inv]
  exact hj

set_option backward.isDefEq.respectTransparency false in
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
attribute [local instance] globalSectionsModule in
/-- **Bertini's theorem for reducedness, on an open.** If functions `g₀, …, g_N` on an open `V`
of a reduced scheme of finite type over `k` have no common zero, then the general member of
their span has reduced zero scheme on `V`. -/
private theorem exists_poly_isReduced {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [IsReduced X]
    (V : X.Opens) [QuasiCompact (V.ι ≫ s)] {N : ℕ} (g : Fin (N + 1) → Γ(X, V))
    (hgen : ∀ x (hx : x ∈ V), ∃ j, IsUnit ((X.presheaf.germ V x hx).hom (g j))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 →
      letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
      IsReduced (zeroScheme V.toScheme (Stacks.Ample.unitModule V.toScheme)
        (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule V.toScheme)
          (fun j => V.topIso.inv (g j)) c)).subscheme := by
  letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
  have hlft : LocallyOfFiniteType (V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ s))
  have hqc : QuasiCompact (V.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (V.ι ≫ s))
  obtain ⟨⟨U, hU, hred⟩, -⟩ := MMP.Threefold.Bridges.exists_dense_open_isReduced_zeroScheme
    (L := Stacks.Ample.unitModule V.toScheme) (fun j => V.topIso.inv (g j))
    (iSup_nonvanishingOpen_systemSection_eq_top s V g hgen)
  obtain ⟨Q, hQ, hQU⟩ := exists_poly_of_dense U hU
  exact ⟨Q, hQ, fun c hc => hred c (hQU c hc)⟩

set_option backward.isDefEq.respectTransparency false in
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
attribute [local instance] globalSectionsModule in
/-- **Bertini's theorem for reducedness, on an open, at the local rings.** If functions
`g₀, …, g_N` on an open `V` of a reduced scheme of finite type over `k` have no common zero, then
the general member of their span generates a radical ideal of every local ring of `V`. -/
private theorem exists_poly_isRadical {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [IsReduced X]
    (V : X.Opens) [QuasiCompact (V.ι ≫ s)] {N : ℕ} (g : Fin (N + 1) → Γ(X, V))
    (hgen : ∀ x (hx : x ∈ V), ∃ j, IsUnit ((X.presheaf.germ V x hx).hom (g j))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 →
      ∀ x (hx : x ∈ V), (Ideal.span {(X.presheaf.germ V x hx).hom (sysFun s g c)}).IsRadical := by
  letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
  obtain ⟨Q, hQ, hred⟩ := exists_poly_isReduced s V g hgen
  refine ⟨Q, hQ, fun c hc x hx => ?_⟩
  haveI := hred c hc
  have h := isRadical_span_germ_of_isReduced V.toScheme
    (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule V.toScheme)
      (fun j => V.topIso.inv (g j)) c) ⟨x, hx⟩
  have h2 := isRadical_span_singleton_map (V.stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv h
  rwa [show (V.stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv _ = _ from
    stalkIso_germ_systemSection s V g c ⟨x, hx⟩] at h2

set_option backward.isDefEq.respectTransparency false in
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
attribute [local instance] globalSectionsModule in
/-- **Bertini's theorem for smoothness, on an open.** If `V` is a nonempty open of a variety over
an algebraically closed field of characteristic zero, contained in the smooth locus, and
functions `g₀, …, g_N` on `V` have no common zero, then the zero scheme of the general member of
their span is smooth over `k`. -/
private theorem exists_poly_smooth {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k s]
    [IsLocallyNoetherian X]
    (V : X.Opens) [Nonempty V] [QuasiCompact (V.ι ≫ s)] (hV : V ≤ s.smoothLocus) {N : ℕ}
    (g : Fin (N + 1) → Γ(X, V))
    (hgen : ∀ x (hx : x ∈ V), ∃ j, IsUnit ((X.presheaf.germ V x hx).hom (g j))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 →
      letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
      Smooth ((zeroScheme V.toScheme (Stacks.Ample.unitModule V.toScheme)
        (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule V.toScheme)
          (fun j => V.topIso.inv (g j)) c)).subschemeι ≫ V.ι ≫ s) := by
  letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
  haveI : AlgebraicGeometry.IsVariety k (V.toScheme ↘ Spec (.of k)) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstanceAs (IsSeparated (V.ι ≫ s))
      toLocallyOfFiniteType := inferInstanceAs (LocallyOfFiniteType (V.ι ≫ s))
      toQuasiCompact := inferInstanceAs (QuasiCompact (V.ι ≫ s)) }
  have hsm : Smooth (V.toScheme ↘ Spec (.of k)) := by
    change Smooth (V.ι ≫ s)
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact eq_top_iff.mpr fun y _ => hV y.2
  let ιY : (i : PEmpty.{u + 1}) → (i.elim : Scheme.{u}) ⟶ V.toScheme := fun i => i.elim
  haveI : ∀ i, IsImmersion (ιY i) := fun i => i.elim
  haveI : ∀ i, Smooth (ιY i ≫ V.toScheme ↘ Spec (.of k)) := fun i => i.elim
  obtain ⟨⟨U, hU, hUs⟩, -⟩ := MMP.Threefold.Bridges.exists_dense_open_smooth_zeroScheme
    (L := Stacks.Ample.unitModule V.toScheme) (fun j => V.topIso.inv (g j))
    (iSup_nonvanishingOpen_systemSection_eq_top s V g hgen) ιY
  obtain ⟨Q, hQ, hQU⟩ := exists_poly_of_dense U hU
  exact ⟨Q, hQ, fun c hc => (hUs c (hQU c hc)).1 hsm⟩

set_option backward.isDefEq.respectTransparency false in
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections in
attribute [local instance] globalSectionsModule in
/-- A point of the open subscheme `V` lies on the zero scheme of a member of the system exactly
when the germ of the corresponding member on the open `V` is not a unit. -/
private theorem mem_support_zeroScheme_systemSection_iff {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (V : X.Opens) {N : ℕ} (g : Fin (N + 1) → Γ(X, V))
    (c : Fin (N + 1) → k) (y : V) :
    letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
    y ∈ (zeroScheme V.toScheme (Stacks.Ample.unitModule V.toScheme)
      (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule V.toScheme)
        (fun j => V.topIso.inv (g j)) c)).support ↔
      ¬ IsUnit ((X.presheaf.germ V y.1 y.2).hom (sysFun s g c)) := by
  letI : V.toScheme.Over (Spec (.of k)) := ⟨V.ι ≫ s⟩
  rw [mem_support_zeroScheme_unitModule_iff, ← isUnit_map_iff (V.stalkIso y).hom.hom,
    stalkIso_germ_systemSection]

/-! ### Smoothness of a reduced subscheme on an open -/

/-- The pullback along an open immersion of the reduced structure on a closed subset is the
reduced structure on its preimage. -/
private theorem comap_vanishingIdeal_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (T : TopologicalSpace.Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal T).comap f =
      Scheme.IdealSheafData.vanishingIdeal (T.preimage f.continuous) := by
  set I := Scheme.IdealSheafData.vanishingIdeal T
  haveI : IsReduced I.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal T
  haveI : IsReduced (Limits.pullback f I.subschemeι) :=
    isReduced_of_isOpenImmersion (Limits.pullback.snd f I.subschemeι)
  haveI : IsReduced (I.comap f).subscheme := isReduced_of_isOpenImmersion (I.comapIso f).hom
  refine (I.comap f).eq_vanishingIdeal_of_isReduced_subscheme _ ?_
  rw [Scheme.IdealSheafData.support_comap,
    show I.support = T from TopologicalSpace.Closeds.ext
      (Scheme.IdealSheafData.coe_support_vanishingIdeal T)]

/-- If the pullback of a closed subscheme to an open `V` is smooth over the base, then every
point of the subscheme over `V` is a smooth point of the subscheme. -/
private theorem exists_mem_smoothLocus_of_smooth_comap {X S : Scheme.{u}} (s : X ⟶ S)
    (I : X.IdealSheafData) [LocallyOfFinitePresentation (I.subschemeι ≫ s)] (V : X.Opens)
    (hsm : Smooth ((I.comap V.ι).subschemeι ≫ V.ι ≫ s)) {z : X} (hzV : z ∈ V)
    (hz : z ∈ I.support) : ∃ y, I.subschemeι y = z ∧ y ∈ (I.subschemeι ≫ s).smoothLocus := by
  let e := (I.comapIso V.ι).hom ≫ Limits.pullback.snd V.ι I.subschemeι
  have he : e ≫ I.subschemeι = (I.comap V.ι).subschemeι ≫ V.ι := by
    simp [e, ← Limits.pullback.condition]
  have hz' : (⟨z, hzV⟩ : V.toScheme) ∈ (I.comap V.ι).support := by
    rwa [Scheme.IdealSheafData.support_comap]
  have hz'' : (⟨z, hzV⟩ : V.toScheme) ∈ Set.range (I.comap V.ι).subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  obtain ⟨a, ha⟩ := hz''
  refine ⟨e a, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply, ha]
    rfl
  · have hsm' : Smooth (e ≫ I.subschemeι ≫ s) := by
      rwa [← Category.assoc, he, Category.assoc]
    change a ∈ e ⁻¹ᵁ (I.subschemeι ≫ s).smoothLocus
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    trivial

/-! ### Linear conditions on the coefficients -/

section Linear

variable {k : Type u} [Field k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) {V : X.Opens} {N : ℕ}

private theorem sysFun_add (g : Fin (N + 1) → Γ(X, V)) (c c' : Fin (N + 1) → k) :
    sysFun s g (c + c') = sysFun s g c + sysFun s g c' := by
  simp only [sysFun, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem sysFun_smul (g : Fin (N + 1) → Γ(X, V)) (t : k) (c : Fin (N + 1) → k) :
    sysFun s g (t • c) = baseRing s V t * sysFun s g c := by
  rw [sysFun, sysFun, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

private theorem sysFun_single (g : Fin (N + 1) → Γ(X, V)) (j : Fin (N + 1)) :
    sysFun s g (Pi.single j 1) = g j := by
  rw [sysFun, Finset.sum_eq_single j (fun b _ hb => by
    rw [Pi.single_eq_of_ne hb, map_zero, zero_mul]) (fun h => absurd (Finset.mem_univ j) h),
    Pi.single_eq_same, map_one, one_mul]

/-- The germ of a member of the system is unchanged by restricting the system to a smaller
open. -/
private theorem germ_sysFun_res (g : Fin (N + 1) → Γ(X, V)) {W : X.Opens} (hWV : W ≤ V)
    (c : Fin (N + 1) → k) {x : X} (hx : x ∈ W) :
    (X.presheaf.germ W x hx).hom (sysFun s (fun j => X.presheaf.map (homOfLE hWV).op (g j)) c) =
      (X.presheaf.germ V x (hWV hx)).hom (sysFun s g c) := by
  simp only [germ_sysFun, X.presheaf.germ_res_apply]

/-- If some function of the system has germ outside an ideal `J` of the local ring at `x`, then
the general member of the system has germ outside `J`: avoiding `J` is the complement of a
proper linear condition on the coefficients. -/
private theorem exists_poly_germ_sysFun_notMem (g : Fin (N + 1) → Γ(X, V)) {x : X}
    (hx : x ∈ V) (J : Ideal (X.presheaf.stalk x))
    (hJ : ∃ j, (X.presheaf.germ V x hx).hom (g j) ∉ J) :
    ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧
      ∀ c, MvPolynomial.eval c ℓ ≠ 0 → (X.presheaf.germ V x hx).hom (sysFun s g c) ∉ J := by
  obtain ⟨j₀, hj₀⟩ := hJ
  let K : Submodule k (Fin (N + 1) → k) :=
    { carrier := {c | (X.presheaf.germ V x hx).hom (sysFun s g c) ∈ J}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, sysFun_add, map_add] at ha hb ⊢
        exact J.add_mem ha hb
      zero_mem' := by
        have : sysFun s g 0 = 0 := by simp [sysFun]
        simp [this]
      smul_mem' := fun t a ha => by
        simp only [Set.mem_setOf_eq, sysFun_smul, map_mul] at ha ⊢
        exact J.mul_mem_left _ ha }
  have hnot : Pi.single j₀ (1 : k) ∉ K := by
    change (X.presheaf.germ V x hx).hom (sysFun s g (Pi.single j₀ 1)) ∉ J
    rwa [sysFun_single]
  obtain ⟨ψ, hψc, hψK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  set ℓ : MvPolynomial (Fin (N + 1)) k :=
    ∑ j, MvPolynomial.C (ψ (Pi.single j 1)) * MvPolynomial.X j
  have hev : ∀ c, MvPolynomial.eval c ℓ = ψ c := by
    intro c
    conv_rhs => rw [pi_eq_sum_univ c]
    simp only [ℓ, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_smul,
      smul_eq_mul, mul_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  refine ⟨ℓ, fun h => hψc (by rw [← hev, h, map_zero]), fun c hc hcK => hc ?_⟩
  rw [hev]
  have : ψ c ∈ K.map ψ := ⟨c, hcK, rfl⟩
  rwa [hψK] at this

/-- A member of the system has germ in an ideal `J` when every function of the system does. -/
private theorem germ_sysFun_mem (g : Fin (N + 1) → Γ(X, V)) (c : Fin (N + 1) → k) {x : X}
    (hx : x ∈ V) (J : Ideal (X.presheaf.stalk x))
    (hJ : ∀ j, (X.presheaf.germ V x hx).hom (g j) ∈ J) :
    (X.presheaf.germ V x hx).hom (sysFun s g c) ∈ J := by
  rw [germ_sysFun]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hJ j)

/-- If at every point of `V` off `T` some function of the system has a unit germ, then at a given
point the general member of the system has a unit germ, if that point is in `V` and off `T`. -/
private theorem exists_poly_isUnit_germ_sysFun (g : Fin (N + 1) → Γ(X, V)) (T : Set X)
    (hg : ∀ x (hx : x ∈ V), x ∉ T → ∃ j, IsUnit ((X.presheaf.germ V x hx).hom (g j))) (y : X) :
    ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧
      ∀ c, MvPolynomial.eval c ℓ ≠ 0 → ∀ hy : y ∈ V, y ∉ T →
        IsUnit ((X.presheaf.germ V y hy).hom (sysFun s g c)) := by
  by_cases h : y ∈ V ∧ y ∉ T
  · obtain ⟨j, hj⟩ := hg y h.1 h.2
    obtain ⟨ℓ, hℓ, hℓc⟩ := exists_poly_germ_sysFun_notMem s g h.1 (IsLocalRing.maximalIdeal _)
      ⟨j, IsLocalRing.notMem_maximalIdeal.mpr hj⟩
    exact ⟨ℓ, hℓ, fun c hc _ _ => IsLocalRing.notMem_maximalIdeal.mp (hℓc c hc)⟩
  · exact ⟨1, one_ne_zero, fun c _ hy hyT => absurd ⟨hy, hyT⟩ h⟩

/-- If along every prime divisor in `T` with generic point in `V` some function of the system
does not vanish to order two, then along a given prime divisor neither does the general member. -/
private theorem exists_poly_germ_sysFun_notMem_sq (g : Fin (N + 1) → Γ(X, V)) (T : Set X)
    (hg : ∀ E : MMP.Mori.PrimeDivisor X, E.support ⊆ T → ∀ h : E.genericPoint ∈ V, ∃ j,
      (X.presheaf.germ V _ h).hom (g j) ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)) ^ 2)
    (E : MMP.Mori.PrimeDivisor X) :
    ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧
      ∀ c, MvPolynomial.eval c ℓ ≠ 0 → E.support ⊆ T → ∀ h : E.genericPoint ∈ V,
        (X.presheaf.germ V _ h).hom (sysFun s g c) ∉
          (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)) ^ 2 := by
  by_cases h : E.support ⊆ T ∧ E.genericPoint ∈ V
  · obtain ⟨ℓ, hℓ, hℓc⟩ := exists_poly_germ_sysFun_notMem s g h.2 _ (hg E h.1 h.2)
    exact ⟨ℓ, hℓ, fun c hc _ _ => hℓc c hc⟩
  · exact ⟨1, one_ne_zero, fun c _ hE hξ => absurd ⟨hE, hξ⟩ h⟩

end Linear

/-- A function whose germ at `x` is a unit has a unit germ at every generization of `x`. -/
private theorem isUnit_germ_of_specializes {X : Scheme.{u}} {V : X.Opens} (g : Γ(X, V))
    {x y : X} (hyx : y ⤳ x) (hx : x ∈ V) (hu : IsUnit ((X.presheaf.germ V x hx).hom g)) :
    IsUnit ((X.presheaf.germ V y (hyx.mem_open V.isOpen hx)).hom g) := by
  rw [← X.presheaf.germ_stalkSpecializes_apply hx hyx g]
  exact hu.map _

/-- A function whose germ at a generization of `x` is nonzero has nonzero germ at `x`. -/
private theorem germ_ne_zero_of_specializes {X : Scheme.{u}} {V : X.Opens} (g : Γ(X, V))
    {x y : X} (hyx : y ⤳ x) (hx : x ∈ V)
    (h0 : (X.presheaf.germ V y (hyx.mem_open V.isOpen hx)).hom g ≠ 0) :
    (X.presheaf.germ V x hx).hom g ≠ 0 := by
  intro h
  rw [← X.presheaf.germ_stalkSpecializes_apply hx hyx g, h, map_zero] at h0
  exact h0 rfl

/-! ### The general member of a system of local equations -/

/-- Finitely many conditions, each holding off the zero locus of a nonzero polynomial, hold
together off the zero locus of a nonzero polynomial. -/
private theorem exists_poly_forall_mem {k : Type u} [Field k] {N : ℕ} {α : Type*} (s : Finset α)
    {p : α → (Fin (N + 1) → k) → Prop}
    (h : ∀ a, ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧ ∀ c, MvPolynomial.eval c ℓ ≠ 0 → p a c) :
    ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧
      ∀ c, MvPolynomial.eval c ℓ ≠ 0 → ∀ a ∈ s, p a c := by
  choose ℓ hℓ0 hℓ using h
  refine ⟨∏ a ∈ s, ℓ a, Finset.prod_ne_zero_iff.mpr fun a _ => hℓ0 a, fun c hc a ha => hℓ a c ?_⟩
  rw [map_prod] at hc
  exact Finset.prod_ne_zero_iff.mp hc a ha

/-- Two conditions, each holding off the zero locus of a nonzero polynomial, hold together off
the zero locus of a nonzero polynomial. -/
private theorem exists_poly_and {k : Type u} [Field k] {N : ℕ} {p q : (Fin (N + 1) → k) → Prop}
    (hp : ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧ ∀ c, MvPolynomial.eval c ℓ ≠ 0 → p c)
    (hq : ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧ ∀ c, MvPolynomial.eval c ℓ ≠ 0 → q c) :
    ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧ ∀ c, MvPolynomial.eval c ℓ ≠ 0 → p c ∧ q c := by
  obtain ⟨ℓ₁, h₁, hp⟩ := hp
  obtain ⟨ℓ₂, h₂, hq⟩ := hq
  refine ⟨ℓ₁ * ℓ₂, mul_ne_zero h₁ h₂, fun c hc => ?_⟩
  rw [map_mul] at hc
  exact ⟨hp c (left_ne_zero_of_mul hc), hq c (right_ne_zero_of_mul hc)⟩

/-- A nonzero polynomial over an infinite domain does not vanish at some point. -/
private theorem exists_eval_ne_zero {R σ : Type*} [CommRing R] [IsDomain R] [Infinite R]
    {ℓ : MvPolynomial σ R} (hℓ : ℓ ≠ 0) : ∃ c, MvPolynomial.eval c ℓ ≠ 0 := by
  by_contra! h
  exact hℓ (MvPolynomial.funext fun c => by simpa using h c)

/-- **Bertini's theorem for reducedness, at the local rings of a smaller open.** The general
member of a system on `V` without common zero on `W ≤ V` generates a radical ideal of every
local ring of `W`. -/
private theorem exists_poly_isRadical_of_le {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [IsReduced X]
    {V W : X.Opens} (hWV : W ≤ V) [QuasiCompact (W.ι ≫ s)] {N : ℕ} (g : Fin (N + 1) → Γ(X, V))
    (hgen : ∀ x (hx : x ∈ W), ∃ j, IsUnit ((X.presheaf.germ V x (hWV hx)).hom (g j))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 →
      ∀ x (hx : x ∈ W),
        (Ideal.span {(X.presheaf.germ V x (hWV hx)).hom (sysFun s g c)}).IsRadical := by
  obtain ⟨Q, hQ, hQc⟩ := exists_poly_isRadical s W
    (fun j => X.presheaf.map (homOfLE hWV).op (g j)) fun x hx => by
      obtain ⟨j, hj⟩ := hgen x hx
      exact ⟨j, by rwa [X.presheaf.germ_res_apply]⟩
  refine ⟨Q, hQ, fun c hc x hx => ?_⟩
  rw [← germ_sysFun_res s g hWV c hx]
  exact hQc c hc x hx

/-- **Bertini's theorem for smoothness and reducedness, on a smaller open.** On an open `W ≤ V`
of the smooth locus, the general member of a system on `V` without common zero on `W` has smooth
and reduced zero scheme on `W`, if `W` is nonempty. -/
private theorem exists_poly_smooth_isReduced {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k s]
    [IsLocallyNoetherian X] {V W : X.Opens} (hWV : W ≤ V) [QuasiCompact (W.ι ≫ s)]
    (hW : W ≤ s.smoothLocus) {N : ℕ} (g : Fin (N + 1) → Γ(X, V))
    (hgen : ∀ x (hx : x ∈ W), ∃ j, IsUnit ((X.presheaf.germ V x (hWV hx)).hom (g j))) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 → Nonempty W →
      letI : W.toScheme.Over (Spec (.of k)) := ⟨W.ι ≫ s⟩
      Smooth ((zeroScheme W.toScheme (Stacks.Ample.unitModule W.toScheme)
        (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule W.toScheme)
          (fun j => W.topIso.inv (X.presheaf.map (homOfLE hWV).op (g j))) c)).subschemeι ≫
            W.ι ≫ s) ∧
      IsReduced (zeroScheme W.toScheme (Stacks.Ample.unitModule W.toScheme)
        (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule W.toScheme)
          (fun j => W.topIso.inv (X.presheaf.map (homOfLE hWV).op (g j))) c)).subscheme := by
  have hgen' : ∀ x (hx : x ∈ W), ∃ j,
      IsUnit ((X.presheaf.germ W x hx).hom (X.presheaf.map (homOfLE hWV).op (g j))) := by
    intro x hx
    obtain ⟨j, hj⟩ := hgen x hx
    exact ⟨j, by rwa [X.presheaf.germ_res_apply]⟩
  by_cases hne : Nonempty W
  · obtain ⟨Q, hQ, hQc⟩ := exists_poly_and (exists_poly_smooth s W hW _ hgen')
      (exists_poly_isReduced s W _ hgen')
    exact ⟨Q, hQ, fun c hc _ => hQc c hc⟩
  · exact ⟨1, one_ne_zero, fun c _ h => absurd h hne⟩

/-- Members of systems agreeing up to a common unit on overlaps have associated germs. -/
private theorem associated_germ_sysFun {k : Type u} [Field k] {Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) {ι : Type*} {U : ι → Z.Opens} {N : ℕ}
    (f : ∀ i, Fin (N + 1) → Γ(Z, U i))
    (hcompat : ∀ i i' (x : Z) (hi : x ∈ U i) (hi' : x ∈ U i'), ∃ w : (Z.presheaf.stalk x)ˣ,
      ∀ j, (Z.presheaf.germ (U i) x hi).hom (f i j) =
        w * (Z.presheaf.germ (U i') x hi').hom (f i' j))
    (c : Fin (N + 1) → k) (i i' : ι) (x : Z) (hi : x ∈ U i) (hi' : x ∈ U i') :
    Associated ((Z.presheaf.germ (U i) x hi).hom (sysFun sZ (f i) c))
      ((Z.presheaf.germ (U i') x hi').hom (sysFun sZ (f i') c)) := by
  obtain ⟨w, hw⟩ := hcompat i i' x hi hi'
  have e : (Z.presheaf.germ (U i) x hi).hom (sysFun sZ (f i) c) =
      w * (Z.presheaf.germ (U i') x hi').hom (sysFun sZ (f i') c) := by
    simp only [germ_sysFun, hw, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact ⟨w⁻¹, by rw [e, mul_right_comm, Units.mul_inv, one_mul]⟩

/-- **The divisor of local equations which are units at the generic point.** On a normal integral
scheme, functions `hᵢ` on an open cover, units at the generic point and with associated germs on
overlaps, are the local equations of a Cartier divisor `D` whose support is where the `hᵢ` are
not units, with coefficient one along a prime divisor where `hᵢ` is radical or of order one. -/
private theorem exists_divisor_of_isUnit_germ_genericPoint {Z : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] {ι : Type*} (U : ι → Z.Opens)
    (hU : ∀ x, ∃ i, x ∈ U i) (h : ∀ i, Γ(Z, U i))
    (hηu : ∀ i (hη : genericPoint Z ∈ U i), IsUnit ((Z.presheaf.germ (U i) _ hη).hom (h i)))
    (hassoc : ∀ i i' (x : Z) (hi : x ∈ U i) (hi' : x ∈ U i'),
      Associated ((Z.presheaf.germ (U i) x hi).hom (h i))
        ((Z.presheaf.germ (U i') x hi').hom (h i'))) :
    ∃ D : Divisor Z, D.IsCartier ∧
      (∀ i x (hx : x ∈ U i), x ∈ D.supp ↔ ¬ IsUnit ((Z.presheaf.germ (U i) x hx).hom (h i))) ∧
      (∀ i (E : MMP.Mori.PrimeDivisor Z) (hE : E.genericPoint ∈ U i),
        IsUnit ((Z.presheaf.germ (U i) _ hE).hom (h i)) → D.coeff E = 0) ∧
      ∀ i (E : MMP.Mori.PrimeDivisor Z) (hE : E.genericPoint ∈ U i),
        ¬ IsUnit ((Z.presheaf.germ (U i) _ hE).hom (h i)) →
        (Ideal.span {(Z.presheaf.germ (U i) _ hE).hom (h i)}).IsRadical ∨
          (Z.presheaf.germ (U i) _ hE).hom (h i) ∉
            (IsLocalRing.maximalIdeal (Z.presheaf.stalk E.genericPoint)) ^ 2 →
        D.coeff E = 1 := by
  have hne : ∀ i (Y : irreducibleComponents Z) (hY : MMP.Mori.componentGenericPoint Z Y ∈ U i),
      (Z.presheaf.germ (U i) _ hY).hom (h i) ≠ 0 := by
    intro i Y
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint Y]
    exact fun hY => (hηu i hY).ne_zero
  obtain ⟨D, hD⟩ :=
    MMP.Threefold.Resolution.exists_divisor_isLocalEquation_sectionUnit U hU h hne hassoc
  have hcoeff : ∀ i (E : MMP.Mori.PrimeDivisor Z) (hE : E.genericPoint ∈ U i),
      D.coeff E = E.ord (MMP.Threefold.Resolution.sectionUnit (h i) (hne i)) :=
    fun i E hE => hD i E ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, hE⟩
  refine ⟨D, fun x => ?_, fun i x hx => ?_, fun i E hE hu => ?_, fun i E hE hnu hor => ?_⟩
  · obtain ⟨i, hi⟩ := hU x
    exact ⟨U i, hi, _, hD i⟩
  · rw [DivisorWithCoeffs.mem_supp_iff]
    constructor
    · rintro ⟨E, hE0, hxE⟩ hu
      have hsp := genericPoint_specializes E hxE
      have hEU := hsp.mem_open (U i).isOpen hx
      apply hE0
      rw [hcoeff i E hEU]
      exact MMP.Threefold.Resolution.ord_sectionUnit_eq_zero _ _ E hEU
        (isUnit_germ_of_specializes (h i) hsp hx hu)
    · intro hnu
      have hsp : genericPoint Z ⤳ x := (genericPoint_spec Z).specializes (Set.mem_univ x)
      have h0 := germ_ne_zero_of_specializes (h i) hsp hx (hηu i _).ne_zero
      obtain ⟨P, hxP, hPU, hPnu⟩ := exists_primeDivisor_not_isUnit_germ (h i) hx h0 hnu
      refine ⟨P, ?_, hxP⟩
      rw [hcoeff i P hPU]
      have := MMP.Threefold.Resolution.one_le_ord_sectionUnit (h i) (hne i) P hPU hPnu
      omega
  · rw [hcoeff i E hE]
    exact MMP.Threefold.Resolution.ord_sectionUnit_eq_zero _ _ E hE hu
  · rw [hcoeff i E hE]
    haveI := E.isDiscreteValuationRing_localRing
    exact E.ord_eq_one_of_irreducible (irreducible_of_isRadical_or_notMem_sq
      (MMP.Threefold.Resolution.germ_genericPoint_ne_zero (h i) (hne i) E hE) hnu hor)
      (MMP.Threefold.Resolution.toComponent_germ_eq_sectionUnit _ _ E hE)

/-- If the zero scheme on an open `W ≤ V` of a member of a system on `V` is smooth and reduced,
and its support is `W ∩ D.supp`, then every point of `W ∩ D.supp` is a smooth point of the
reduced structure on `D.supp`. -/
private theorem exists_mem_smoothLocus_suppIdeal {k : Type u} [Field k] {Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (D : Divisor Z)
    [LocallyOfFinitePresentation (D.suppIdeal.subschemeι ≫ sZ)]
    {V W : Z.Opens} (hWV : W ≤ V) {N : ℕ} (g : Fin (N + 1) → Γ(Z, V)) (c : Fin (N + 1) → k)
    (hsupp : ∀ y (hy : y ∈ W),
      y ∈ D.supp ↔ ¬ IsUnit ((Z.presheaf.germ V y (hWV hy)).hom (sysFun sZ g c)))
    (h : letI : W.toScheme.Over (Spec (.of k)) := ⟨W.ι ≫ sZ⟩
      Smooth ((zeroScheme W.toScheme (Stacks.Ample.unitModule W.toScheme)
        (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule W.toScheme)
          (fun j => W.topIso.inv (Z.presheaf.map (homOfLE hWV).op (g j))) c)).subschemeι ≫
            W.ι ≫ sZ) ∧
      IsReduced (zeroScheme W.toScheme (Stacks.Ample.unitModule W.toScheme)
        (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule W.toScheme)
          (fun j => W.topIso.inv (Z.presheaf.map (homOfLE hWV).op (g j))) c)).subscheme)
    {z : Z} (hzW : z ∈ W) (hz : z ∈ (D.supp : Set Z)) :
    ∃ y, D.suppIdeal.subschemeι y = z ∧ y ∈ (D.suppIdeal.subschemeι ≫ sZ).smoothLocus := by
  letI : W.toScheme.Over (Spec (.of k)) := ⟨W.ι ≫ sZ⟩
  obtain ⟨hsm, hred⟩ := h
  set Zs := zeroScheme W.toScheme (Stacks.Ample.unitModule W.toScheme)
    (MMP.Threefold.Bridges.systemSection (L := Stacks.Ample.unitModule W.toScheme)
      (fun j => W.topIso.inv (Z.presheaf.map (homOfLE hWV).op (g j))) c)
  haveI : IsReduced Zs.subscheme := hred
  have hZs : Zs.support = D.supp.preimage W.ι.continuous := by
    ext y
    refine (mem_support_zeroScheme_systemSection_iff sZ W _ c y).trans ?_
    rw [germ_sysFun_res]
    change _ ↔ y.1 ∈ D.supp
    rw [hsupp y.1 y.2]
  have heq : D.suppIdeal.comap W.ι = Zs := by
    rw [DivisorWithCoeffs.suppIdeal, comap_vanishingIdeal_of_isOpenImmersion]
    exact (Zs.eq_vanishingIdeal_of_isReduced_subscheme _ hZs).symm
  refine exists_mem_smoothLocus_of_smooth_comap sZ D.suppIdeal W (by rwa [heq]) hzW ?_
  rwa [← SetLike.mem_coe, DivisorWithCoeffs.coe_support_suppIdeal]

/-- **The divisor of a general member of a system of local equations.** Let `Z` be a normal
quasi-projective variety over an algebraically closed field of characteristic zero, `T₀ ⊊ Z`
closed and `S` a finite set of points off `T₀`. Suppose given a finite open cover `Uᵢ` of `Z` and
on each `Uᵢ` functions `fᵢ₀, …, f_{iN}` which agree up to a common unit on overlaps (they are the
local expressions of sections of one invertible sheaf), vanish along `T₀`, have no common zero
off `T₀`, and do not all vanish to order two along any prime divisor contained in `T₀`. Then the
divisor of a general member `∑ⱼ cⱼ fᵢⱼ` has all the properties of
`exists_isCartier_reduced_supp_superset`. -/
private theorem exists_of_chartSystem {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sZ]
    [IsLocallyNoetherian Z] [IsNormal Z] (T₀ : Set Z) (hT₀ : IsClosed T₀) (hT₀' : T₀ ≠ Set.univ)
    (S : Set Z) (hS : S.Finite) (hST : Disjoint S T₀)
    {ι : Type u} [Finite ι] (U : ι → Z.Opens) (hU : ∀ x, ∃ i, x ∈ U i) {N : ℕ}
    (f : ∀ i, Fin (N + 1) → Γ(Z, U i))
    (hcompat : ∀ i i' (x : Z) (hi : x ∈ U i) (hi' : x ∈ U i'), ∃ w : (Z.presheaf.stalk x)ˣ,
      ∀ j, (Z.presheaf.germ (U i) x hi).hom (f i j) =
        w * (Z.presheaf.germ (U i') x hi').hom (f i' j))
    (H1 : ∀ i x (hx : x ∈ U i), x ∈ T₀ → ∀ j,
      (Z.presheaf.germ (U i) x hx).hom (f i j) ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk x))
    (H2 : ∀ i x (hx : x ∈ U i), x ∉ T₀ → ∃ j, IsUnit ((Z.presheaf.germ (U i) x hx).hom (f i j)))
    (H3 : ∀ E : MMP.Mori.PrimeDivisor Z, E.support ⊆ T₀ → ∀ i (h : E.genericPoint ∈ U i), ∃ j,
      (Z.presheaf.germ (U i) _ h).hom (f i j) ∉
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk E.genericPoint)) ^ 2) :
    ∃ H' : Divisor Z, H'.IsCartier ∧ (∀ P, H'.coeff P = 0 ∨ H'.coeff P = 1) ∧
      T₀ ⊆ H'.supp ∧ Disjoint S H'.supp ∧
      (∀ z ∈ (H'.supp : Set Z), z ∉ T₀ → z ∈ sZ.smoothLocus →
        ∃ y, H'.suppIdeal.subschemeι y = z ∧
          y ∈ (H'.suppIdeal.subschemeι ≫ sZ).smoothLocus) ∧
      ∀ P : MMP.Mori.PrimeDivisor Z, P.support ⊆ T₀ → H'.coeff P = 1 := by
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsNoetherian Z := ⟨⟩
  haveI : Infinite k := IsAlgClosed.instInfinite
  haveI : Fintype ι := Fintype.ofFinite ι
  set η := genericPoint Z
  have hηT : η ∉ T₀ := genericPoint_notMem hT₀ hT₀'
  set Tc : Z.Opens := ⟨T₀ᶜ, hT₀.isOpen_compl⟩
  have hWU : ∀ i, U i ⊓ Tc ⊓ sZ.smoothLocus ≤ U i := fun i => inf_le_left.trans inf_le_left
  have hS' : (insert η S).Finite := hS.insert η
  have hEfin := finite_setOf_genericPoint_mem_of_ne_univ hT₀ hT₀'
  obtain ⟨Q, hQ, hQc⟩ := exists_poly_forall_mem Finset.univ fun i => exists_poly_and
    (exists_poly_and (exists_poly_and
      (exists_poly_forall_mem hS'.toFinset (exists_poly_isUnit_germ_sysFun sZ (f i) T₀ (H2 i)))
      (exists_poly_forall_mem hEfin.toFinset
        (exists_poly_germ_sysFun_notMem_sq sZ (f i) T₀ fun E hE => H3 E hE i)))
      (exists_poly_isRadical_of_le sZ (inf_le_left : U i ⊓ Tc ≤ U i) (f i)
        fun x hx => H2 i x hx.1 hx.2))
    (exists_poly_smooth_isReduced sZ (hWU i) inf_le_right (f i) fun x hx => H2 i x hx.1.1 hx.1.2)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero hQ
  have hc' := fun i => hQc c hc i (Finset.mem_univ i)
  have hnuT : ∀ i x (hx : x ∈ U i), x ∈ T₀ →
      ¬ IsUnit ((Z.presheaf.germ (U i) x hx).hom (sysFun sZ (f i) c)) := fun i x hx hxT =>
    (IsLocalRing.mem_maximalIdeal _).mp (germ_sysFun_mem sZ (f i) c hx _ (H1 i x hx hxT))
  obtain ⟨D, hDc, hsupp, hD0, hD1⟩ := exists_divisor_of_isUnit_germ_genericPoint U hU
    (fun i => sysFun sZ (f i) c)
    (fun i hηU => (hc' i).1.1.1 η (hS'.mem_toFinset.mpr (Set.mem_insert _ _)) hηU hηT)
    (associated_germ_sysFun sZ f hcompat c)
  refine ⟨D, hDc, fun E => ?_, fun x hx => ?_, Set.disjoint_left.mpr fun y hyS hysupp => ?_,
    fun z hz hzT hzs => ?_, fun P hP => ?_⟩
  · obtain ⟨i, hi⟩ := hU E.genericPoint
    by_cases hu : IsUnit ((Z.presheaf.germ (U i) _ hi).hom (sysFun sZ (f i) c))
    · exact Or.inl (hD0 i E hi hu)
    refine Or.inr (hD1 i E hi hu ?_)
    by_cases hT : E.genericPoint ∈ T₀
    · exact Or.inr ((hc' i).1.1.2 E (hEfin.mem_toFinset.mpr hT)
        (support_subset_of_genericPoint_mem E hT₀ hT) hi)
    · exact Or.inl ((hc' i).1.2 _ ⟨hi, hT⟩)
  · obtain ⟨i, hi⟩ := hU x
    exact (hsupp i x hi).mpr (hnuT i x hi hx)
  · obtain ⟨i, hi⟩ := hU y
    exact (hsupp i y hi).mp hysupp ((hc' i).1.1.1 y
      (hS'.mem_toFinset.mpr (Set.mem_insert_of_mem _ hyS)) hi (Set.disjoint_left.mp hST hyS))
  · obtain ⟨i, hi⟩ := hU z
    have hzW : z ∈ U i ⊓ Tc ⊓ sZ.smoothLocus := ⟨⟨hi, hzT⟩, hzs⟩
    exact exists_mem_smoothLocus_suppIdeal sZ D (hWU i) (f i) c
      (fun y hy => hsupp i y (hWU i hy)) ((hc' i).2 ⟨⟨z, hzW⟩⟩) hzW hz
  · have hT : P.genericPoint ∈ T₀ := hP (MMP.Flips.primeDivisor_genericPoint_mem_support P)
    obtain ⟨i, hi⟩ := hU P.genericPoint
    exact hD1 i P hi (hnuT i _ hi hT) (Or.inr ((hc' i).1.1.2 P (hEfin.mem_toFinset.mpr hT) hP hi))

/-! ### Local equations from global sections of an invertible module -/

open Stacks.SectionExtension in
/-- **The general member of a linear system of an invertible module.** Let `M` be an invertible
module on `Z`, `eᵢ` finitely many global sections whose nonvanishing loci cover `Z`, and
`σ₀, …, σ_N` global sections which vanish along `T₀`, have no common zero off `T₀`, and such that
along every prime divisor `E ⊆ T₀` some `σⱼ` is, near the generic point of `E`, a function of
order one times a nonvanishing section. Then the divisor of a general member of the span of the
`σⱼ` has all the properties of `exists_isCartier_reduced_supp_superset`. -/
private theorem exists_isCartier_reduced_supp_superset_of_sections
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sZ]
    [IsLocallyNoetherian Z] [IsNormal Z] (T₀ : Set Z) (hT₀ : IsClosed T₀) (hT₀' : T₀ ≠ Set.univ)
    (S : Set Z) (hS : S.Finite) (hST : Disjoint S T₀)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M] {ι : Type u} [Finite ι]
    (e : ι → Γ(M, ⊤)) (he : ∀ x, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus M (e i)) {N : ℕ}
    (σ : Fin (N + 1) → Γ(M, ⊤))
    (h1 : ∀ j, ∀ x ∈ T₀, x ∉ Stacks.Ample.nonvanishingLocus M (σ j))
    (h2 : ∀ x ∉ T₀, ∃ j, x ∈ Stacks.Ample.nonvanishingLocus M (σ j))
    (h3 : ∀ E : MMP.Mori.PrimeDivisor Z, E.support ⊆ T₀ → ∃ (j : Fin (N + 1)) (W : Z.Opens)
      (hW : E.genericPoint ∈ W) (g : Γ(Z, W)) (ε : Γ(M, ⊤)),
      W ≤ Stacks.NonvanishingOpen.nonvanishingOpen Z M ε ∧ resTop W (σ j) = g • resTop W ε ∧
      (Z.presheaf.germ W _ hW).hom g ∉
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk E.genericPoint)) ^ 2) :
    ∃ H' : Divisor Z, H'.IsCartier ∧ (∀ P, H'.coeff P = 0 ∨ H'.coeff P = 1) ∧
      T₀ ⊆ H'.supp ∧ Disjoint S H'.supp ∧
      (∀ z ∈ (H'.supp : Set Z), z ∉ T₀ → z ∈ sZ.smoothLocus →
        ∃ y, H'.suppIdeal.subschemeι y = z ∧
          y ∈ (H'.suppIdeal.subschemeι ≫ sZ).smoothLocus) ∧
      ∀ P : MMP.Mori.PrimeDivisor Z, P.support ⊆ T₀ → H'.coeff P = 1 := by
  set U : ι → Z.Opens := fun i => Stacks.NonvanishingOpen.nonvanishingOpen Z M (e i) with hUdef
  have hU : ∀ x, ∃ i, x ∈ U i := fun x => by
    obtain ⟨i, hi⟩ := he x
    exact ⟨i, by rw [hUdef, Stacks.NonvanishingOpen.mem_nonvanishingOpen]; exact hi⟩
  choose f hf using fun i j => exists_resTop_eq_smul M (e i) (σ j) (le_refl (U i))
  -- the transition function between two charts, on their overlap
  have htrans : ∀ i i' (x : Z) (hx : x ∈ U i ⊓ U i'), ∃ v : Γ(Z, U i ⊓ U i'),
      IsUnit ((Z.presheaf.germ _ x hx).hom v) ∧
      ∀ j, Z.presheaf.map (homOfLE inf_le_left).op (f i j) =
        Z.presheaf.map (homOfLE inf_le_right).op (f i' j) * v := by
    intro i i' x hx
    obtain ⟨v, hv⟩ := exists_resTop_eq_smul M (e i) (e i') (inf_le_left : U i ⊓ U i' ≤ U i)
    refine ⟨v, ?_, fun j => ?_⟩
    · have := mem_nonvanishingLocus_iff_isUnit_of_res_eq (e i) (e i')
        (inf_le_left : U i ⊓ U i' ≤ U i) hv hx
      rw [← this, ← Stacks.NonvanishingOpen.mem_nonvanishingOpen]
      exact hx.2
    · refine smul_resTop_injective M (e i) (inf_le_left : U i ⊓ U i' ≤ U i) ?_
      rw [← resTop_eq_smul_of_le M inf_le_left _ (hf i j), mul_smul, ← hv,
        ← resTop_eq_smul_of_le M inf_le_right _ (hf i' j)]
  refine exists_of_chartSystem sZ T₀ hT₀ hT₀' S hS hST U hU f ?_ ?_ ?_ ?_
  · intro i i' x hi hi'
    have hx : x ∈ U i ⊓ U i' := ⟨hi, hi'⟩
    obtain ⟨v, hvu, hv⟩ := htrans i i' x hx
    refine ⟨hvu.unit, fun j => ?_⟩
    have := congrArg (Z.presheaf.germ _ x hx).hom (hv j)
    rw [Z.presheaf.germ_res_apply, map_mul, Z.presheaf.germ_res_apply] at this
    rw [this, IsUnit.unit_spec, mul_comm]
  · intro i x hx hxT j
    by_contra hmem
    have := (mem_nonvanishingLocus_iff_isUnit_of_res_eq (e i) (σ j) (le_refl (U i)) (hf i j)
      hx).mpr (IsLocalRing.notMem_maximalIdeal.mp hmem)
    exact h1 j x hxT this
  · intro i x hx hxT
    obtain ⟨j, hj⟩ := h2 x hxT
    exact ⟨j, (mem_nonvanishingLocus_iff_isUnit_of_res_eq (e i) (σ j) (le_refl (U i)) (hf i j)
      hx).mp hj⟩
  · intro E hE i hEi
    obtain ⟨j, W, hW, g, ε, hWε, hrel, hg⟩ := h3 E hE
    refine ⟨j, fun hmem => hg ?_⟩
    obtain ⟨v, hv⟩ := exists_resTop_eq_smul M (e i) ε (inf_le_right : W ⊓ U i ≤ U i)
    have hx : E.genericPoint ∈ W ⊓ U i := ⟨hW, hEi⟩
    have hvu : IsUnit ((Z.presheaf.germ _ _ hx).hom v) := by
      rw [← mem_nonvanishingLocus_iff_isUnit_of_res_eq (e i) ε inf_le_right hv hx,
        ← Stacks.NonvanishingOpen.mem_nonvanishingOpen]
      exact hWε hW
    have heq : Z.presheaf.map (homOfLE inf_le_right).op (f i j) =
        Z.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op g * v := by
      refine smul_resTop_injective M (e i) (inf_le_right : W ⊓ U i ≤ U i) ?_
      rw [← resTop_eq_smul_of_le M inf_le_right _ (hf i j), mul_smul, ← hv,
        ← resTop_eq_smul_of_le M inf_le_left _ hrel]
    have := congrArg (Z.presheaf.germ _ _ hx).hom heq
    rw [Z.presheaf.germ_res_apply, map_mul, Z.presheaf.germ_res_apply] at this
    rw [this] at hmem
    have := Ideal.mul_mem_right ((hvu.unit⁻¹ : (Z.presheaf.stalk E.genericPoint)ˣ) :
      Z.presheaf.stalk E.genericPoint) _ hmem
    rwa [mul_assoc, hvu.mul_val_inv, mul_one] at this

/-- `exists_isCartier_reduced_supp_superset_of_sections` for a family of sections indexed by any
finite type. -/
private theorem exists_isCartier_reduced_supp_superset_of_fintype_sections
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sZ]
    [IsLocallyNoetherian Z] [IsNormal Z] (T₀ : Set Z) (hT₀ : IsClosed T₀) (hT₀' : T₀ ≠ Set.univ)
    (S : Set Z) (hS : S.Finite) (hST : Disjoint S T₀)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M] {ι : Type u} [Finite ι]
    (e : ι → Γ(M, ⊤)) (he : ∀ x, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus M (e i))
    {κ : Type*} [Fintype κ] (σ : κ → Γ(M, ⊤))
    (h1 : ∀ j, ∀ x ∈ T₀, x ∉ Stacks.Ample.nonvanishingLocus M (σ j))
    (h2 : ∀ x ∉ T₀, ∃ j, x ∈ Stacks.Ample.nonvanishingLocus M (σ j))
    (h3 : ∀ E : MMP.Mori.PrimeDivisor Z, E.support ⊆ T₀ → ∃ (j : κ) (W : Z.Opens)
      (hW : E.genericPoint ∈ W) (g : Γ(Z, W)) (ε : Γ(M, ⊤)),
      W ≤ Stacks.NonvanishingOpen.nonvanishingOpen Z M ε ∧
      Stacks.SectionExtension.resTop W (σ j) = g • Stacks.SectionExtension.resTop W ε ∧
      (Z.presheaf.germ W _ hW).hom g ∉
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk E.genericPoint)) ^ 2) :
    ∃ H' : Divisor Z, H'.IsCartier ∧ (∀ P, H'.coeff P = 0 ∨ H'.coeff P = 1) ∧
      T₀ ⊆ H'.supp ∧ Disjoint S H'.supp ∧
      (∀ z ∈ (H'.supp : Set Z), z ∉ T₀ → z ∈ sZ.smoothLocus →
        ∃ y, H'.suppIdeal.subschemeι y = z ∧
          y ∈ (H'.suppIdeal.subschemeι ≫ sZ).smoothLocus) ∧
      ∀ P : MMP.Mori.PrimeDivisor Z, P.support ⊆ T₀ → H'.coeff P = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ T₀ := by
    by_contra h
    push Not at h
    exact hT₀' (Set.eq_univ_of_forall h)
  obtain ⟨j₀, -⟩ := h2 x hx
  haveI : Nonempty κ := ⟨j₀⟩
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := κ))
  let φ : Fin (N + 1) ≃ κ := (finCongr hN.symm).trans (Fintype.equivFin κ).symm
  refine exists_isCartier_reduced_supp_superset_of_sections sZ T₀ hT₀ hT₀' S hS hST M e he (σ ∘ φ)
    (fun j => h1 (φ j)) (fun x hx => ?_) (fun E hE => ?_)
  · obtain ⟨j, hj⟩ := h2 x hx
    exact ⟨φ.symm j, by simpa using hj⟩
  · obtain ⟨j, W, hW, g, ε, h⟩ := h3 E hE
    exact ⟨φ.symm j, W, hW, g, ε, by simpa using h⟩

/-! ### Near a prime divisor contained in `T₀` -/

/-- On an integral scheme, a point specializing to the generic point of a prime divisor is either
that generic point or the generic point of the scheme. -/
private theorem eq_genericPoint_of_specializes {X : Scheme.{u}} [IsIntegral X]
    (E : MMP.Mori.PrimeDivisor X) {ξ : X} (hξ : ξ ⤳ E.genericPoint) (hξη : ξ ≠ genericPoint X) :
    ξ = E.genericPoint := by
  by_contra hne
  have hηξ : genericPoint X ⤳ ξ := (genericPoint_spec X).specializes (Set.mem_univ ξ)
  have h1 : E.genericPoint < ξ := lt_of_le_not_ge hξ fun h =>
    hne (Specializes.antisymm hξ (show E.genericPoint ⤳ ξ from h)).eq
  have h2 : ξ < genericPoint X := lt_of_le_not_ge hηξ fun h =>
    hξη (Specializes.antisymm (show ξ ⤳ genericPoint X from h) hηξ).eq
  have hE := E.coheight_genericPoint
  have h3 := Order.coheight_strictAnti h1
    (lt_of_le_of_lt ((Order.coheight_anti h1.le).trans hE.le) ENat.one_lt_top)
  rw [hE, ENat.lt_one_iff_eq_zero, Order.coheight_eq_zero] at h3
  exact h2.not_isMax h3

/-- Near the generic point of a prime divisor `E`, a closed subset `T` of a Noetherian integral
scheme not containing the generic point is contained in `E`. -/
private theorem exists_open_inter_subset_support {X : Scheme.{u}} [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] {T : Set X} (hT : IsClosed T) (hηT : genericPoint X ∉ T)
    (E : MMP.Mori.PrimeDivisor X) :
    ∃ V : X.Opens, E.genericPoint ∈ V ∧ T ∩ V ⊆ E.support := by
  obtain ⟨S, hSf, hSirr, hTS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible ⟨T, hT⟩
  have hTS' : T = ⋃ t ∈ S, (t : Set X) := by
    have := congrArg (fun C : TopologicalSpace.Closeds X => (C : Set X)) hTS
    simp only [TopologicalSpace.Closeds.coe_mk, TopologicalSpace.Closeds.coe_sSup] at this
    rw [this, Set.sUnion_image, IsClosed.closure_eq]
    exact hSf.isClosed_biUnion fun t _ => t.isClosed
  set B : Set X := ⋃ t ∈ {t ∈ S | E.genericPoint ∉ t}, (t : Set X) with hBdef
  have hB : IsClosed B :=
    (hSf.subset (Set.sep_subset _ _)).isClosed_biUnion fun t _ => t.isClosed
  refine ⟨⟨Bᶜ, hB.isOpen_compl⟩, ?_, ?_⟩
  · intro hmem
    obtain ⟨t, ⟨-, hEt⟩, hEt'⟩ := Set.mem_iUnion₂.mp hmem
    exact hEt hEt'
  · rintro y ⟨hyT, hyB⟩
    have hy := hyT
    rw [hTS', Set.mem_iUnion₂] at hy
    obtain ⟨t, htS, hyt⟩ := hy
    have hηt : E.genericPoint ∈ t := by
      by_contra h
      exact hyB (Set.mem_biUnion (x := t) ⟨htS, h⟩ hyt)
    have hgen := (hSirr t htS).isGenericPoint_genericPoint_closure
    rw [t.isClosed.closure_eq] at hgen
    have htT : (t : Set X) ⊆ T := fun z hz => by
      rw [hTS', Set.mem_iUnion₂]; exact ⟨t, htS, hz⟩
    have hξ : (hSirr t htS).genericPoint = E.genericPoint := by
      refine eq_genericPoint_of_specializes E (hgen.specializes hηt) fun h => hηT ?_
      rw [← h]; exact htT hgen.mem
    have h' : y ∈ closure {(hSirr t htS).genericPoint} := by rw [hgen.def]; exact hyt
    rw [hξ] at h'
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact h'

/-- An irreducible element of a discrete valuation ring is not in the square of the maximal
ideal. -/
private theorem notMem_maximalIdeal_sq_of_irreducible {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) :
    ϖ ∉ (IsLocalRing.maximalIdeal R) ^ 2 := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  rintro ⟨c, hc⟩
  apply hϖ.not_isUnit
  have h1 : ϖ * (c * ϖ) = ϖ * 1 := by
    rw [mul_one, ← mul_assoc, mul_comm ϖ c, mul_assoc, ← sq]
    exact hc
  exact IsUnit.of_mul_eq_one c (by rw [mul_comm]; exact mul_left_cancel₀ hϖ.ne_zero h1)

/-- **A local equation of a prime divisor contained in `T₀`.** Near the generic point of a prime
divisor `E ⊆ T`, there is a function vanishing along `T` whose germ at the generic point of `E` is
a uniformizer. -/
private theorem exists_uniformizer_vanishing {X : Scheme.{u}} [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] [IsNormal X] {T : Set X} (hT : IsClosed T)
    (hηT : genericPoint X ∉ T) (E : MMP.Mori.PrimeDivisor X) :
    ∃ (V : X.Opens) (hV : E.genericPoint ∈ V) (h : Γ(X, V)),
      (∀ y (hy : y ∈ V), y ∈ T → ¬ IsUnit ((X.presheaf.germ V y hy).hom h)) ∧
      (X.presheaf.germ V _ hV).hom h ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk E.genericPoint)) ^ 2 := by
  haveI := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk E.genericPoint)
  obtain ⟨V₀, hV₀, h₀, hh₀⟩ := X.presheaf.exists_germ_eq ϖ
  obtain ⟨V₁, hV₁, hTV⟩ := exists_open_inter_subset_support hT hηT E
  have hV : E.genericPoint ∈ V₀ ⊓ V₁ := ⟨hV₀, hV₁⟩
  have hgerm : (X.presheaf.germ (V₀ ⊓ V₁) _ hV).hom
      (X.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op h₀) = ϖ := by
    rw [X.presheaf.germ_res_apply]; exact hh₀
  refine ⟨V₀ ⊓ V₁, hV, X.presheaf.map (homOfLE inf_le_left).op h₀, fun y hy hyT hu => ?_, ?_⟩
  · have hyE : y ∈ E.support := hTV ⟨hyT, hy.2⟩
    have := isUnit_germ_of_specializes _ (genericPoint_specializes E hyE) hy hu
    rw [hgerm] at this
    exact hϖ.not_isUnit this
  · rw [hgerm]
    exact notMem_maximalIdeal_sq_of_irreducible hϖ

/-! ### Global sections of the tensor powers of an ample module -/

section Sections

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

open Stacks.SectionExtension Stacks.AmpleFiniteAvoidance Stacks.GradedSections
  Stacks.SectionProduct

/-- **A function near a point, as a ratio of global sections.** For `L` ample and `h` a function
on an open `V ∋ x`, there are global sections `τ`, `ε` of one positive tensor power of `L` and an
open `x ∈ W ⊆ V ∩ X_ε` with `τ = h ε` on `W`, such that `τ` vanishes wherever `h` is not defined
or not a unit. -/
private theorem exists_ratio_section {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) {x : X} {V : X.Opens}
    (hxV : x ∈ V) (h : Γ(X, V)) :
    ∃ (q : ℕ) (τ ε : powSections L q) (W : X.Opens) (_ : x ∈ W) (hWV : W ≤ V),
      1 ≤ q ∧ W ≤ nvOpen L ε ∧
      resTop W (globalSection X _ τ) =
        X.presheaf.map (homOfLE hWV).op h • resTop W (globalSection X _ ε) ∧
      ∀ y ∈ nvLocus L τ, ∃ hyV : y ∈ V, IsUnit ((X.presheaf.germ V y hyV).hom h) := by
  obtain ⟨n, hn, s, hxs, hsV⟩ := isBasisNonvanishing_of_isAmple X L hL x V hxV
  obtain ⟨a₀, ha₀⟩ := exists_powSections_nvLocus_eq L n s
  obtain ⟨N, a, F, c, hN, -, ha, hcaff, hcover⟩ := exists_common_degree_affine_cover L hL hn a₀
  have hW : ∀ y, y ∈ nvOpen L a ↔ y ∈ Stacks.AmpleTheory.powNonvanishingOpen X L n s := by
    intro y
    rw [← SetLike.mem_coe, coe_nvOpen, ha, ha₀, ← SetLike.mem_coe,
      Stacks.AmpleTheory.coe_powNonvanishingOpen]
  have hWV : nvOpen L a ≤ V := fun y hy => hsV ((hW y).mp hy)
  obtain ⟨p, t, σ, hWσ, hrel⟩ := exists_ratio_of_affine_cover L a c (nvOpen L a) rfl _
    (fun _ => rfl) hcaff hcover (X.presheaf.map (homOfLE hWV).op h)
  set t₀ := (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm t
  set σ₀ := (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm σ
  have ht₀ : globalSection X _ t₀ = t :=
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).apply_symm_apply t
  have hσ₀ : globalSection X _ σ₀ = σ :=
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).apply_symm_apply σ
  refine ⟨N + p, mul a t₀, mul a σ₀, nvOpen L a, (hW x).mpr hxs, hWV, by omega, ?_, ?_, ?_⟩
  · intro y hy
    rw [← SetLike.mem_coe, coe_nvOpen, nvLocus_mul]
    refine ⟨by rw [← coe_nvOpen]; exact hy, ?_⟩
    rw [nvLocus, hσ₀, ← Stacks.NonvanishingOpen.mem_nonvanishingOpen]
    exact hWσ hy
  · rw [globalSection_mul, globalSection_mul, ht₀, hσ₀]
    exact resTop_app_of_res_eq _ _ t σ hrel
  · intro y hy
    rw [nvLocus_mul] at hy
    obtain ⟨hya, hyt⟩ := hy
    have hyW : y ∈ nvOpen L a := by rw [← SetLike.mem_coe, coe_nvOpen]; exact hya
    refine ⟨hWV hyW, ?_⟩
    rw [nvLocus, ht₀] at hyt
    have := (mem_nonvanishingLocus_iff_isUnit_of_res_eq σ t hWσ hrel hyW).mp hyt
    rwa [X.presheaf.germ_res_apply] at this

/-- **Raising a ratio to a common degree.** Multiplying both members of a ratio `τ = g ε` on `W`
by a power of `ε` puts them in any degree divisible by theirs, keeps `ε` nonvanishing on `W`, and
can only shrink the nonvanishing locus of `τ`. -/
private theorem exists_raise_ratio {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {q : ℕ} (τ ε : powSections L q) {W : X.Opens}
    (g : Γ(X, W)) (hWε : W ≤ nvOpen L ε)
    (hrel : resTop W (globalSection X _ τ) = g • resTop W (globalSection X _ ε)) {D : ℕ}
    (hqD : q ∣ D) (hD : 1 ≤ D) :
    ∃ τ' ε' : powSections L D, nvLocus L τ' ⊆ nvLocus L τ ∧ W ≤ nvOpen L ε' ∧
      resTop W (globalSection X _ τ') = g • resTop W (globalSection X _ ε') := by
  obtain ⟨m, rfl⟩ := hqD
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (fun h : m = 0 => by simp [h] at hD)
  refine ⟨mul (powSec L ε k) τ, mul (powSec L ε k) ε, nvLocus_mul_subset_right L _ _, ?_, ?_⟩
  · have hpow : nvLocus L (mul (powSec L ε k) ε) = nvLocus L ε :=
      nvLocus_powSec_of_one_le L ε (k + 1) (by omega)
    intro y hy
    rw [← SetLike.mem_coe, coe_nvOpen, hpow, ← coe_nvOpen]
    exact hWε hy
  · change resTop W (globalSection X (Stacks.TensorPowers.natTensorPow L (q * k + q))
        (mul (powSec L ε k) τ)) = g • resTop W (globalSection X
          (Stacks.TensorPowers.natTensorPow L (q * k + q)) (mul (powSec L ε k) ε))
    rw [globalSection_mul, globalSection_mul]
    exact resTop_app_of_res_eq _ g _ _ hrel

/-- **A reduced Cartier divisor containing a prescribed closed subset.** Let `Z` be a normal
quasi-projective variety over an algebraically closed field `k` of characteristic zero, `T₀` a
proper closed subset and `S` a finite set of points outside `T₀`. Then there is a Cartier
divisor `H'` on `Z`, with every coefficient `0` or `1`, such that `T₀ ⊆ Supp H'`,
`S ∩ Supp H' = ∅`, the reduced subscheme `Supp H'` is smooth over `k` at every point of
`Supp H' ∖ (T₀ ∪ Sing Z)`, and `H'` has coefficient `1` along every prime divisor contained
in `T₀`. -/
@[mmp "lem_mmp_foundation_prescribed_reduced_cartier_section"]
public theorem exists_isCartier_reduced_supp_superset {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sZ]
    [IsLocallyNoetherian Z] [IsNormal Z] (T₀ : Set Z) (hT₀ : IsClosed T₀) (hT₀' : T₀ ≠ Set.univ)
    (S : Set Z) (hS : S.Finite) (hST : Disjoint S T₀) :
    ∃ H' : Divisor Z, H'.IsCartier ∧ (∀ P, H'.coeff P = 0 ∨ H'.coeff P = 1) ∧
      T₀ ⊆ H'.supp ∧ Disjoint S H'.supp ∧
      (∀ z ∈ (H'.supp : Set Z), z ∉ T₀ → z ∈ sZ.smoothLocus →
        ∃ y, H'.suppIdeal.subschemeι y = z ∧
          y ∈ (H'.suppIdeal.subschemeι ≫ sZ).smoothLocus) ∧
      ∀ P : PrimeDivisor Z, P.support ⊆ T₀ → H'.coeff P = 1 := by
  classical
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : AlgebraicGeometry.IsNoetherian Z := ⟨⟩
  obtain ⟨-, L, hLinv, hLamp⟩ := IsQuasiProjectiveVariety.isQuasiProjective (f := sZ)
  haveI : Stacks.Ample.IsInvertibleModule Z L := hLinv
  have hL : Stacks.Ample.IsAmple Z L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sZ L hLamp
  have hηT : genericPoint Z ∉ T₀ := genericPoint_notMem hT₀ hT₀'
  -- a finite cover by nonvanishing loci in one degree
  obtain ⟨d₀, b₀, hd₀, -, -⟩ := exists_pos_affine_nvOpen L hL (genericPoint Z)
  obtain ⟨N₀, -, F₀, c, hN₀, -, -, -, hcover⟩ := exists_common_degree_affine_cover L hL hd₀ b₀
  -- sections nonvanishing off `T₀` only, finitely many covering `Z ∖ T₀`
  have hB : ∀ x : (T₀ᶜ : Set Z), ∃ (n : ℕ) (b : powSections L n), 1 ≤ n ∧
      x.1 ∈ nvLocus L b ∧ nvLocus L b ⊆ T₀ᶜ := by
    intro x
    obtain ⟨n, hn, s, hxs, hsV⟩ :=
      isBasisNonvanishing_of_isAmple Z L hL x.1 ⟨T₀ᶜ, hT₀.isOpen_compl⟩ x.2
    obtain ⟨a, ha⟩ := exists_powSections_nvLocus_eq L n s
    refine ⟨n, a, hn, ?_, ?_⟩
    · rw [ha]; exact hxs
    · rw [ha]; exact fun y hy => hsV hy
  choose n b hn hxb hbT using hB
  obtain ⟨F, hF⟩ := (TopologicalSpace.NoetherianSpace.isCompact (T₀ᶜ : Set Z)).elim_finite_subcover
    (fun x => nvLocus L (b x)) (fun x => by rw [← coe_nvOpen]; exact (nvOpen L (b x)).isOpen)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxb _⟩)
  -- sections of order one along the prime divisors in `T₀`
  set Es : Set (MMP.Mori.PrimeDivisor Z) := {E | E.genericPoint ∈ T₀}
  have hEfin : Es.Finite := finite_setOf_genericPoint_mem_of_ne_univ hT₀ hT₀'
  haveI : Fintype Es := hEfin.fintype
  have hC : ∀ E : Es, ∃ (q : ℕ) (τ ε : powSections L q) (W : Z.Opens)
      (hW : E.1.genericPoint ∈ W) (g : Γ(Z, W)), 1 ≤ q ∧ W ≤ nvOpen L ε ∧
      resTop W (globalSection Z _ τ) = g • resTop W (globalSection Z _ ε) ∧
      (Z.presheaf.germ W _ hW).hom g ∉
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk E.1.genericPoint)) ^ 2 ∧
      ∀ y ∈ T₀, y ∉ nvLocus L τ := by
    intro E
    obtain ⟨V, hV, h, hhT, hh2⟩ := exists_uniformizer_vanishing hT₀ hηT E.1
    obtain ⟨q, τ, ε, W, hxW, hWV, hq, hWε, hrel, hτ⟩ := exists_ratio_section L hL hV h
    refine ⟨q, τ, ε, W, hxW, _, hq, hWε, hrel, ?_, fun y hyT hyτ => ?_⟩
    · rwa [Z.presheaf.germ_res_apply]
    · obtain ⟨hyV, hu⟩ := hτ y hyτ
      exact hhT y hyV hyT hu
  choose q τ ε W hW g hq hWε hrel hg hτT using hC
  -- one common degree
  set D := N₀ * (∏ x ∈ F, n x) * ∏ E, q E
  have hD : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega)
    (Finset.prod_ne_zero_iff.mpr fun x _ => by have := hn x; omega))
    (Finset.prod_ne_zero_iff.mpr fun E _ => by have := hq E; omega))
  have hN₀D : N₀ ∣ D := dvd_mul_of_dvd_left (dvd_mul_right N₀ _) _
  have hnD : ∀ x ∈ F, n x ∣ D := fun x hx =>
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hx) _) _
  have hqD : ∀ E, q E ∣ D := fun E => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _
    (Finset.mem_univ E)) _
  choose e he using fun i => Stacks.AmpleAffineAvoidance.exists_pow_of_dvd L (c i) hN₀D hD
  choose b' hb' using fun x : F => Stacks.AmpleAffineAvoidance.exists_pow_of_dvd L (b x.1)
    (hnD x.1 x.2) hD
  choose τ' ε' hτ' hε' hrel' using fun E =>
    exists_raise_ratio L (τ E) (ε E) (g E) (hWε E) (hrel E) (hqD E) hD
  haveI := isInvertibleModule_natTensorPow L D
  refine exists_isCartier_reduced_supp_superset_of_fintype_sections sZ T₀ hT₀ hT₀' S hS hST
    (Stacks.TensorPowers.natTensorPow L D) (fun i => globalSection Z _ (e i)) (fun x => ?_)
    (Sum.elim (fun x : F => globalSection Z _ (b' x)) (fun E => globalSection Z _ (τ' E)))
    (fun j y hyT hy => ?_) (fun x hx => ?_) (fun E hE => ?_)
  · have hx : x ∈ ⨆ i, nvOpen L (c i) := hcover trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨i, ?_⟩
    change x ∈ nvLocus L (e i)
    rw [he i, ← coe_nvOpen]
    exact hi
  · rcases j with x | E
    · change y ∈ nvLocus L (b' x) at hy
      rw [hb' x] at hy
      exact hbT x.1 hy hyT
    · exact hτT E y hyT (hτ' E hy)
  · obtain ⟨i, hiF, hxi⟩ := Set.mem_iUnion₂.mp (hF hx)
    refine ⟨Sum.inl ⟨i, hiF⟩, ?_⟩
    change x ∈ nvLocus L (b' ⟨i, hiF⟩)
    rw [hb']
    exact hxi
  · have hE' : E.genericPoint ∈ T₀ := hE (MMP.Flips.primeDivisor_genericPoint_mem_support E)
    refine ⟨Sum.inr ⟨E, hE'⟩, W ⟨E, hE'⟩, hW ⟨E, hE'⟩, g ⟨E, hE'⟩,
      globalSection Z _ (ε' ⟨E, hE'⟩), ?_, ?_, ?_⟩
    · rw [← nvOpen_eq]
      exact hε' _
    · exact hrel' _
    · exact hg ⟨E, hE'⟩

end Sections

end MMP.Mori

end
