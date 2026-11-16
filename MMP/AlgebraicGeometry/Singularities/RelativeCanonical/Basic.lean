module

public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.Basic
public import MMP.AlgebraicGeometry.Divisor.CartierCoefficients
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Nilpotent

/-!
# Regularity of the Jacobian section and the support of `K_{X'/X}` (Lazarsfeld §9.1.B)

Let `μ : X' ⟶ X` be a birational morphism of varieties over a field `k`, and
`j_μ : μ^*Ω^n_{X/k} ⟶ Ω^n_{X'/k}` its Jacobian section, the pull-back of `n`-forms. A birational
morphism is an open immersion on a non-empty open `W ⊆ X'`; there pull-back of forms along the
étale morphisms `W ⟶ X` and `W ⟶ X'` is an isomorphism, so `j_μ` is an isomorphism over `W`.
Since `X'` is integral and `W` is dense, `j_μ` is then a regular section of
`ω_{X'} ⊗ μ^*ω_X^{-1}`: on any open trivializing both line bundles its local function is non-zero,
hence a non-zero-divisor in every local ring.

Consequently `K_{X'/X}` is the divisor of `j_μ`. If `X'` is moreover non-singular of dimension
`n`, then `Ω^n_{X'/k}` is invertible, and near a point `y ∉ Exc(μ)` a trivializing section `e'` of
`Ω^n_{X'/k}` is the image of the trivializing section `j_μ^{-1}(e')` of `μ^*Ω^n_{X/k}`, so
`K_{X'/X}` has local equation `1` near `y`. Hence `Supp K_{X'/X} ⊆ Exc(μ)`, and every prime
divisor along which `K_{X'/X}` has non-zero order lies in `Exc(μ)`, i.e. is a component of
`except(μ)`.

## Main results

* `MMP.Intersection.isRegularHom_jacobianSection`: the Jacobian section of a birational morphism
  from an integral scheme is regular, in every degree.
* `MMP.Intersection.IsRelativeCanonicalDivisor.cartierSupport_subset_exceptionalLocus`:
  `Supp K_{X'/X} ⊆ Exc(μ)`.
* `MMP.Intersection.IsRelativeCanonicalDivisor.support_subset_exceptionalLocus` and
  `MMP.Intersection.IsRelativeCanonicalDivisor.coeff_exceptionalDivisorSum_eq_one`: every prime
  component of `K_{X'/X}` is contained in `Exc(μ)`, and is a component of `except(μ)`.

## Implementation notes

* Regularity is proved for a birational `μ` with `X'` integral, in every degree `n`; neither
  smoothness, properness nor the dimension enter. The support statements need `X'` to be a
  non-singular variety (so that `Ω^n_{X'/k}` is invertible for `n = dim X'`); neither properness of
  `μ` nor any hypothesis on `X` is used.
* A non-singular variety is smooth of relative dimension its dimension
  (`MMP.Intersection.smoothOfRelativeDimension_of_isVariety`), which is what invertibility of the
  top forms requires.
* A prime component of the Cartier divisor `K_{X'/X}` is a prime divisor `P` with
  `ord_P(K_{X'/X}) ≠ 0`, the order read through the Weil divisor of `K_{X'/X}`
  (`MMP.Intersection.IsWeilDivisorOfCartier`).

## References

* R. Lazarsfeld, *Positivity in Algebraic Geometry II*, §9.1.B.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace MMP.Intersection

open MMP.Mori (Divisor)

variable {k : Type u} [Field k] {X X' : Scheme.{u}}

/-- A birational morphism is an open immersion on a nonempty open of a nonempty source. -/
theorem _root_.MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion [Nonempty X'] {μ : X' ⟶ X}
    (hμ : MMP.Mori.IsBirationalMorphism μ) :
    ∃ W : X'.Opens, (W : Set X').Nonempty ∧ IsOpenImmersion (W.ι ≫ μ) := by
  obtain ⟨e, he⟩ := hμ
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  refine ⟨W, hW.nonempty, ?_⟩
  have h' : W.ι ≫ μ = (e.toPartialMap.restrict W hW hWe).hom := by
    rw [h]
    simp only [Scheme.PartialMap.restrict, Scheme.Hom.toPartialMap_hom, Scheme.topIso_hom]
    exact (Scheme.homOfLE_ι_assoc X' hWf μ).symm
  rw [h']
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom]
  have : IsOpenImmersion e.iso.hom := IsOpenImmersion.of_isIso _
  have : IsOpenImmersion (e.iso.hom ≫ e.target.ι) := IsOpenImmersion.comp _ _
  exact @IsOpenImmersion.comp _ _ _ _ _ inferInstance this

/-- A Cartier divisor with local equation `1` on a neighbourhood of the generic point of a
subvariety `V` has order `0` along `V`. -/
theorem IsOrderAlong.eq_zero_of_isLocalEquationOn_one {Y : Scheme.{u}} {D : Y.CartierDivisor}
    {V : Scheme.Subvariety Y} {N : ℤ} (hN : IsOrderAlong D V N) {U : Y.Opens}
    (hVU : V.genericPoint ∈ U) (hU : IsLocalEquationOn D U 1) : N = 0 := by
  obtain ⟨a, b, -, -, ⟨g, hg, hb, hab⟩, la, lb, hla, hlb, rfl⟩ := hN
  obtain ⟨u, hu, rfl⟩ := MMP.Mori.IsLocalEquationOn.exists_isUnit_eq_mul hU hVU hg
  rw [Units.val_one, map_one, mul_one, ← map_mul] at hab
  have hspan : Ideal.span {a} = Ideal.span {b} := by
    rw [← stalkToTotalQuotient_injective _ hab, Ideal.span_singleton_mul_right_unit hu]
  rw [hspan, hlb] at hla
  rw [Nat.cast_inj.mp hla, sub_self]

variable (sX : X ⟶ Spec (.of k))

/-- Over an open `W ⊆ X'` on which `μ` is an open immersion, the restriction of the Jacobian
section to `W` is an isomorphism. -/
theorem isIso_restrict_map_jacobianSection (μ : X' ⟶ X) (W : X'.Opens)
    [IsOpenImmersion (W.ι ≫ μ)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map (jacobianSection sX μ n)) := by
  have hcomp := Scheme.Hom.relativeDifferentialFormsMap_comp μ W.ι sX (μ ≫ sX) (W.ι ≫ μ ≫ sX)
    (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) (by simp) n
  have h₁ := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale (W.ι ≫ μ) sX
    (W.ι ≫ μ ≫ sX) (𝟙 _) (by simp) (n : ℤ)
  have h₂ := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale W.ι (μ ≫ sX)
    (W.ι ≫ μ ≫ sX) (𝟙 _) (by simp) (n : ℤ)
  rw [hcomp] at h₁
  have h₃ : IsIso ((Scheme.Modules.pullback W.ι).map (jacobianSection sX μ n)) := by
    have := @IsIso.of_isIso_comp_left _ _ _ _ _
      ((Scheme.Modules.pullbackComp W.ι μ).inv.app (Scheme.Hom.relativeDifferentialForms sX n))
      _ _ h₁
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h₂ this
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.naturality
    (jacobianSection sX μ n)
  have : IsIso ((Scheme.Modules.restrictFunctor W.ι).map (jacobianSection sX μ n) ≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app _) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).hom.app _)

/-- Over the image of an open of `W`, where `W ⊆ X'` is an open on which `μ` is an open
immersion, the Jacobian section is bijective on sections. -/
theorem bijective_jacobianSection_app_image (μ : X' ⟶ X) (W : X'.Opens)
    [IsOpenImmersion (W.ι ≫ μ)] (n : ℕ) (V : W.toScheme.Opens) :
    Function.Bijective ((jacobianSection sX μ n).app (W.ι ''ᵁ V)) := by
  have := isIso_restrict_map_jacobianSection sX μ W n
  exact ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor W.ι).map (jacobianSection sX μ n)) V)

/-- **The Jacobian section of a birational morphism is regular** (Lazarsfeld §9.1.B): for a
birational morphism `μ : X' ⟶ X` with `X'` integral, `j_μ : μ^*Ω^n_{X/k} ⟶ Ω^n_{X'/k}` is a
regular homomorphism of line bundles, in every degree `n`. -/
@[mmp "lem_p09a_jacobian_section_regular"]
theorem isRegularHom_jacobianSection [IsIntegral X'] {μ : X' ⟶ X}
    (hμ : MMP.Mori.IsBirationalMorphism μ) (n : ℕ) :
    IsRegularHom (jacobianSection sX μ n) := by
  intro U e e' he _ r hr x hx
  obtain ⟨W, hWne, hW⟩ := hμ.exists_isOpenImmersion
  let V : X'.Opens := W.ι ''ᵁ (W.ι ⁻¹ᵁ U)
  have hVU : V ≤ U := W.ι.image_preimage_le U
  have hVne : (V : Set X').Nonempty := by
    have hV : V = W ⊓ U := by
      simp only [V, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    rw [hV]
    exact nonempty_preirreducible_inter W.isOpen U.isOpen hWne ⟨x, hx⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h0
  have hr0 : r = 0 := germ_injective_of_isIntegral X' x hx (by rw [h0, map_zero])
  rw [hr0, zero_smul] at hr
  have h1 : (jacobianSection sX μ n).app V
      (((Scheme.Modules.pullback μ).obj (Scheme.Hom.relativeDifferentialForms sX n)).presheaf.map
        (homOfLE hVU).op e) = 0 := by
    have := ConcreteCategory.congr_hom
      ((jacobianSection sX μ n).mapPresheaf.naturality (homOfLE hVU).op) e
    simp only [Scheme.Modules.mapPresheaf_app] at this
    rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hr, map_zero] at this
  have h2 := (bijective_jacobianSection_app_image sX μ W n (W.ι ⁻¹ᵁ U)).1
    (h1.trans (map_zero _).symm)
  have h3 := (he V hVU).1 (show (1 : Γ(X', V)) • _ = (0 : Γ(X', V)) • _ by
    simp only [h2, smul_zero])
  have : Nonempty V := hVne.to_subtype
  exact one_ne_zero h3

/-- A smooth variety of dimension `n` over `k` is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_of_isVariety {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k f] [Smooth f] (n : ℕ) (hn : topologicalKrullDim Y = n) :
    SmoothOfRelativeDimension n f := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f n fun x => ?_
  have heq : (f ⁻¹' {f x}) = (Set.univ : Set Y) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  let e : f.fiber (f x) ≃ₜ Y :=
    (f.fiberHomeo (f x)).trans ((Homeomorph.setCongr heq).trans (Homeomorph.Set.univ Y))
  rwa [topologicalKrullDimAt_eq_of_homeomorph e,
    ← AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y f]

/-- Over every open `V ⊆ W`, where `W ⊆ X'` is an open on which `μ` is an open immersion, the
Jacobian section is bijective on sections. -/
theorem bijective_jacobianSection_app_of_le (μ : X' ⟶ X) (W : X'.Opens)
    [IsOpenImmersion (W.ι ≫ μ)] (n : ℕ) {V : X'.Opens} (hV : V ≤ W) :
    Function.Bijective ((jacobianSection sX μ n).app V) := by
  obtain ⟨V', rfl⟩ : ∃ V' : W.toScheme.Opens, W.ι ''ᵁ V' = V :=
    ⟨W.ι ⁻¹ᵁ V, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hV⟩
  exact bijective_jacobianSection_app_image sX μ W n V'

/-- Away from the exceptional locus, the divisor of the Jacobian section of degree `dim X'` has
local equation `1` on some neighbourhood of each point. -/
theorem exists_isLocalEquationOn_one_of_notMem_exceptionalLocus {μ : X' ⟶ X}
    [MMP.Mori.IsVariety k (μ ≫ sX)] [Smooth (μ ≫ sX)] (n : ℕ) (hn : topologicalKrullDim X' = n)
    {K : X'.CartierDivisor} (hK : IsDivisorOfHom (jacobianSection sX μ n) K) {y : X'}
    (hy : y ∉ exceptionalLocus μ) :
    ∃ U : X'.Opens, y ∈ U ∧ IsLocalEquationOn K U 1 := by
  simp only [mem_exceptionalLocus_iff, not_forall, not_not] at hy
  obtain ⟨W, hyW, hW⟩ := hy
  have := smoothOfRelativeDimension_of_isVariety (μ ≫ sX) n hn
  have hinv := Stacks.Discriminant.isInvertible_relativeDifferentialForms (μ ≫ sX) n
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := X'.toRingedSpace)
    (Scheme.Hom.relativeDifferentialForms (μ ≫ sX) n) (h := hinv)
  have : ∀ z : X'.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X'.toRingedSpace z) :=
    X'.isLocalRing
  obtain ⟨U₀, hyU₀, a, ha⟩ := Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible
    (X := X'.toRingedSpace) (Scheme.Hom.relativeDifferentialForms (μ ≫ sX) n) y
  let L := (Scheme.Modules.pullback μ).obj (Scheme.Hom.relativeDifferentialForms sX n)
  let M := Scheme.Hom.relativeDifferentialForms (μ ≫ sX) n
  let φ := jacobianSection sX μ n
  let U : X'.Opens := U₀ ⊓ W
  let a' : Γ(M, U₀) := a
  let e' : Γ(M, U) := M.presheaf.map (homOfLE (inf_le_left : U ≤ U₀)).op a'
  have he' : IsTrivializingGenerator M U e' := by
    intro V hV
    have hres : M.presheaf.map (homOfLE hV).op e' =
        M.presheaf.map (homOfLE (hV.trans inf_le_left)).op a' := by
      simp only [e']
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [hres]
    exact ha V (hV.trans inf_le_left)
  obtain ⟨e, he⟩ := (bijective_jacobianSection_app_of_le sX μ W n
    (inf_le_right : U ≤ W)).2 e'
  have heT : IsTrivializingGenerator L U e := by
    intro V hV
    have hb := bijective_jacobianSection_app_of_le sX μ W n (hV.trans inf_le_right)
    have hcomp : (φ.app V) ∘ (fun r : Γ(X', V) => r • L.presheaf.map (homOfLE hV).op e) =
        fun r : Γ(X', V) => r • M.presheaf.map (homOfLE hV).op e' := by
      funext r
      have hnat := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hV).op) e
      simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at hnat
      simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul]
      rw [hnat, he]
    exact (Function.Bijective.of_comp_iff' hb _).mp (hcomp ▸ he' V hV)
  obtain ⟨h1, hloc⟩ := hK.2.2 U e e' heT he' 1 (by rwa [one_smul])
  refine ⟨U, ⟨hyU₀, hyW⟩, ?_⟩
  rwa [show h1.unit = 1 from Units.ext (map_one _)] at hloc

/-- For a birational morphism from an integral scheme, the relative canonical divisor is the
divisor of the Jacobian section in degree `dim X'` (the convention `K = 0` for a non-regular
Jacobian section never applies). -/
theorem IsRelativeCanonicalDivisor.exists_isDivisorOfHom [IsIntegral X'] {μ : X' ⟶ X}
    (hμ : MMP.Mori.IsBirationalMorphism μ) {K : X'.CartierDivisor}
    (hK : IsRelativeCanonicalDivisor sX μ K) :
    ∃ n : ℕ, topologicalKrullDim X' = n ∧ IsDivisorOfHom (jacobianSection sX μ n) K := by
  obtain ⟨n, hn, ⟨-, hdiv⟩ | ⟨hreg, -⟩⟩ := hK
  · exact ⟨n, hn, hdiv⟩
  · exact absurd (isRegularHom_jacobianSection sX hμ n) hreg

private theorem IsRelativeCanonicalDivisor.exists_isLocalEquationOn_one {μ : X' ⟶ X}
    [MMP.Mori.IsVariety k (μ ≫ sX)] (hsm : MMP.Mori.IsSmoothScheme (μ ≫ sX))
    (hμ : MMP.Mori.IsBirationalMorphism μ) {K : X'.CartierDivisor}
    (hK : IsRelativeCanonicalDivisor sX μ K) {y : X'} (hy : y ∉ exceptionalLocus μ) :
    ∃ U : X'.Opens, y ∈ U ∧ IsLocalEquationOn K U 1 := by
  have : LocallyOfFinitePresentation (μ ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
      AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : Smooth (μ ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hsm
  obtain ⟨n, hn, hdiv⟩ := hK.exists_isDivisorOfHom sX hμ
  exact exists_isLocalEquationOn_one_of_notMem_exceptionalLocus sX n hn hdiv hy

/-- **`K_{X'/X}` is supported on the exceptional locus** (Lazarsfeld §9.1.B): for a birational
morphism `μ : X' ⟶ X` from a non-singular variety, `Supp K_{X'/X} ⊆ Exc(μ)`. -/
@[mmp "lem_p09a_relative_canonical_divisor_exceptional"]
theorem IsRelativeCanonicalDivisor.cartierSupport_subset_exceptionalLocus {μ : X' ⟶ X}
    [MMP.Mori.IsVariety k (μ ≫ sX)] (hsm : MMP.Mori.IsSmoothScheme (μ ≫ sX))
    (hμ : MMP.Mori.IsBirationalMorphism μ) {K : X'.CartierDivisor}
    (hK : IsRelativeCanonicalDivisor sX μ K) :
    cartierSupport K ⊆ exceptionalLocus μ := by
  intro y hy
  by_contra hyE
  obtain ⟨U, hyU, hU⟩ := hK.exists_isLocalEquationOn_one sX hsm hμ hyE
  apply hy
  have h0 : restrictDivisor K U = 0 := by
    rw [← hU]
    unfold cartierClass
    exact map_zero _
  rw [← TopCat.Presheaf.germ_res_apply (cartierSheaf X').presheaf (homOfLE le_top) y hyU K]
  change (cartierSheaf X').presheaf.germ U y hyU (restrictDivisor K U) = 0
  rw [h0, map_zero]

/-- **Every prime component of `K_{X'/X}` lies in the exceptional locus** (Lazarsfeld §9.1.B):
for a birational morphism `μ : X' ⟶ X` from a non-singular variety, a prime divisor `P` along
which `K_{X'/X}` has non-zero order is contained in `Exc(μ)`. -/
@[mmp "lem_p09a_relative_canonical_divisor_exceptional"]
theorem IsRelativeCanonicalDivisor.support_subset_exceptionalLocus {μ : X' ⟶ X}
    [MMP.Mori.IsVariety k (μ ≫ sX)] (hsm : MMP.Mori.IsSmoothScheme (μ ≫ sX))
    (hμ : MMP.Mori.IsBirationalMorphism μ) {K : X'.CartierDivisor}
    (hK : IsRelativeCanonicalDivisor sX μ K) {wK : Divisor X'} (hw : IsWeilDivisorOfCartier K wK)
    {P : MMP.Mori.PrimeDivisor X'} (hP : wK.coeff P ≠ 0) :
    P.support ⊆ exceptionalLocus μ := by
  intro y hy
  by_contra hyE
  obtain ⟨U, hyU, hU⟩ := hK.exists_isLocalEquationOn_one sX hsm hμ hyE
  have hgen := (primeDivisorSubvariety P).isGenericPoint_genericPoint
  have hsp : (primeDivisorSubvariety P).genericPoint ⤳ y := by
    rwa [specializes_iff_mem_closure, hgen.def]
  exact hP ((hw P).eq_zero_of_isLocalEquationOn_one (hsp.mem_open U.isOpen hyU) hU)

/-- **`K_{X'/X}` is supported on `except(μ)`** (Lazarsfeld §9.1.B): every prime divisor along
which `K_{X'/X}` has non-zero order is a component of the exceptional divisor `except(μ)`. -/
@[mmp "lem_p09a_relative_canonical_divisor_exceptional"]
theorem IsRelativeCanonicalDivisor.coeff_exceptionalDivisorSum_eq_one {μ : X' ⟶ X}
    [MMP.Mori.IsVariety k (μ ≫ sX)] (hsm : MMP.Mori.IsSmoothScheme (μ ≫ sX))
    (hμ : MMP.Mori.IsBirationalMorphism μ) {K : X'.CartierDivisor}
    (hK : IsRelativeCanonicalDivisor sX μ K) {wK : Divisor X'} (hw : IsWeilDivisorOfCartier K wK)
    {E : Divisor X'} (hE : IsExceptionalDivisorSum μ E) {P : MMP.Mori.PrimeDivisor X'}
    (hP : wK.coeff P ≠ 0) : E.coeff P = 1 := by
  simp only [hE P, hK.support_subset_exceptionalLocus sX hsm hμ hw hP, ite_true]

end MMP.Intersection
