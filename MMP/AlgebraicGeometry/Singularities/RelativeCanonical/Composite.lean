module

public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# The relative canonical divisor of a composite; non-exceptional prime divisors (Lazarsfeld §9.1)

* For birational morphisms `g : V → X'` and `μ : X' → X` of non-singular varieties,
  `K_{V/X} = K_{V/X'} + g^* K_{X'/X}`.
* For a birational morphism `μ : X' → X` of non-singular varieties and a prime divisor
  `E ⊆ X'` not contained in `Exc(μ)`, the closure `P` of `μ(E)` is a prime divisor of `X` and
  `ord_E(μ^* G) = ord_P(G)` for every `ℝ`-divisor `G` on `X`.

## Main results

* `MMP.Positivity.IsRelativeCanonicalDivisor.comp`
* `MMP.Positivity.exists_primeDivisor_coeff_weilPullback_eq`

## Implementation notes

A non-singular variety over `k` is `MMP.Mori.IsVariety` together with `MMP.Mori.IsSmoothScheme`,
as in `MMP.Foundations.Intersection.Singularities.Resolution`; `X'` and `V` are `k`-schemes
through `μ ≫ s_X` and `g ≫ μ ≫ s_X`. "`g^* K_{X'/X}`" is any pull-back of `K_{X'/X}` along `g`
(`MMP.Intersection.IsPullback`), and "`ord_E(μ^*G)`" is the coefficient of `E` in the Weil
divisor of any pull-back of `G` (`MMP.Intersection.IsWeilPullback`), with `ord_P(G)` the
coefficient of `P` in the Weil divisor of `G` (`MMP.Intersection.IsWeilRDivisorOf`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Intersection
open MMP.Mori (Divisor RDivisor)

section Helpers

open Opposite

private theorem isTrivializingGenerator_pullbackUnit {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M] {U : Z.Opens} {e : Γ(M, U)}
    (he : IsTrivializingGenerator M U e) :
    IsTrivializingGenerator ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
      (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom M (op U) e) :=
  (Stacks.SheafOfModules.pullbackGenerator f M
    (Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Z.toRingedSpace) M) U
    ⟨e, he⟩).2

private theorem pullback_map_app_pullbackUnit {Y Z : Scheme.{u}} (f : Y ⟶ Z) {M N : Z.Modules}
    (φ : M ⟶ N) (U : Z.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ U)
        (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom M (op U) m) =
      Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom N (op U) (φ.app U m) :=
  (congrArg (fun ψ => ψ.val.app (op U) m)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)).symm

private theorem IsDivisorOfHom.eq_add_of_eq_comp {V X' : Scheme.{u}} (g : V ⟶ X')
    {L₀ M₀ : X'.Modules} {N L : V.Modules}
    [Stacks.Ample.IsInvertibleModule X' L₀] [Stacks.Ample.IsInvertibleModule X' M₀]
    [Stacks.Ample.IsInvertibleModule V N]
    {φ : L₀ ⟶ M₀} {ψ : (Scheme.Modules.pullback g).obj M₀ ⟶ N} {χ : L ⟶ N}
    (β : (Scheme.Modules.pullback g).obj L₀ ≅ L)
    (hχ : χ = β.inv ≫ (Scheme.Modules.pullback g).map φ ≫ ψ)
    {K₁ : X'.CartierDivisor} {K₂ K G : V.CartierDivisor}
    (hφ : IsDivisorOfHom φ K₁) (hψ : IsDivisorOfHom ψ K₂) (hχd : IsDivisorOfHom χ K)
    (hG : IsPullback g K₁ G) : K = K₂ + G := by
  refine eq_of_forall_isLocalEquationAt fun v => ?_
  obtain ⟨U₀, -, a₀, hvU₀, ha₀⟩ :=
    exists_isTrivializingGenerator M₀ (V := ⊤) (x := g v) trivial
  obtain ⟨U', hU'U₀, e₁, hvU', he₁⟩ := exists_isTrivializingGenerator L₀ hvU₀
  let a : Γ(M₀, U') := M₀.presheaf.map (homOfLE hU'U₀).op a₀
  have ha : IsTrivializingGenerator M₀ U' a := ha₀.res hU'U₀
  obtain ⟨rμ, hrμ⟩ := ha.bijective.2 (φ.app U' e₁)
  have hrμ' : φ.app U' e₁ = rμ • a := hrμ.symm
  obtain ⟨huμ, hlocμ⟩ := hφ.2.2 U' e₁ a he₁ ha rμ hrμ'
  let ε₀ : Γ((Scheme.Modules.pullback g).obj L₀, g ⁻¹ᵁ U') :=
    Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom L₀ (op U') e₁
  let a' : Γ((Scheme.Modules.pullback g).obj M₀, g ⁻¹ᵁ U') :=
    Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom M₀ (op U') a
  have hε₀ : IsTrivializingGenerator _ (g ⁻¹ᵁ U') ε₀ :=
    isTrivializingGenerator_pullbackUnit g L₀ he₁
  have ha' : IsTrivializingGenerator _ (g ⁻¹ᵁ U') a' := isTrivializingGenerator_pullbackUnit g M₀ ha
  obtain ⟨U, hUU', b, hvU, hb⟩ := exists_isTrivializingGenerator N (V := g ⁻¹ᵁ U') hvU'
  let εU := ((Scheme.Modules.pullback g).obj L₀).presheaf.map (homOfLE hUU').op ε₀
  let aU := ((Scheme.Modules.pullback g).obj M₀).presheaf.map (homOfLE hUU').op a'
  have hεU : IsTrivializingGenerator _ U εU := hε₀.res hUU'
  have haU : IsTrivializingGenerator _ U aU := ha'.res hUU'
  obtain ⟨rg, hrg⟩ := hb.bijective.2 (ψ.app U aU)
  have hrg' : ψ.app U aU = rg • b := hrg.symm
  obtain ⟨hug, hlocg⟩ := hψ.2.2 U aU b haU hb rg hrg'
  let c : Γ(V, U) := V.presheaf.map (homOfLE hUU').op (g.app U' rμ)
  have hφε : ((Scheme.Modules.pullback g).map φ).app U εU = c • aU := by
    have hnat := ConcreteCategory.congr_hom
      (((Scheme.Modules.pullback g).map φ).mapPresheaf.naturality (homOfLE hUU').op) ε₀
    simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at hnat
    refine hnat.trans ?_
    change ((Scheme.Modules.pullback g).obj M₀).presheaf.map (homOfLE hUU').op
      (((Scheme.Modules.pullback g).map φ).app (g ⁻¹ᵁ U') ε₀) = c • aU
    have h1 : ((Scheme.Modules.pullback g).map φ).app (g ⁻¹ᵁ U') ε₀ = g.app U' rμ • a' :=
      (pullback_map_app_pullbackUnit g φ U' e₁).trans
        ((congrArg (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom M₀ (op U')) hrμ').trans
          (Stacks.RingedSpace.pullbackUnit_smul _ _ _ _ _))
    rw [h1]
    exact Scheme.Modules.map_smul _ _ _ _
  have hβ : β.inv.app U (β.hom.app U εU) = εU := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, β.hom_inv_id]
    rfl
  have hχε : χ.app U (β.hom.app U εU) = (c * rg) • b := by
    rw [hχ]
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    rw [hβ, hφε, Scheme.Modules.Hom.app_smul, hrg', smul_smul]
  have hε : IsTrivializingGenerator L U (β.hom.app U εU) := hεU.map_iso β
  obtain ⟨hu, hloc⟩ := hχd.2.2 U (β.hom.app U εU) b hε hb (c * rg) hχε
  have hK : IsLocalEquationAt K v (stalkToTotalQuotient v (V.presheaf.germ U v hvU (c * rg))) :=
    ⟨U, hvU, hu.unit, hloc, by rw [IsUnit.unit_spec]; exact germ_toTotalQuotient hvU _⟩
  have hK₂ : IsLocalEquationAt K₂ v (stalkToTotalQuotient v (V.presheaf.germ U v hvU rg)) :=
    ⟨U, hvU, hug.unit, hlocg, by rw [IsUnit.unit_spec]; exact germ_toTotalQuotient hvU _⟩
  have hK₁ : IsLocalEquationAt K₁ (g v)
      (stalkToTotalQuotient (g v) (X'.presheaf.germ U' (g v) hvU' rμ)) :=
    ⟨U', hvU', huμ.unit, hlocμ, by rw [IsUnit.unit_spec]; exact germ_toTotalQuotient hvU' _⟩
  have hGv : IsLocalEquationAt G v
      (stalkToTotalQuotient v (g.stalkMap v (X'.presheaf.germ U' (g v) hvU' rμ))) :=
    hG.isLocalEquationAt (a := X'.presheaf.germ U' (g v) hvU' rμ) (b := 1) hK₁
      ⟨by simp, by simp⟩ ⟨by simp, by simp⟩
  have hc : V.presheaf.germ U v hvU c = g.stalkMap v (X'.presheaf.germ U' (g v) hvU' rμ) := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  refine ⟨_, hK, ?_⟩
  have := hK₂.add hGv
  rwa [map_mul, map_mul, hc, mul_comm]

/-- The Jacobian section is regular as soon as the morphism is an open immersion on a nonempty
open of the integral source. -/
private theorem isRegularHom_jacobianSection_of_isOpenImmersion {k : Type u} [Field k]
    {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X'] {μ : X' ⟶ X} (W : X'.Opens)
    (hWne : (W : Set X').Nonempty) [IsOpenImmersion (W.ι ≫ μ)] (n : ℕ) :
    IsRegularHom (jacobianSection sX μ n) := by
  intro U e e' he _ r hr x hx
  let V : X'.Opens := W.ι ''ᵁ (W.ι ⁻¹ᵁ U)
  have hVU : V ≤ U := W.ι.image_preimage_le U
  have hVne : (V : Set X').Nonempty := by
    rw [show V = W ⊓ U by
      simp only [V, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]]
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

/-- For birational morphisms `g : V ⟶ X'` and `μ : X' ⟶ X` of irreducible schemes, `g ≫ μ` is an
open immersion on a nonempty open of `V`. -/
private theorem exists_isOpenImmersion_comp {X X' V : Scheme.{u}} [IrreducibleSpace X'] [Nonempty V]
    [Nonempty X'] {μ : X' ⟶ X} {g : V ⟶ X'}
    (hμ : MMP.Mori.IsBirationalMorphism μ) (hg : MMP.Mori.IsBirationalMorphism g) :
    ∃ W : V.Opens, (W : Set V).Nonempty ∧ IsOpenImmersion (W.ι ≫ g ≫ μ) := by
  obtain ⟨Wg, hWgne, hWg⟩ := hg.exists_isOpenImmersion
  obtain ⟨Wμ, hWμne, hWμ⟩ := hμ.exists_isOpenImmersion
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter (Wg.ι ≫ g).isOpenEmbedding.isOpen_range
    Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  refine ⟨U, ⟨_, hwU⟩, ?_⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rwa [hfac]
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  rw [← Category.assoc, ← hfac, Category.assoc]
  infer_instance

end Helpers

variable {k : Type u} [Field k] {X X' V : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- **The chain rule for relative canonical divisors** (Lazarsfeld §9.1). Let `g : V → X'` and
`μ : X' → X` be birational morphisms of non-singular varieties. Then
`K_{V/X} = K_{V/X'} + g^* K_{X'/X}`. -/
@[mmp "lem_p09a_relative_canonical_divisor_composite"]
theorem IsRelativeCanonicalDivisor.comp [MMP.Mori.IsVariety k sX]
    (hX : MMP.Mori.IsSmoothScheme sX) {μ : X' ⟶ X} [MMP.Mori.IsVariety k (μ ≫ sX)]
    (hX' : MMP.Mori.IsSmoothScheme (μ ≫ sX)) {g : V ⟶ X'}
    [MMP.Mori.IsVariety k (g ≫ μ ≫ sX)] (hV : MMP.Mori.IsSmoothScheme (g ≫ μ ≫ sX))
    (hμ : MMP.Mori.IsBirationalMorphism μ)
    (hg : MMP.Mori.IsBirationalMorphism g) {KVX' : V.CartierDivisor}
    {KX'X : X'.CartierDivisor} {KVX : V.CartierDivisor} {G : V.CartierDivisor}
    (hKVX' : IsRelativeCanonicalDivisor (μ ≫ sX) g KVX')
    (hKX'X : IsRelativeCanonicalDivisor sX μ KX'X)
    (hKVX : IsRelativeCanonicalDivisor sX (g ≫ μ) KVX) (hG : IsPullback g KX'X G) :
    KVX = KVX' + G := by
  haveI : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (μ ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (g ≫ μ ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : LocallyOfFinitePresentation (μ ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : LocallyOfFinitePresentation (g ≫ μ ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).mp hX
  haveI : Smooth (μ ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hX'
  haveI : Smooth (g ≫ μ ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hV
  have hdX : topologicalKrullDim X = topologicalKrullDim X' :=
    topologicalKrullDim_eq_of_isBirationalMorphism sX (μ ≫ sX) hμ
  have hdX' : topologicalKrullDim X' = topologicalKrullDim V :=
    topologicalKrullDim_eq_of_isBirationalMorphism (μ ≫ sX) (g ≫ μ ≫ sX) hg
  obtain ⟨n, hn, hd₁⟩ := hKVX'.exists_isDivisorOfHom (μ ≫ sX) hg
  obtain ⟨n₂, hn₂, hd₂⟩ := hKX'X.exists_isDivisorOfHom sX hμ
  obtain rfl : n = n₂ := by exact_mod_cast (hdX'.trans hn).symm.trans hn₂
  obtain ⟨n₃, hn₃, ⟨-, hd₃⟩ | ⟨hreg, -⟩⟩ := hKVX
  · obtain rfl : n = n₃ := by exact_mod_cast hn.symm.trans hn₃
    have := smoothOfRelativeDimension_of_isVariety sX n (hdX.trans hn₂)
    have := smoothOfRelativeDimension_of_isVariety (μ ≫ sX) n hn₂
    have := smoothOfRelativeDimension_of_isVariety (g ≫ μ ≫ sX) n hn
    haveI : Stacks.Ample.IsInvertibleModule X'
        (Scheme.Hom.relativeDifferentialForms (μ ≫ sX) n) :=
      Stacks.Discriminant.isInvertible_relativeDifferentialForms (μ ≫ sX) n
    haveI : Stacks.Ample.IsInvertibleModule V
        (Scheme.Hom.relativeDifferentialForms (g ≫ μ ≫ sX) n) :=
      Stacks.Discriminant.isInvertible_relativeDifferentialForms (g ≫ μ ≫ sX) n
    haveI : Stacks.Ample.IsInvertibleModule X' ((Scheme.Modules.pullback μ).obj
        (Scheme.Hom.relativeDifferentialForms sX n)) :=
      @Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback _ _
        μ.toLRSHom.toShHom _ (Stacks.Discriminant.isInvertible_relativeDifferentialForms sX n)
    exact IsDivisorOfHom.eq_add_of_eq_comp g
      ((Scheme.Modules.pullbackComp g μ).app (Scheme.Hom.relativeDifferentialForms sX n))
      (Scheme.Hom.relativeDifferentialFormsMap_comp μ g sX (μ ≫ sX) (g ≫ μ ≫ sX) (𝟙 _) (𝟙 _)
        (𝟙 _) (by simp) (by simp) (by simp) n) hd₂ hd₁ hd₃ hG
  · exfalso
    obtain ⟨W, hWne, hW⟩ := exists_isOpenImmersion_comp hμ hg
    haveI : IsOpenImmersion (W.ι ≫ g ≫ μ) := hW
    exact hreg (isRegularHom_jacobianSection_of_isOpenImmersion sX (μ := g ≫ μ) W hWne n₃)

/-- **Non-exceptional prime divisors** (Lazarsfeld §9.1). Let `μ : X' → X` be a birational
morphism of non-singular varieties and `E ⊆ X'` a prime divisor with `E ⊄ Exc(μ)`. Then the
closure `P` of `μ(E)` is a prime divisor of `X`, and `ord_E(μ^*G) = ord_P(G)` for every
`ℝ`-divisor `G` on `X`. -/
@[mmp "lem_p09a_non_exceptional_divisor_order"]
theorem exists_primeDivisor_coeff_weilPullback_eq [MMP.Mori.IsVariety k sX]
    (hX : MMP.Mori.IsSmoothScheme sX) {μ : X' ⟶ X} [MMP.Mori.IsVariety k (μ ≫ sX)]
    (hX' : MMP.Mori.IsSmoothScheme (μ ≫ sX)) (hμ : MMP.Mori.IsBirationalMorphism μ)
    (E : MMP.Mori.PrimeDivisor X') (hE : ¬ (E.support : Set X') ⊆ exceptionalLocus μ) :
    ∃ P : MMP.Mori.PrimeDivisor X, (P.support : Set X) = closure (μ '' (E.support : Set X')) ∧
      ∀ (G : RCartierDivisor X) (w : RDivisor X) (w' : RDivisor X'), IsWeilRDivisorOf G w →
        IsWeilPullback μ G w' → w'.coeff E = w.coeff P := by
  haveI : LocallyOfFiniteType sX := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (μ ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  obtain ⟨Q, hQ, hiso⟩ := exists_primeDivisor_genericPoint_eq_of_not_subset hE
  refine ⟨Q, ?_, fun G w w' hw hw' => hw'.coeff_eq_of_genericPoint_eq hw hQ⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    show AlgebraicGeometry.PrimeDivisor.genericPoint Q = μ E.genericPoint from hQ,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  apply subset_antisymm
  · exact closure_mono (Set.singleton_subset_iff.mpr
      ⟨E.genericPoint, subset_closure rfl, rfl⟩)
  · refine closure_minimal ?_ isClosed_closure
    exact (image_closure_subset_closure_image μ.continuous).trans
      (closure_mono (by rw [Set.image_singleton]))

end MMP.Positivity
