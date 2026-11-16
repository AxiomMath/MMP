module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Resolution.SmoothProjectiveOpenModel
import MMP.AlgebraicGeometry.Intersection.N1FiniteDimensionalProjective
import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Finite dimensionality of `N₁(X)` for proper curves on a possibly nonproper variety

Let `k` be an algebraically closed field of characteristic zero and `X` a variety over `k`, not
necessarily proper. The space `MMP.Mori.NumericalCurveClasses sX` is the real vector space of
finite formal sums of proper integral curves on `X`, modulo the cycles of degree zero against
every invertible sheaf on `X`. This file proves that it is finite-dimensional.

Choose a smooth projective variety `T`, a nonempty open `U ⊆ T` and a proper surjective
birational `τ : U ⟶ X`. The push-forward `N₁(U) ⟶ N₁(T)` along the open immersion is injective:
every invertible sheaf on `U` is `𝒪_U(D)` for a Weil divisor `D`, the closure `D̄` of `D` in `T`
is Cartier because `T` is smooth, and `𝒪_T(D̄)|_U ≅ 𝒪_U(D)`. So `N₁(U)` is finite-dimensional
with `N₁(T)`. The push-forward `τ_* : N₁(U) ⟶ N₁(X)` is surjective, since every proper curve
of `X` is the image of a proper curve of `U`, mapping onto it with positive degree. Hence
`N₁(X)` is finite-dimensional.

## Main results

* `MMP.Mori.finiteDimensional_numericalCurveClasses`: `N₁(X)` is a finite-dimensional real
  vector space.

## Implementation notes

The curves in `MMP.Mori.OneCycle` are proper over `k` by definition (`MMP.Mori.ProperCurve`). So
for nonproper `X` the space is the one built from proper curves, and for proper `X` it is the
usual `N₁(X)`, since there every integral closed curve is proper
(`MMP.Mori.isProperCurve_of_isProper`). Numerical triviality is tested against all invertible
sheaves on `X`. Each Cartier divisor `D` gives the invertible sheaf `𝒪_X(D)`, so this kernel lies
inside the kernel for Cartier divisors alone, and the Cartier-divisor quotient is a quotient of
this space. The statement is made for schemes in the universe `0`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

section Helpers

open Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Pushforward

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]

/-- The residue degree of `f` at the generic point of a proper curve `C` is the degree of
`C ⟶ f(C)`, the corestriction of `C.ι ≫ f` to its scheme-theoretic image. -/
private theorem residueFieldDegree_eq_degreeOver_toImage (f : X ⟶ Y) (C : ProperCurve sX)
    [IsProper (C.ι ≫ f)] [IsIntegral (C.ι ≫ f).image] :
    residueFieldDegree f C.point = degreeOver (C.ι ≫ f).toImage := by
  have h1 := residueDegree_comp C.ι f (genericPoint C.scheme)
  rw [C.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion C.ι, mul_one]
    at h1
  have h2 := residueDegree_comp (C.ι ≫ f).toImage (C.ι ≫ f).imageι (genericPoint C.scheme)
  rw [Scheme.Hom.toImage_imageι,
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (C.ι ≫ f).imageι,
    one_mul, AlgebraicGeometry.residueDegree_genericPoint_eq_degreeOver (C.ι ≫ f).toImage] at h2
  exact h1.symm.trans h2

/-- If the image of a proper curve `C` under `f` is again a proper curve, the degree
`[k(C) : k(f(C))]` is positive. -/
private theorem residueFieldDegree_pos (f : X ⟶ Y) (hf : f ≫ sY = sX) (C : ProperCurve sX)
    (hC : IsProperCurve sY (f C.point)) : 0 < residueFieldDegree f C.point := by
  set φ := C.ι ≫ f with hφdef
  have hφ : φ ≫ sY = C.ι ≫ sX := by rw [hφdef, Category.assoc, hf]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := C.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hpt : ¬ ∃ y : Y, Set.range φ = {y} := by
    rintro ⟨y, hy⟩
    have hr : ∀ t, curveSubschemeAtι (f C.point) t = y := fun t => by
      have ht : curveSubschemeAtι (f C.point) t ∈ closure {f C.point} :=
        range_curveSubschemeAtι (f C.point) ▸ ⟨t, rfl⟩
      rw [← C.range_comp f hf, ← hφdef, hy] at ht
      exact ht
    have : Subsingleton (curveSubschemeAt (f C.point)) :=
      ⟨fun a b => (curveSubschemeAtι (f C.point)).isEmbedding.injective
        ((hr a).trans (hr b).symm)⟩
    have h0 : topologicalKrullDim (curveSubschemeAt (f C.point)) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [hC.dim_eq] at h0
    norm_num at h0
  rw [residueFieldDegree_eq_degreeOver_toImage]
  apply degreeOver_pos
  rw [dominantFunctionFieldMap_eq_functionFieldMap (f := φ.toImage)]
  exact finite_functionField_image sY φ hpt

/-- **Proper surjections lift numerical classes.** If `τ : V ⟶ Y` is a proper surjective
morphism of varieties over `k`, the push-forward `τ_* : N₁(V) ⟶ N₁(Y)` is surjective. -/
private theorem pushforward_surjective {V : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    (hV : MMP.Mori.IsVariety k sV) (hY : MMP.Mori.IsVariety k sY) (τ : V ⟶ Y)
    (hτ : τ ≫ sY = sV) [IsProper τ] [Surjective τ] :
    Function.Surjective (NumericalCurveClasses.pushforward τ hτ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro w -
  obtain ⟨z, rfl⟩ := OneCycle.numericalClass_surjective sY w
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simpa only [map_add] using add_mem hz hw
  | single C' r =>
    obtain ⟨C, hC⟩ := ProperCurve.exists_image_closure_eq_of_surjective hV hY τ hτ C'
    have hpt : τ C.point = C'.point := by
      have h1 : τ C.point ∈ closure {C'.point} := hC ▸ ⟨C.point, subset_closure rfl, rfl⟩
      have h2 : C'.point ∈ closure {τ C.point} := by
        obtain ⟨c, hc, hc'⟩ : C'.point ∈ τ '' closure {C.point} := hC ▸ subset_closure rfl
        rw [← hc']
        have := image_closure_subset_closure_image (s := {C.point}) τ.continuous ⟨c, hc, rfl⟩
        rwa [Set.image_singleton] at this
      exact ((specializes_iff_mem_closure.mpr h2).antisymm
        (specializes_iff_mem_closure.mpr h1)).eq
    have hC' : IsProperCurve sY (τ C.point) := hpt ▸ C'.isProperCurve
    refine ⟨OneCycle.numericalClass sV
      (Finsupp.single C (r / (residueFieldDegree τ C.point : ℝ))), ?_⟩
    change OneCycle.numericalClass sY (OneCycle.pushforward ℝ sV sY τ _) = _
    have hd' : (residueFieldDegree τ C.point : ℝ) ≠ 0 := by
      exact_mod_cast (residueFieldDegree_pos τ hτ C hC').ne'
    have he : (⟨τ C.point, hC'⟩ : ProperCurve sY) = C' := ProperCurve.ext hpt
    congr 1
    rw [OneCycle.pushforward, Finsupp.linearCombination_single, cyclePushforwardOfPoint,
      dif_pos hC', Finsupp.smul_single, smul_eq_mul, div_mul_cancel₀ r hd', he]

end Pushforward

section DivisorialSheafRestrict

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{0}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : Mori.PrimeDivisor V) :
    Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  rw [Valuation.comap_apply, Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).2 hg),
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{0}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{0}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z)).specializes

/-- Specializing a germ from `x` to `y` and back to `x` returns it. -/
private theorem stalkSpecializes_stalkSpecializes_apply_self {Y : Scheme.{0}} {x y : Y}
    (h : x ⤳ y) (h' : y ⤳ x) (s : Y.presheaf.stalk x) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) = s := by
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{0}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{0}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply_self,
    stalkSpecializes_stalkSpecializes_apply_self] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff_evFF {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) := by
  unfold evFF
  rw [Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  simpa only [MMP.Fourfold.componentGenericPoint_eq_genericPoint] using Z.2

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, -⟩ := h
  exact ((genericPoint_spec U.toScheme).specializes trivial).mem_open V.isOpen hx

/-- `Set.univ`, viewed as the unique irreducible component of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{0}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint]⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply_self, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι)
    (functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨Classical.arbitrary U, trivial⟩)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply_self]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply_self]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF,
      evFF_restrictRF U V ψ _ ⟨_, Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← Mori.PrimeDivisor.genericPoint_mem_iff, ← Mori.PrimeDivisor.genericPoint_mem_iff,
      show Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    exact U.ι.isOpenEmbedding.injective.mem_set_image.symm
  refine ⟨fun h P hP => ?_, fun h E' hE' =>
    (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))⟩
  have hPU : P.genericPoint ∈ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    obtain ⟨x, -, hx⟩ := (Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
    rw [← hx]
    exact x.2
  obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
  exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _,
    Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h =>
    Subtype.ext (restrictRF_injective U V (congrArg Subtype.val h)), fun φ => ?_⟩
  obtain ⟨ψ, hψ⟩ :=
    restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
  refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
    (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
      D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

end DivisorialSheafRestrict

section OpenModel

variable {k : Type} [Field k]

/-- A nonempty open subscheme of a variety is a variety. -/
private theorem isVariety_ι_comp {T : Scheme.{0}} (sT : T ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k sT] (U : T.Opens) [Nonempty U] : MMP.Mori.IsVariety k (U.ι ≫ sT) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsNoetherian T := ⟨⟩
  have : IsIntegral T := ‹MMP.Mori.IsVariety k sT›.toIsIntegral
  exact (MMP.Mori.isVariety_iff k _).2
    ⟨isIntegral_of_isOpenImmersion U.ι, inferInstance, inferInstance, inferInstance⟩

/-- Every invertible sheaf on a nonempty open `U` of a smooth variety `T` is the restriction of
an invertible sheaf on `T`: it is `𝒪_U(D)` for a Weil divisor `D`, and the closure of `D` in `T`
is Cartier. -/
private theorem exists_isInvertible_pullback_iso {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    [MMP.Mori.IsVariety k sT] (hsm : IsSmoothScheme sT) (U : T.Opens) [Nonempty U]
    (L : U.toScheme.Modules)
    [SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2 L] :
    ∃ (L' : T.Modules) (_ : SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L'),
      Nonempty ((Scheme.Modules.pullback U.ι).obj L' ≅ L) := by
  have : IsIntegral T := ‹MMP.Mori.IsVariety k sT›.toIsIntegral
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsNoetherian T := ⟨⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨D, ⟨eD⟩⟩ := exists_divisorialSheaf_iso_of_isInvertible L
  let D' : Divisor T := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap U.ι) D
  have hD' : D'.restrictOpen U = D :=
    Finsupp.comapDomain_mapDomain _ (OpenWeilRestriction.primeDivisorMap_injective U.ι) D
  have hC : D'.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm D'
  have := hC.isInvertibleModule_divisorialSheaf
  have := isIso_divisorialSheafRestrictHom U D'
  exact ⟨D'.divisorialSheaf, inferInstance,
    ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm ≪≫
      asIso (divisorialSheafRestrictHom U D') ≪≫
      eqToIso (by rw [hD']) ≪≫ eD⟩⟩

/-- The degree of a real 1-cycle depends only on the isomorphism class of the invertible
sheaf. -/
private theorem OneCycle.degree_eq_of_iso {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    {L L' : X.Modules} [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    OneCycle.degree ℝ sX L = OneCycle.degree ℝ sX L' := by
  rw [OneCycle.degree, OneCycle.degree]
  congr 1
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

/-- **Proper curves on an open of a smooth projective variety.** If `U` is a nonempty open of a
smooth projective variety `T` over an algebraically closed field of characteristic zero, then
`N₁(U)` embeds in `N₁(T)`, hence is finite-dimensional. -/
private theorem finiteDimensional_of_isOpen [IsAlgClosed k] [CharZero k] {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sT] (hsm : IsSmoothScheme sT)
    (U : T.Opens) [Nonempty U] :
    FiniteDimensional ℝ (NumericalCurveClasses (U.ι ≫ sT)) := by
  have := NumericalCurveClasses.finiteDimensional_of_isProjectiveVariety sT
  refine Module.Finite.of_injective (NumericalCurveClasses.pushforward U.ι rfl) ?_
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  obtain ⟨z, rfl⟩ := OneCycle.numericalClass_surjective _ w
  have hz : OneCycle.pushforward ℝ (U.ι ≫ sT) sT U.ι z ∈ OneCycle.numericallyTrivial sT :=
    (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hw)
  refine (Submodule.Quotient.mk_eq_zero _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  obtain ⟨L', _, ⟨e⟩⟩ := exists_isInvertible_pullback_iso hsm U L
  rw [← OneCycle.degree_eq_of_iso _ e, ← OneCycle.degree_pushforward U.ι rfl]
  exact OneCycle.mem_numericallyTrivial.mp hz L'

end OpenModel

end Helpers

/-- On a variety `X` over an algebraically closed field of characteristic zero, the real
vector space `N₁(X)` of proper curves on `X` modulo numerical equivalence is finite-dimensional.
`X` need not be proper. -/
@[mmp "lem_mmp_foundation_proper_curve_numerical_space_finite_char_zero"]
public theorem finiteDimensional_numericalCurveClasses {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsVariety k sX] :
    FiniteDimensional ℝ (NumericalCurveClasses sX) := by
  obtain ⟨T, sT, hT, hsm, U, _, τ, hτp, hτs, -, hτ⟩ :=
    exists_smooth_projective_open_proper_birational sX
  have : MMP.Mori.IsVariety k sT := hT.toIsVariety
  have := finiteDimensional_of_isOpen sT ((isSmoothScheme_iff sT).2 hsm) U
  have := ‹MMP.Mori.IsVariety k sX›.toIsSeparated
  have := ‹MMP.Mori.IsVariety k sX›.toLocallyOfFiniteType
  exact Module.Finite.of_surjective _
    (pushforward_surjective (isVariety_ι_comp sT U) inferInstance τ hτ)

end MMP.Mori

end
