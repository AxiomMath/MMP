module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.Adjunction.SmoothDivisorResidueRestriction

/-!
# Effective residue adjunction on a normal prime divisor

Let `X` be a normal complex variety of dimension `n + 1`, `S ⊂ X` a normal prime divisor and
`B ≥ 0` a `ℚ`-divisor not containing `S`, such that `D = K_X + S + B` is `ℚ`-Cartier. Fix the
canonical divisor through a rational top form: `K_X = div(τ)` with `τ` having a simple pole along
`S`, and `K_S = div(ρ)` with `ρ = Res_S τ` its Poincaré residue. Then `S` is not a component of
`D`, so the `ℚ`-Cartier divisor `D` restricts to `S`, and there is an effective `ℚ`-divisor `B_S`
on `S` with `K_S + B_S = D|_S`. Moreover, for a log resolution `p : Y ⟶ X` of `(X, S + B)` with
strict transform `S'` of `S`, induced map `q : S' ⟶ S`, `K_Y = div(p^*τ)`, `K_{S'}` the divisor of
the residue of `p^*τ` along `S'` and `K_Y + Γ = p^*D`,
`K_{S'} + (Γ - S')|_{S'} = q^*(K_S + B_S)`.

## Main results

* `MMP.Mori.Divisor.IsPullback.comp`, `MMP.Mori.QDivisor.IsPullback.comp`: pull-back is
  functorial for composites.
* `MMP.Fourfold.exists_isEffective_isPullback_divisorOfForm_isPoincareResidue`: effective residue
  adjunction `K_S + B_S = D|_S` on a normal prime divisor, compatible with log resolutions.

## Implementation notes

Restriction of a `ℚ`-Cartier divisor to `S` is its pull-back along the closed immersion
`S ⟶ X` (`MMP.Mori.QDivisor.IsPullback`), which is defined since the generic point of `S` lies
off the support. The canonical divisors are the divisors of the chosen compatible forms, so that
neither adjoint has `S`, respectively `S'`, as a component; `B_S` is determined by the first
equality.

Writing `j : T ⟶ X` for the inclusion of `S` and `j' : T' ⟶ Y` for that of `S'`, the restriction
`D|_T` is the `ℚ`-Cartier pull-back along `j`
(`MMP.Mori.QDivisor.IsQCartier.existsUnique_isPullback`) and `B_S = D|_T - div ρ`; its
effectivity is checked at each codimension-one point of `T`
(`MMP.Fourfold.coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue`). For a log resolution
`p : Y ⟶ X` the strict transform `T'` is smooth, being a component of the snc divisor
`Ex(p) ∪ p⁻¹(Supp (P + B))`, and `p^*τ` has a simple pole along it. Residue adjunction on the
smooth `Y` (`MMP.Fourfold.isPullback_divisorOfForm_add_of_isPoincareResidue`) gives
`j'^*(K_Y + Γ) = K_{T'} + (Γ - T')|_{T'}`, and `q^*(D|_T) = (q ≫ j)^*D = (j' ≫ p)^*D` by
functoriality and uniqueness of `ℚ`-Cartier pull-backs.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 16
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

namespace Divisor

/-- **Pull-back of Cartier divisors is functorial.** If `B' = f^*B` and `B'' = g^*B'`, then
`B'' = (g ≫ f)^*B`; no dominance of `f` or `g` is needed. -/
theorem IsPullback.comp {X Y Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ Z} {g : X ⟶ Y} {B : Divisor Z} (hBc : B.IsCartier)
    {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ B.supp}
    {B' : Divisor Y} (h₁ : B.IsPullback f hB B')
    {hB' : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ B'.supp}
    {B'' : Divisor X} (h₂ : B'.IsPullback g hB' B'')
    (hB'' : ∀ W : irreducibleComponents X, (g ≫ f) (componentGenericPoint X W) ∉ B.supp) :
    B.IsPullback (g ≫ f) hB'' B'' := by
  classical
  refine Divisor.IsPullback.of_forall_exists fun E => ?_
  obtain ⟨U, hU, φ, hφ⟩ := hBc ((g ≫ f) E.genericPoint)
  let ψ : (RationalFunctions Y)ˣ := (RationalFunctions.unitsEquiv Y).symm fun W =>
    if hW : f (componentGenericPoint Y W) ∈ U then pullbackComponent f hB hφ W hW else 1
  have hψW : ∀ (W : irreducibleComponents Y) (hW : f (componentGenericPoint Y W) ∈ U),
      Units.map (RationalFunctions.component Y W).toMonoidHom ψ =
        pullbackComponent f hB hφ W hW := by
    intro W hW
    ext
    change (if hW : f (componentGenericPoint Y W) ∈ U then
      pullbackComponent f hB hφ W hW else 1).val = _
    rw [dif_pos hW]
  have hψ : B'.IsLocalEquation (f ⁻¹ᵁ U) ψ := by
    intro E' hE'
    rw [h₁ U φ hφ E' hE', PrimeDivisor.ord_eq_ordUnit, hψW]
  have hE : (E.support ∩ (g ≫ f) ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff _).mp hU
  refine ⟨U, φ, hφ, hE, ?_⟩
  rw [h₂ (f ⁻¹ᵁ U) ψ hψ E hE]
  congr 1
  set η := componentGenericPoint X E.component
  have hzU : f (g η) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' E.component) (mem_pointComponent _)
  rw [pullbackComponent_eq hB'' hφ _ (mem_pointComponent _) a ha]
  set W' := pointComponent (g η)
  have hsp : componentGenericPoint Y W' ⤳ g η :=
    (isGenericPoint_componentGenericPoint Y W').specializes (mem_pointComponent _)
  have hsp' : f (componentGenericPoint Y W') ⤳ f (g η) := f.base.hom.map_specializes hsp
  have hW'U : f (componentGenericPoint Y W') ∈ U := hsp'.mem_open U.isOpen hzU
  have hzW'' : f (g η) ∈ (pointComponent (f (componentGenericPoint Y W'))).1 :=
    hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _
      (pointComponent (f (componentGenericPoint Y W'))).2) (mem_pointComponent _)
  have hWW : pointComponent (f (componentGenericPoint Y W')) = pointComponent (f (g η)) :=
    eq_of_mem_irreducibleComponents hzW'' (mem_pointComponent _)
  have hmem : f (componentGenericPoint Y W') ∈ (pointComponent (f (g η))).1 :=
    hWW ▸ mem_pointComponent _
  let a' : (Z.presheaf.stalk (f (componentGenericPoint Y W')))ˣ :=
    Units.map (Z.presheaf.stalkSpecializes hsp').hom.toMonoidHom a
  have ha' : (stalkToRationalFunctions Z hmem).hom a' =
      (φ : RationalFunctions Z) (pointComponent (f (g η))) := by
    rw [← ha]
    change (Z.presheaf.stalkSpecializes hsp' ≫ Z.presheaf.stalkSpecializes _).hom a.val =
      (Z.presheaf.stalkSpecializes _).hom a.val
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  let b : (Y.presheaf.stalk (g η))ˣ := Units.map (f.stalkMap (g η)).hom.toMonoidHom a
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g η))).hom b =
      (ψ : RationalFunctions Y) W' := by
    have h1 := congrArg Units.val (hψW W' hW'U)
    change _ = (Units.map (RationalFunctions.component Y W').toMonoidHom ψ).val
    rw [h1, pullbackComponent_eq hB hφ hW'U hmem a' ha']
    change (Y.presheaf.stalkSpecializes hsp).hom ((f.stalkMap (g η)).hom a.val) =
      (f.stalkMap _).hom ((Z.presheaf.stalkSpecializes hsp').hom a.val)
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent _) b hb]
  ext
  change (g.stalkMap η).hom ((f.stalkMap (g η)).hom a.val) = ((g ≫ f).stalkMap η).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

end Divisor

namespace QDivisor

/-- **Pull-back of `ℚ`-divisors is functorial.** If `D₁ = f^*D` and `D₂ = g^*D₁`, then
`D₂ = (g ≫ f)^*D`; no dominance of `f` or `g` is needed. -/
theorem IsPullback.comp {X Y Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ Z} {g : X ⟶ Y} {D : QDivisor Z}
    {hD : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ D.supp}
    {D₁ : QDivisor Y} (h₁ : D.IsPullback f hD D₁)
    {hD₁ : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ D₁.supp}
    {D₂ : QDivisor X} (h₂ : D₁.IsPullback g hD₁ D₂)
    (hD₂ : ∀ W : irreducibleComponents X, (g ≫ f) (componentGenericPoint X W) ∉ D.supp) :
    D.IsPullback (g ≫ f) hD₂ D₂ := by
  intro m hm E hE hEc
  obtain ⟨E', hE', hp⟩ := h₁ m hm E hE hEc
  obtain ⟨E'', hE'', hp'⟩ := h₂ m hm E' hE' (hp.isCartier hEc)
  exact ⟨E'', hE'', hp.comp hEc hp' _⟩

end QDivisor

end MMP.Mori

namespace MMP.Fourfold

open MMP.Mori

/-- A prime divisor whose generic point maps off the support of a Cartier divisor has
coefficient zero in its pull-back. -/
private theorem divisor_coeff_eq_zero_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : Divisor Y}
    (hBc : B.IsCartier)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {B' : Divisor X} (h : B.IsPullback f hB B') (E : Mori.PrimeDivisor X)
    (hE : f E.genericPoint ∉ B.supp) : B'.coeff E = 0 := by
  obtain ⟨U, hU, φ, hφ⟩ := hBc (f E.genericPoint)
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff _).mp hU
  rw [h U φ hφ E hEU]
  have hsp : componentGenericPoint X E.component ⤳ E.genericPoint := E.specializes_genericPoint
  have hsp' : f (componentGenericPoint X E.component) ⤳ f E.genericPoint :=
    f.base.hom.map_specializes hsp
  set W := pointComponent (f (componentGenericPoint X E.component))
  have hW : f (componentGenericPoint X E.component) ∈ W.1 := mem_pointComponent _
  have hyW : f E.genericPoint ∈ W.1 :=
    hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) hW
  obtain ⟨c, hc⟩ := hφ.exists_unit_stalk hU hE hyW
  let c' : (Y.presheaf.stalk (f (componentGenericPoint X E.component)))ˣ :=
    Units.map (Y.presheaf.stalkSpecializes hsp').hom.toMonoidHom c
  have hc' : (stalkToRationalFunctions Y hW).hom c' = (φ : RationalFunctions Y) W := by
    rw [← hc]
    change (Y.presheaf.stalkSpecializes hsp' ≫ Y.presheaf.stalkSpecializes _).hom c.val =
      (Y.presheaf.stalkSpecializes _).hom c.val
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  rw [pullbackComponent_eq hB hφ _ hW c' hc']
  refine E.ordUnit_eq_zero_of_isUnit ((c.isUnit).map (f.stalkMap E.genericPoint).hom) ?_
  change (X.presheaf.stalkSpecializes _).hom ((f.stalkMap E.genericPoint).hom
    c.val) = (f.stalkMap _).hom ((Y.presheaf.stalkSpecializes hsp').hom c.val)
  rw [Scheme.Hom.stalkSpecializes_stalkMap_apply]

/-- A prime divisor whose generic point maps off the support of a `ℚ`-Cartier divisor has
coefficient zero in its pull-back. -/
theorem qdivisor_coeff_eq_zero_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B : QDivisor Y}
    (hBq : B.IsQCartier)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {B' : QDivisor X} (h : B.IsPullback f hB B') (E : Mori.PrimeDivisor X)
    (hE : f E.genericPoint ∉ B.supp) : B'.coeff E = 0 := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hBq.exists_pos
  obtain ⟨D', hD', hp⟩ := h m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have h0 := divisor_coeff_eq_zero_of_isPullback hDc hp E (by
    rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD])
  have := congrArg (fun G : QDivisor X => G.coeff E) hD'
  simp only [Divisor.coeff_toQDivisor, h0, DivisorWithCoeffs.coeff_smul, Int.cast_zero] at this
  exact (smul_eq_zero.mp this.symm).resolve_left hm'

/-- The pull-back predicate depends only on the morphism. -/
private theorem qdivisor_isPullback_of_hom_eq {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f g : X ⟶ Y} (h : f = g) {B : QDivisor Y}
    {hf : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ B.supp}
    {hg : ∀ W : irreducibleComponents X, g (componentGenericPoint X W) ∉ B.supp}
    {R : QDivisor X} (H : B.IsPullback f hf R) : B.IsPullback g hg R := by
  subst h; exact H

/-- A closed immersion of an irreducible scheme onto the support of a prime divisor maps the
generic point to the generic point of the divisor. -/
private theorem map_genericPoint_eq {X T : Scheme.{u}} (j : T ⟶ X) [IsClosedImmersion j]
    [IrreducibleSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X)) :
    j (genericPoint T) = P.genericPoint := by
  have h1 : IsGenericPoint (j (genericPoint T)) (P.support : Set X) := by
    have := (genericPoint_spec T).image j.base.hom.continuous
    rwa [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP] at this
  have h2 : IsGenericPoint P.genericPoint (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  exact h1.eq h2

/-- The generic point of a prime divisor `P` lies off the support of a divisor in which `P` has
coefficient zero. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X]
    {G : DivisorWithCoeffs R X} {P : Mori.PrimeDivisor X} (hG : G.coeff P = 0) :
    P.genericPoint ∉ G.supp := by
  intro h
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem
  exact hE hG

/-- The generic point of an integral scheme lies off the support of every divisor. -/
private theorem genericPoint_notMem_supp {R : Type*} [Zero R] {X : Scheme.{u}}
    [IsIntegral X] (G : DivisorWithCoeffs R X) : genericPoint X ∉ G.supp := by
  intro h
  obtain ⟨E, -, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hmem
  have heq : E.genericPoint = genericPoint X :=
    (hmem.antisymm (genericPoint_specializes _)).eq
  have h1 := E.coheight_genericPoint
  rw [heq, Order.coheight_eq_zero.mpr fun b _ => genericPoint_specializes b] at h1
  exact absurd h1 (by decide)

/-- On a log resolution of `(X, B)`, a prime divisor lying over `Supp B` is smooth: it is a
component of the snc divisor `Ex(p) ∪ p⁻¹(Supp B)`. -/
private theorem smooth_comp_of_isLogResolution {X Y T' : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] {B : QDivisor X} (p : Y ⟶ X)
    [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] [LocallyOfFiniteType (p ≫ sX)]
    (hlog : Fourfold.IsLogResolution sX B p) (j' : T' ⟶ Y) [IsClosedImmersion j'] [IsReduced T']
    (P' : Mori.PrimeDivisor Y) (hP' : Set.range j'.base = (P'.support : Set Y))
    (hsupp : p P'.genericPoint ∈ (QDivisor.toRDivisor B).supp) : Smooth (j' ≫ p ≫ sX) := by
  classical
  have hmemS : P'.genericPoint ∈ ((exceptionalSet p ⊔
      (QDivisor.toRDivisor B).supp.preimage p.continuous : TopologicalSpace.Closeds Y) :
        Set Y) := by
    rw [TopologicalSpace.Closeds.coe_sup]
    exact Or.inr hsupp
  rcases hlog.isSNCSubset with hbot | ⟨s, hs, hsnc⟩
  · rw [hbot] at hmemS
    exact absurd hmemS (by simp)
  rw [← hs] at hmemS
  obtain ⟨E, hEs, hE⟩ := Set.mem_iUnion₂.mp hmemS
  obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hE
  have hcoef : E ∈ (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support := by
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hEs]
  have hsm := hsnc.1 E hcoef
  have : LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ p ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (f := E.idealSheaf.subschemeι ≫ p ≫ sX)).mpr inferInstance
  have hsm' : Smooth (E.idealSheaf.subschemeι ≫ p ≫ sX) := (isSmoothScheme_iff _).mp hsm
  have : IsReduced j'.ker.subscheme := isReduced_of_isOpenImmersion (asIso j'.toImage).inv
  have : IsIntegral E.idealSheaf.subscheme := E.integral
  have hker : j'.ker = E.idealSheaf := by
    rw [← MMP.Mori.vanishingIdeal_support_eq_self j'.ker,
      ← MMP.Mori.vanishingIdeal_support_eq_self E.idealSheaf]
    congr 1
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker, j'.isClosedEmbedding.isClosed_range.closure_eq, hP']
  rw [← hker] at hsm'
  rw [← j'.toImage_imageι, Category.assoc]
  exact inferInstance

/-- If `ord_P τ = -1` and `coeff_P B = 0`, then the generic point of each component of `T` maps
off `Supp (div τ + P + B)`. -/
private theorem genericPoint_notMem_supp_add_single {X T : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] (P : Mori.PrimeDivisor X)
    (hP : Set.range j.base = (P.support : Set X)) (B : QDivisor X) (hBP : B.coeff P = 0)
    (τ : RationalPluriForms sX (n + 1) 1)
    (hτ : P.ordForm τ = -1) (Z : irreducibleComponents T) :
    j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp := by
  intro hZ
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
  have hPgp : P.genericPoint ∈ Set.range j.base := by
    rw [hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨t, ht⟩ := hPgp
  have hZu : Z.1 = Set.univ := by
    have h' := Z.2
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h'
    exact h'
  have hsp : componentGenericPoint T Z ⤳ t :=
    (isGenericPoint_componentGenericPoint T Z).specializes (by rw [hZu]; trivial)
  have hPE : P.genericPoint ∈ E.support := by
    rw [← ht]
    have hcl : IsClosed E.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
    exact (hsp.map j.base.hom.continuous).mem_closed hcl hmem
  have hEP : E = P := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hPE
  subst hEP
  apply hE
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hBP,
    DivisorWithCoeffs.coeff_single_self, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτ]
  norm_num

/-- Compatibility of the different with a log resolution `p` of `(X, P + B)`: with `j' : T' ⟶ Y`
the strict transform of `P`, `ρ'` a residue of `p^*τ` and `p^*D = div(p^*τ) + Γ`, the restriction
`(Γ - P')|_{T'}` exists and `q^*(D|_T) = div ρ' + (Γ - P')|_{T'}`. -/
private theorem isPullback_residue_of_isLogResolution
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (B : QDivisor X) (hBP : B.coeff P = 0)
    (τ : RationalPluriForms sX (n + 1) 1) (hτ : P.ordForm τ = -1)
    (hD : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsQCartier)
    (hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp)
    (R₀ : QDivisor T)
    (hR₀ : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen R₀) :
      ∀ {Y T' : Scheme.{0}} (p : Y ⟶ X) [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
        [CompactSpace Y] [LocallyOfFiniteType (p ≫ sX)] [IsDominant p],
        Fourfold.IsLogResolution sX (Finsupp.single P 1 + B) p →
        ∀ (j' : T' ⟶ Y) [IsClosedImmersion j'] [IsIntegral T'] [IsNormal T']
          [IsLocallyNoetherian T'] [CompactSpace T'] (P' : Mori.PrimeDivisor Y),
          Set.range j'.base = (P'.support : Set Y) → p P'.genericPoint = P.genericPoint →
        ∀ (q : T' ⟶ T), q ≫ j = j' ≫ p →
        ∀ (ρ' : RationalPluriForms (j' ≫ p ≫ sX) n 1),
          IsPoincareResidue (p ≫ sX) j' n 1 (pullbackRationalPluriForms sX p τ) ρ' →
        ∀ (Γ : QDivisor Y),
          (∃ hgenY : ∀ Z : irreducibleComponents Y, p (componentGenericPoint Y Z) ∉
              (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp,
            (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback p hgenY
              (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX p τ)) + Γ)) →
        ∃ R : QDivisor T',
          (∃ hgen' : ∀ Z : irreducibleComponents T', j' (componentGenericPoint T' Z) ∉
              (Γ - Finsupp.single P' 1).supp,
            (Γ - Finsupp.single P' 1).IsPullback j' hgen' R) ∧
          ∃ hq : ∀ Z : irreducibleComponents T', q (componentGenericPoint T' Z) ∉ R₀.supp,
            R₀.IsPullback q hq (Divisor.toQDivisor (divisorOfForm ρ') + R) := by
  intro Y T' p _ _ _ _ _ _ hlog j' _ _ _ _ _ P' hP' hpP q hq ρ' hρ' Γ hΓex
  obtain ⟨hgenY, hΓ⟩ := hΓex
  classical
  set D := Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B
  have hjT : j (genericPoint T) = P.genericPoint := map_genericPoint_eq j P hP
  have hj'T : j' (genericPoint T') = P'.genericPoint := map_genericPoint_eq j' P' hP'
  have hPD : P.genericPoint ∉ D.supp := by
    have := hgen (pointComponent (genericPoint T))
    rwa [componentGenericPoint_eq_genericPoint, hjT] at this
  have hcgp' : ∀ Z : irreducibleComponents T', j' (componentGenericPoint T' Z) = P'.genericPoint :=
    fun Z => by rw [componentGenericPoint_eq_genericPoint, hj'T]
  have hsmY' : IsSmoothScheme (p ≫ sX) := hlog.isSmoothScheme
  have : LocallyOfFinitePresentation (p ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := p ≫ sX)).mpr inferInstance
  have : Smooth (p ≫ sX) := (isSmoothScheme_iff _).mp hsmY'
  have : IsProper p := hlog.isProper
  have : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  have hYvar : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := ⟨⟩
  have hbij := hlog.isBirationalMorphism.functionFieldMap_bijective
  have : ValuationRing (X.presheaf.stalk (p P'.genericPoint)) := by
    have := P.isDiscreteValuationRing_localRing
    rw [hpP]; infer_instance
  have : IsIso (p.stalkMap P'.genericPoint) :=
    MMP.Positivity.isIso_stalkMap_of_valuationRing p hbij _
  have hd : (letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat) = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  set τ' := pullbackRationalPluriForms sX p τ
  have hτ' : P'.ordForm τ' = -1 :=
    (MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hbij hd P' P hpP τ).trans hτ
  have hτ'0 : τ' ≠ 0 := fun h => by
    rw [h, PrimeDivisor.ordForm_zero] at hτ'; exact absurd hτ' (by decide)
  have hYdim : topologicalKrullDim Y = n + 1 := by
    rw [topologicalKrullDim_eq_toNat_trdeg (p ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX p hbij, hd]
    norm_cast
  have hPsupp : P.genericPoint ∈ (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hsupp : p P'.genericPoint ∈ (QDivisor.toRDivisor (Finsupp.single P 1 + B)).supp := by
    rw [hpP, DivisorWithCoeffs.mem_supp_iff]
    refine ⟨P, ?_, hPsupp⟩
    rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_add, hBP,
      DivisorWithCoeffs.coeff_single_self]
    norm_num
  have : Smooth (j' ≫ p ≫ sX) := smooth_comp_of_isLogResolution sX p hlog j' P' hP' hsupp
  have hGP' := qdivisor_coeff_eq_zero_of_isPullback hD hΓ P' (by rw [hpP]; exact hPD)
  have hGgen : ∀ Z : irreducibleComponents T', j' (componentGenericPoint T' Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ') + Γ).supp :=
    fun Z => by rw [hcgp']; exact genericPoint_notMem_supp_of_coeff_eq_zero hGP'
  obtain ⟨-, -, hadj⟩ := isPullback_divisorOfForm_add_of_isPoincareResidue (p ≫ sX) hYvar hYdim
    j' P' hP' τ' hτ'0 hτ' ρ' hρ'
  obtain ⟨R, hR, hGpull⟩ := hadj _ Γ (isQCartier_of_isSmoothScheme hsmY' _) hGgen rfl
  refine ⟨R, hR, ?_⟩
  have h2 : ∀ Z : irreducibleComponents T', (j' ≫ p) (componentGenericPoint T' Z) ∉ D.supp :=
    fun Z => by
      change p (j' (componentGenericPoint T' Z)) ∉ D.supp
      rw [hcgp', hpP]; exact hPD
  have hpath2 := hΓ.comp hGpull h2
  have hqT : q (genericPoint T') = genericPoint T := by
    apply j.isClosedEmbedding.injective
    change (q ≫ j) (genericPoint T') = j (genericPoint T)
    rw [hq]
    change p (j' (genericPoint T')) = _
    rw [hj'T, hpP, hjT]
  have hqgen : ∀ Z : irreducibleComponents T', q (componentGenericPoint T' Z) ∉ R₀.supp :=
    fun Z => by
      rw [componentGenericPoint_eq_genericPoint, hqT]; exact genericPoint_notMem_supp R₀
  obtain ⟨R₁, hR₁, -⟩ := (hR₀.isQCartier hD).existsUnique_isPullback hqgen
  have h1 : ∀ Z : irreducibleComponents T', (q ≫ j) (componentGenericPoint T' Z) ∉ D.supp := by
    rw [hq]; exact h2
  have hpath1 := qdivisor_isPullback_of_hom_eq hq (hg := h2) (hR₀.comp hR₁ h1)
  have hR₁eq : R₁ = Divisor.toQDivisor (divisorOfForm ρ') + R :=
    (hD.existsUnique_isPullback h2).unique hpath1 hpath2
  exact ⟨hqgen, hR₁eq ▸ hR₁⟩

/-- **Effective residue adjunction on a normal prime divisor.** Let `X` be a normal complex
variety of dimension `n + 1`, `j : T ⟶ X` the inclusion of a normal prime divisor `P`, and `B` an
effective `ℚ`-divisor with `coeff_P B = 0`. Let `τ` be a rational top form with `ord_P τ = -1` and
`ρ` its Poincaré residue along `T` (`MMP.Fourfold.IsPoincareResidue`), and suppose
`D = div(τ) + P + B` is `ℚ`-Cartier. Then there is an effective `ℚ`-divisor `B_S` on `T` with
`div(ρ) + B_S = D|_T`, and for every log resolution `p : Y ⟶ X` of `(X, P + B)`, strict transform
`j' : T' ⟶ Y` of `P` with induced `q : T' ⟶ T`, residue `ρ'` of `p^*τ` along `T'` and
`Γ = p^*D - div(p^*τ)`, one has `div(ρ') + (Γ - P')|_{T'} = q^*(div(ρ) + B_S)`. -/
@[mmp "lem_fourfold_normal_prime_effective_residue_adjunction"]
theorem exists_isEffective_isPullback_divisorOfForm_isPoincareResidue
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (B : QDivisor X) (hB : B.IsEffective) (hBP : B.coeff P = 0)
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (hD : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsQCartier) :
    ∃ BS : QDivisor T, BS.IsEffective ∧
      (∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
          (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp,
        (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen
          (Divisor.toQDivisor (divisorOfForm ρ) + BS)) ∧
      ∀ {Y T' : Scheme.{0}} (p : Y ⟶ X) [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
        [CompactSpace Y] [LocallyOfFiniteType (p ≫ sX)] [IsDominant p],
        IsLogResolution sX (Finsupp.single P 1 + B) p →
        ∀ (j' : T' ⟶ Y) [IsClosedImmersion j'] [IsIntegral T'] [IsNormal T']
          [IsLocallyNoetherian T'] [CompactSpace T'] (P' : Mori.PrimeDivisor Y),
          Set.range j'.base = (P'.support : Set Y) → p P'.genericPoint = P.genericPoint →
        ∀ (q : T' ⟶ T), q ≫ j = j' ≫ p →
        ∀ (ρ' : RationalPluriForms (j' ≫ p ≫ sX) n 1),
          IsPoincareResidue (p ≫ sX) j' n 1 (pullbackRationalPluriForms sX p τ) ρ' →
        ∀ (Γ : QDivisor Y),
          (∃ hgenY : ∀ Z : irreducibleComponents Y, p (componentGenericPoint Y Z) ∉
              (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp,
            (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback p hgenY
              (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX p τ)) + Γ)) →
        ∃ R : QDivisor T',
          (∃ hgen' : ∀ Z : irreducibleComponents T', j' (componentGenericPoint T' Z) ∉
              (Γ - Finsupp.single P' 1).supp,
            (Γ - Finsupp.single P' 1).IsPullback j' hgen' R) ∧
          ∃ hq : ∀ Z : irreducibleComponents T', q (componentGenericPoint T' Z) ∉
              (Divisor.toQDivisor (divisorOfForm ρ) + BS).supp,
            (Divisor.toQDivisor (divisorOfForm ρ) + BS).IsPullback q hq
              (Divisor.toQDivisor (divisorOfForm ρ') + R) := by
  have hgen := genericPoint_notMem_supp_add_single j P hP B hBP τ hτ
  obtain ⟨R₀, hR₀, -⟩ := hD.existsUnique_isPullback hgen
  have hBS : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen
      (Divisor.toQDivisor (divisorOfForm ρ) + (R₀ - Divisor.toQDivisor (divisorOfForm ρ))) := by
    rwa [add_sub_cancel]
  exact ⟨_, fun Q => coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue sX hX hdim j hT
      P hP B hB hBP τ hτ0 hτ ρ hρ hD _ hgen hBS Q, ⟨hgen, hBS⟩,
    isPullback_residue_of_isLogResolution sX hX hdim j P hP B hBP τ hτ hD hgen _ hBS⟩

end MMP.Fourfold
