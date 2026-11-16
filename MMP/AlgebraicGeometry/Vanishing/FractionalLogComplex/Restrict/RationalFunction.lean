module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Restrict.Data
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts

/-!
# Restriction of a rational function to an open integral piece

Let `X` be a locally Noetherian normal scheme, `U` an open of `X` and `ψ` a unit of the ring of
rational functions `K(X)`. When the generic points of the components of `U` lie off
`Supp div ψ` (for instance when `U` is integral), `ψ` pulls back along `U ⟶ X` to a unit `ψ_U`
of `K(U)`, `MMP.Mori.pullbackRationalFunction U.ι ψ`. Its divisor is the restriction of
`div ψ`: the order of `ψ_U` along a prime divisor `E` of `U` is the order of `ψ` along the prime
divisor of `X` with the same generic point, since `U ⟶ X` induces an isomorphism of the
discrete valuation rings along them.

Consequently the root datum `N M = B + div ψ` restricts to `U`, and a regular function `u` on
`U' = X ∖ (D ∪ Supp M)` whose germs at the generic points are those of `ψ` restricts to a
regular function on `U' ∩ U` whose germs are those of `ψ_U`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.ι_componentGenericPoint_notMem_supp`: on an integral
  open `U`, the generic point lies off the support of every divisor of `X`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.principalDivisor_pullbackRationalFunction_ι`:
  `div ψ_U = (div ψ)|_U`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.zsmul_restrictDivisor_eq_add_principalDivisor`:
  `N M|_U = B|_U + div ψ_U`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.toRationalFunctionsPresheaf_restrictSection`: the
  restriction of `u` has the germs of `ψ_U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

open MMP.Mori

universe u

variable {X : Scheme.{u}} (U : X.Opens)

/-- On an integral open `U` of `X`, the generic point of every component of `U` maps off the
support of every divisor of `X`. -/
theorem ι_componentGenericPoint_notMem_supp [IsIntegral U.toScheme] {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R X) (Z : irreducibleComponents U.toScheme) :
    U.ι (componentGenericPoint U.toScheme Z) ∉ D.supp := by
  rw [← mem_supp_restrictDivisor_iff, MMP.Fourfold.componentGenericPoint_eq_genericPoint]
  exact MMP.Fourfold.genericPoint_notMem_supp _

variable [IsLocallyNoetherian X] [IsNormal X]

omit [IsLocallyNoetherian X] in
/-- The generic point of the component of a prime divisor `E` of `U` lies, in `X`, on the
component of the prime divisor of `X` with the generic point of `E`. -/
theorem ι_componentGenericPoint_mem_component (E : MMP.Mori.PrimeDivisor U) :
    U.ι (componentGenericPoint U.toScheme E.component) ∈
      (primeDivisorOfOpens U E).component.1 := by
  have sp : U.ι (componentGenericPoint U.toScheme E.component) ⤳
      (primeDivisorOfOpens U E).genericPoint := by
    rw [genericPoint_primeDivisorOfOpens]
    exact U.ι.base.hom.map_specializes E.specializes_genericPoint
  have hW := mem_pointComponent (U.ι (componentGenericPoint U.toScheme E.component))
  have hP : (primeDivisorOfOpens U E).genericPoint ∈ (pointComponent
      (U.ι (componentGenericPoint U.toScheme E.component))).1 :=
    sp.mem_closed (isClosed_of_mem_irreducibleComponents _ (pointComponent _).2) hW
  rwa [eq_of_mem_irreducibleComponents hP (primeDivisorOfOpens U E).genericPoint_mem_component]
    at hW

/-- **The divisor of the restriction is the restriction of the divisor**: for `ψ ∈ K(X)^×` whose
divisor misses the generic points of the components of the open `U`,
`div (ψ|_U) = (div ψ)|_U`. -/
theorem principalDivisor_pullbackRationalFunction_ι [CompactSpace X] [CompactSpace U.toScheme]
    (ψ : (RationalFunctions X)ˣ)
    (hφ : ∀ Z : irreducibleComponents U.toScheme,
      U.ι (componentGenericPoint U.toScheme Z) ∉ (principalDivisor ψ).supp) :
    principalDivisor (pullbackRationalFunction U.ι ψ hφ) =
      restrictDivisor U (principalDivisor ψ) := by
  ext E
  change E.ord _ = (primeDivisorOfOpens U E).ord ψ
  have hW := ι_componentGenericPoint_mem_component U E
  obtain ⟨a, ha⟩ := (Divisor.isLocalEquation_principalDivisor ψ ⊤).exists_unit_stalk
    (U := ⊤) trivial (hφ E.component) hW
  have hcomp : Units.map (RationalFunctions.component U.toScheme E.component).toMonoidHom
      (pullbackRationalFunction U.ι ψ hφ) = pullbackComponent U.ι hφ
        (Divisor.isLocalEquation_principalDivisor ψ ⊤) E.component trivial := by
    ext; rfl
  rw [PrimeDivisor.ord_eq_ordUnit, hcomp, pullbackComponent_eq hφ
    (Divisor.isLocalEquation_principalDivisor ψ ⊤) trivial hW a ha]
  have : IsIso (U.ι.stalkMap E.genericPoint) :=
    IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι _
  exact MMP.Positivity.ordUnit_stalkMap_eq_ord E (primeDivisorOfOpens U E)
    (genericPoint_primeDivisorOfOpens U E).symm ψ hW a ha

/-- **The root datum restricts**: `N M = B + div ψ` gives `N M|_U = B|_U + div (ψ|_U)`. -/
theorem zsmul_restrictDivisor_eq_add_principalDivisor [CompactSpace X] [CompactSpace U.toScheme]
    {N : ℕ} {M Bn : Divisor X} {ψ : (RationalFunctions X)ˣ}
    (hψ : (N : ℤ) • M = Bn + principalDivisor ψ)
    (hφ : ∀ Z : irreducibleComponents U.toScheme,
      U.ι (componentGenericPoint U.toScheme Z) ∉ (principalDivisor ψ).supp) :
    (N : ℤ) • restrictDivisor U M =
      restrictDivisor U Bn + principalDivisor (pullbackRationalFunction U.ι ψ hφ) := by
  rw [principalDivisor_pullbackRationalFunction_ι, ← restrictDivisor_zsmul, ← restrictDivisor_add,
    hψ]

/-- **The function `u` restricts**: if the regular function `u` on `U' = X ∖ (D ∪ Supp M)` has
the germs of `ψ` at the generic points of the components meeting `U'`, then its restriction to
`U' ∩ U` has the germs of `ψ|_U`. -/
theorem toRationalFunctionsPresheaf_restrictSection [CompactSpace X] (D M : Divisor X)
    (ψ : (RationalFunctions X)ˣ)
    (hφ : ∀ Z : irreducibleComponents U.toScheme,
      U.ι (componentGenericPoint U.toScheme Z) ∉ (principalDivisor ψ).supp)
    (u : Γ(X, cU' D M))
    (hu : (toRationalFunctionsPresheaf X).app (op (cU' D M)) u =
      (rationalFunctionsPresheaf X).map (homOfLE le_top).op
        ((rationalFunctionsPresheafTopEquiv X).symm ψ)) :
    (toRationalFunctionsPresheaf U.toScheme).app
        (op (cU' (restrictDivisor U D) (restrictDivisor U M))) (restrictSection U D M u) =
      (rationalFunctionsPresheaf U.toScheme).map (homOfLE le_top).op
        ((rationalFunctionsPresheafTopEquiv U.toScheme).symm
          (pullbackRationalFunction U.ι ψ hφ)) := by
  funext Z
  obtain ⟨Z, hZ⟩ := Z
  have hy : U.ι (componentGenericPoint U.toScheme Z) ∈ cU' D M := by
    rwa [cU'_restrictDivisor] at hZ
  set y := U.ι (componentGenericPoint U.toScheme Z)
  set W := pointComponent y
  have hyW : y ∈ W.1 := mem_pointComponent y
  obtain ⟨a, ha⟩ := (Divisor.isLocalEquation_principalDivisor ψ ⊤).exists_unit_stalk
    (U := ⊤) trivial (hφ Z) hyW
  have hWU' : componentGenericPoint X W ∈ cU' D M :=
    ((isGenericPoint_componentGenericPoint X W).specializes hyW).mem_open (cU' D M).isOpen hy
  have hau : (a : X.presheaf.stalk y) = (X.presheaf.germ (cU' D M) y hy).hom u := by
    apply stalkToRationalFunctions_injective hyW
    have h1 : (X.presheaf.germ (cU' D M) (componentGenericPoint X W) hWU').hom u =
        (ψ : RationalFunctions X) W := congrFun hu ⟨W, hWU'⟩
    rw [ha, ← h1]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  have hR : (rationalFunctionsPresheaf U.toScheme).map (homOfLE le_top).op
      ((rationalFunctionsPresheafTopEquiv U.toScheme).symm
        (pullbackRationalFunction U.ι ψ hφ)) ⟨Z, hZ⟩ =
      ((pullbackComponent U.ι hφ (Divisor.isLocalEquation_principalDivisor ψ ⊤) Z trivial :
        (U.toScheme.presheaf.stalk (componentGenericPoint U.toScheme Z))ˣ) :
          U.toScheme.presheaf.stalk (componentGenericPoint U.toScheme Z)) := rfl
  rw [hR, pullbackComponent_eq hφ (Divisor.isLocalEquation_principalDivisor ψ ⊤) trivial hyW a ha]
  change (U.toScheme.presheaf.germ _ _ hZ).hom (restrictSection U D M u) =
    (U.ι.stalkMap _).hom (a : X.presheaf.stalk y)
  rw [hau, Scheme.Hom.germ_stalkMap_apply, restrictSection,
    TopCat.Presheaf.germ_res_apply]

end MMP.FourfoldProofs.FractionalLogComplexProof
