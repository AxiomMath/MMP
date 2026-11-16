module

public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf

/-!
# A rational function and its regular representatives

On an integral scheme `X`, a rational function `φ ∈ K(X)` whose restriction to a non-empty open
`U` is the image of a section `a ∈ Γ(X, U)` is, read in the function field of `X`, the germ of `a`
at the generic point: `MMP.Mori.rationalFunctionsEquivFunctionField X φ = germ a`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.rationalFunctionsEquivFunctionField_eq_germ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

/-- On an integral scheme, if the restriction of a rational function `φ` to a non-empty open `U`
is the image of a section `a ∈ Γ(X, U)`, then `φ`, read in the function field of `X`, is the
germ of `a` at the generic point. -/
theorem rationalFunctionsEquivFunctionField_eq_germ {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    [Nonempty U] (φ : MMP.Mori.RationalFunctions X) (a : Γ(X, U))
    (h : (MMP.Mori.toRationalFunctionsPresheaf X).app (op U) a =
      (MMP.Mori.rationalFunctionsPresheaf X).map (homOfLE le_top).op
        ((MMP.Mori.rationalFunctionsPresheafTopEquiv X).symm φ)) :
    MMP.Mori.rationalFunctionsEquivFunctionField X φ = X.germToFunctionField U a := by
  obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty U›
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  let Ud : Stacks.Chow.DenseOpen X := ⟨U, U.isOpen.dense ⟨x, hx⟩⟩
  have hmem : ∀ Z : irreducibleComponents X, MMP.Mori.componentGenericPoint X Z ∈ U := by
    intro Z
    have hZ : (Z : Set X) ∈ ({Set.univ} : Set (Set X)) :=
      irreducibleComponents_eq_singleton (X := X) ▸ Z.2
    exact (MMP.Mori.genericPoint_mem_iff Z U).2 ⟨x, hx, by simp_all⟩
  have hφ : φ = MMP.Mori.rationalFunctionsEquivStalks X (Stacks.Chow.ofSection X Ud a) := by
    funext Z
    have h1 := congrFun h ⟨Z, hmem Z⟩
    rw [MMP.Mori.toRationalFunctionsPresheaf_app_apply] at h1
    refine (h1.symm.trans ?_).trans
      ((Stacks.Chow.rationalFunctionsEquivStalks X).2 Ud a Z (hmem Z)).symm
    rfl
  rw [hφ]
  change (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
    ((MMP.Mori.rationalFunctionsEquivStalks X).symm
      (MMP.Mori.rationalFunctionsEquivStalks X (Stacks.Chow.ofSection X Ud a))) = _
  rw [RingEquiv.symm_apply_apply]
  exact (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 Ud a
    ((genericPoint_spec X).mem_open_set_iff U.isOpen |>.2 ⟨x, trivial, hx⟩)

end MMP.FourfoldProofs.FractionalLogComplexProof
