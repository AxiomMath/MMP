/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.NormalizedDualizingComplexNagataCharts
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedProper
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.NormalizedStalksOfClosedPoints
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.VanishingAndSupport
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingComplexNagata
public import StacksFrontier.RingTheory.Dualizing.CanonicalModuleDepth

/-!
# The normalized dualizing complex of a scheme of finite type over a field

For `X` Noetherian and of finite type over a field `k` (no separatedness or properness), the
dualizing complex `K_X` normalized relative to `k[0]` (Stacks, Tag 0AUA,
`Stacks.Duality.normalizedDualizingComplex`) is a dualizing complex with coherent cohomology; if
`X` is of pure dimension `d` its cohomology lives in degrees `-d, …, 0`, and at every point `x`,
with `e = trdeg_k κ(x)` and `h = dim 𝒪_{X,x}` (so `e + h = d`), there is a normalized dualizing
complex `D_x` over `𝒪_{X,x}` with `H^i(K_X)_x ≅ H^{i+e}(D_x)`; in particular
`(H^{-d}K_X)_x ≅ H^{-h}(D_x)`, which has depth at least `min(h, 2)`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Stacks.Duality

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

namespace MMP.Flips

variable {k : Type u} [Field k] {X : Scheme.{u}}

private theorem isField_stalk_spec_of_field (s : Spec (.of k)) :
    IsField ((Spec (.of k)).presheaf.stalk s) := by
  refine isField_stalk_of_closure_mem_irreducibleComponents (X := Spec (.of k)) s ?_
  have h1 : closure ({s} : Set (Spec (.of k))) = Set.univ := by
    rw [(isClosed_singleton : IsClosed ({s} : Set (Spec (.of k)))).closure_eq]
    exact Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  rw [h1, irreducibleComponents_eq_singleton]
  rfl

private def unitStalkEquivSchemeStalk (X : Scheme.{u}) (x : X) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (schemeStalkModuleFunctor x).obj (Stacks.UnitStalk.unitModule X) :=
  LinearEquiv.ofBijective
    { toFun := fun r => stalkLinearEquivSchemeStalk (Stacks.UnitStalk.unitModule X) x
        (Stacks.UnitStalk.unitStalkLinearEquiv X x r)
      map_add' := fun r r' => by
        rw [map_add]
        exact map_add (stalkLinearEquivSchemeStalk (Stacks.UnitStalk.unitModule X) x) _ _
      map_smul' := by
        intro r m
        obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
        obtain ⟨V, hV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf m
        have ea : X.presheaf.germ U x hU a = X.presheaf.germ (U ⊓ V) x ⟨hU, hV⟩
            (X.presheaf.map (homOfLE inf_le_left).op a) :=
          (X.presheaf.germ_res_apply _ _ _ _).symm
        have eb : X.presheaf.germ V x hV b = X.presheaf.germ (U ⊓ V) x ⟨hU, hV⟩
            (X.presheaf.map (homOfLE inf_le_right).op b) :=
          (X.presheaf.germ_res_apply _ _ _ _).symm
        rw [ea, eb]
        have key : ∀ (W : TopologicalSpace.Opens X) (hW : x ∈ W) (p q : Γ(X, W)),
            stalkLinearEquivSchemeStalk (Stacks.UnitStalk.unitModule X) x
              (Stacks.UnitStalk.unitStalkLinearEquiv X x
                (X.presheaf.germ W x hW p • X.presheaf.germ W x hW q)) =
            X.presheaf.germ W x hW p •
              stalkLinearEquivSchemeStalk (Stacks.UnitStalk.unitModule X) x
                (Stacks.UnitStalk.unitStalkLinearEquiv X x (X.presheaf.germ W x hW q)) := by
          intro W hW p q
          rw [smul_eq_mul, ← map_mul, Stacks.UnitStalk.unitStalkLinearEquiv_germ,
            Stacks.UnitStalk.unitStalkLinearEquiv_germ]
          exact schemeStalkModuleFunctor_germ_smul x (Stacks.UnitStalk.unitModule X) W hW p q
        simp only [RingHom.id_apply]
        exact key _ _ _ _ }
    ((stalkLinearEquivSchemeStalk (Stacks.UnitStalk.unitModule X) x).bijective.comp
      (Stacks.UnitStalk.unitStalkLinearEquiv X x).bijective)

private theorem exists_normalized_stalk_structureSheaf (s : Spec (.of k)) :
    ∃ E : CochainComplex (Spec (.of k)).Modules ℤ,
      Nonempty (DerivedCategory.Q.obj E ≅ (derivedStructureSheafPlus (Spec (.of k))).obj.obj) ∧
      _root_.Dualizing.IsNormalizedDualizingComplex.{u, u}
        (@derivedStalkOfComplex (Spec (.of k)) s (HasDerivedCategory.standard _) E) := by
  let := (isNoetherian_spec_of_field k)
  have hf := isField_stalk_spec_of_field (k := k) s
  have : IsNoetherianRing ((Spec (.of k)).presheaf.stalk s) := by
    let := hf.toField
    infer_instance
  refine ⟨(CochainComplex.singleFunctor _ 0).obj (Stacks.UnitStalk.unitModule _), ⟨?_⟩, ?_⟩
  · exact (DerivedCategory.singleFunctorIsoCompQ (Spec (.of k)).Modules 0).symm.app _
  · have eN : (schemeStalkModuleFunctor s).obj (Stacks.UnitStalk.unitModule (Spec (.of k))) ≅
        ModuleCat.of _ ((Spec (.of k)).presheaf.stalk s) :=
      LinearEquiv.toModuleIso
        (unitStalkEquivSchemeStalk _ s).symm
    have h := Dualizing.isNormalizedDualizingComplex_single_self_of_isField hf
    refine (Dualizing.isNormalizedDualizingComplex_congr.{u, u} ?_).mpr h
    letI := HasDerivedCategory.standard (ModuleCat.{u} ((Spec (.of k)).presheaf.stalk s))
    exact DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (schemeStalkModuleFunctor s)
          (ComplexShape.up ℤ) 0).app _) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ
        (ModuleCat.{u} ((Spec (.of k)).presheaf.stalk s)) 0).symm.app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eN

/-- A scheme `X` that is Noetherian and of finite type over a field is of finite type over a
Noetherian base, in the sense of `Stacks.Duality.IsFiniteTypeOverNoetherian`. -/
theorem isFiniteTypeOverNoetherian_of_field [IsNoetherian X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] : IsFiniteTypeOverNoetherian π := by
  have : CompactSpace X := inferInstance
  have : QuasiCompact π := inferInstance
  exact Stacks.Duality.isFiniteTypeOverNoetherian_of_field π

/-- The dualizing complex `K_X = π^! k` of `X` normalized relative to `k[0]`. -/
abbrev normalizedDualizingComplexOverField [IsNoetherian X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] :=
  normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field π)
    (derivedStructureSheafPlus (Spec (.of k)))
    (isDualizingComplex_derivedStructureSheafPlus_of_field k)

/-- **The normalized dualizing complex and its local canonical modules over a field.** Let `X` be
Noetherian and of finite type over a field `k` (structure map `π`), with no separatedness or
properness assumption. Its dualizing complex `K_X` normalized relative to `k[0]` exists (it is
`normalizedDualizingComplexOverField π`) and has coherent cohomology. If `X` is pure of dimension
`d`, then `H^i(K_X) = 0` for `i < -d` and for `i > 0`, and at every point `x`, with
`e = trdeg_k κ(x)` and `h = dim 𝒪_{X,x}`, one has `e + h = d` and there is a normalized dualizing
complex `D_x` over `𝒪_{X,x}` with `H^i(K_X)_x ≅ H^{i+e}(D_x)` for all `i`; in particular
`(H^{-d}K_X)_x ≅ H^{-h}(D_x)`, and this module has depth at least `min(h, 2)`. -/
@[mmp "lem_mmp_foundation_normalized_dualizing_finite_type_field"]
theorem normalizedDualizingComplexOverField_spec [IsNoetherian X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] :
    haveI := (isFiniteTypeOverNoetherian_of_field π).source_noetherian
    let K := (normalizedDualizingComplexOverField π).complex.obj.obj
    IsDualizingComplex K ∧
      (∀ i : ℤ,
        _root_.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules i).obj K)) ∧
      ∀ d : ℕ, (∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) →
        (∀ i : ℤ, (i < -(d : ℤ) ∨ 0 < i) →
          Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) ∧
        ∀ x : X,
          letI : Algebra k (X.residueField x) :=
            ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ X.Γevaluation x).hom.toAlgebra
          ∃ (D : StandardDerivedCategory (X.presheaf.stalk x)) (e h : ℕ),
            _root_.Dualizing.IsNormalizedDualizingComplex.{u, u} D ∧
            Algebra.trdeg k (X.residueField x) = e ∧
            ringKrullDim (X.presheaf.stalk x) = h ∧ e + h = d ∧
            (∀ i : ℤ, Nonempty
              (moduleStalkAtPoint ((DerivedCategory.homologyFunctor X.Modules i).obj K) x
                ≃ₗ[X.presheaf.stalk x] standardHomology D (i + (e : ℤ)))) ∧
            min (h : ℕ∞) 2 ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal _)
              (moduleStalkAtPoint
                ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj K) x) := by
  have := (isFiniteTypeOverNoetherian_of_field π).source_noetherian
  intro K
  have hK : IsDualizingComplex K :=
    isDualizingComplex_normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field π)
      (derivedStructureSheafPlus (Spec (.of k)))
      (isDualizingComplex_derivedStructureSheafPlus_of_field k)
  have h0 : ∀ x : X, IsClosed ({x} : Set X) → associatedShiftFunction K x = 0 := by
    intro x hx
    have : IsLocallyNoetherian X := inferInstance
    refine (associatedShiftFunction_eq_zero_iff hK x).mpr fun E hE => ?_
    refine isNormalizedDualizingComplex_derivedStalkOfComplex_normalizedDualizingComplex
      (isFiniteTypeOverNoetherian_of_field π) (derivedStructureSheafPlus (Spec (.of k)))
      (isDualizingComplex_derivedStructureSheafPlus_of_field k) x hx ?_ E hE
    exact exists_normalized_stalk_structureSheaf _
  refine ⟨hK, fun i => isCoherent_homology_of_isDualizingComplex hK i, fun d hd => ?_⟩
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨fun i _ => isZero_of_isEmpty _, isEmptyElim⟩
  obtain ⟨hdim, hloc⟩ := hasNormalizedStalks_natDim hK h0
  have hdX : topologicalKrullDim X = (d : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_iSup_irreducibleComponents X]
    obtain ⟨x⟩ := hX
    obtain ⟨W, hW, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({x} : Set X) isIrreducible_singleton
    refine le_antisymm (iSup₂_le fun Z hZ => (hd Z hZ).le) ?_
    exact le_iSup₂_of_le W hW (hd W hW).ge
  have hnd : natDim X = d := by exact_mod_cast hdim.symm.trans hdX
  refine ⟨fun i hi => ?_, fun x => ?_⟩
  · by_contra hz
    have := mem_Icc_of_not_isZero_homology hloc i hz
    rw [hnd] at this
    rcases hi with hi | hi
    · exact absurd this.1 (not_le.mpr hi)
    · exact absurd this.2 (not_le.mpr hi)
  · let : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ X.Γevaluation x).hom.toAlgebra
    obtain ⟨L, e, h, hL, he, hh, hle, hiso⟩ := hloc.exists_normalized x
    have hat := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X π x
    have hcl := topologicalKrullDim_closure_singleton_eq_trdeg k X π x
    have hEq : TopologicalSpace.Equidimensional X := fun W hW Z hZ =>
      (hd W hW).trans (hd Z hZ).symm
    have hloc' := topologicalKrullDimAt_eq_of_equidimensional k X π hEq hdX x
    rw [he] at hcl
    have htr : Algebra.trdeg k (X.residueField x) = (e : Cardinal) := by
      rw [← Cardinal.toENat_eq_natCast]
      exact_mod_cast hcl.symm
    have hsum : e + h = d := by
      rw [hloc', htr, hh] at hat
      simp at hat
      exact_mod_cast hat.symm
    refine ⟨L, e, h, hL, htr, hh, hsum, hiso, ?_⟩
    obtain ⟨φ⟩ := hiso (-(d : ℤ))
    have hidx : (-(d : ℤ)) + (e : ℤ) = -(h : ℤ) := by omega
    rw [hidx] at φ
    rw [Module.depth_eq_depth_of_linearEquiv _ φ]
    exact _root_.Dualizing.min_two_le_depth_canonicalModule h L hL hh

end MMP.Flips
