module

public import MMP.AlgebraicGeometry.Curves.Maps.Charts

/-!
# Derivations of the charts of a curve map and sections of `f^* T_U ⊗ I`

Let `f : C ⟶ U` be a morphism of `k`-schemes with `U` smooth, `T_U = (Ω_{U/k})^∨` its tangent
sheaf and `I` the ideal sheaf of a closed subscheme of `C`. For affine opens `V ⊆ C` and `W ⊆ U`
with `f(V) ⊆ W`, a section `x` of `f^* T_U ⊗ I` over `V` contracts with the differentials:
`a ↦ x(d a)` is a derivation of `Γ(U, W)` with values in `Γ(I, V)`, and every derivation arises
from exactly one section. This combines the sections of a tensor product and of a pullback over
affine opens, the sections of a dual over an affine open, the affine computation of `Ω_{U/k}` and
`Γ(U, W) ⊗ Hom(P, Γ(U, W)) ⊗ J = Hom(P, J)` for a finite projective `P`. The identification is
compatible with restriction, which on derivations is the unique extension along the étale
restriction maps between the affine opens.

On the charts of a curve map (`MMP.Fourfold.CurveMapCharts.curveCharts`) this identifies the
presheaf of derivations of the charts with values in the ideals of the marked points with the
sections of `f^* T_U(-B)`. A second part counts first-order deformations on the charts: a linear
family of compatible derivations has an obstruction class in the Čech `H¹` of the structure sheaf,
and on its kernel the first-order local expressions glue, giving a space of first-order tuples
of dimension at least `dim - dim Ȟ¹(𝒪)`. The chart coordinates separate derivations, since two
maps into a ring agreeing on the ratios of the coordinates of a monomorphism into `ℙᵈ_k` agree.

## Main definitions

* `MMP.Fourfold.CurveMapDerivations.markedSectionsMap`: the contraction
  `Γ(V, f^* E^∨ ⊗ I) → Hom(Γ(E, W), Γ(I, V))`.
* `MMP.Fourfold.CurveMapDerivations.derivationOfHom`: the derivation `φ ∘ d` of a linear map out
  of `Γ(Ω_{X/k}, W)`.
* `MMP.Fourfold.CurveMapDerivations.dualPoint`, `MMP.Fourfold.CurveMapDerivations.dualFrame`: the
  first-order deformation `f0 + ε D` of a chart map and the frames `1 + ε φ`.
* `MMP.Fourfold.CurveMapDerivations.derivObstruction`: the obstruction cochain
  `(D(t_{ij}) / t_{ij})` of a compatible family of derivations.
* `MMP.Fourfold.CurveMapDerivations.dualNumberArtin`: `k[ε]` as a local Artinian `k`-algebra.

## Main results

* `MMP.Fourfold.CurveMapDerivations.markedSectionsMap_bijective`,
  `MMP.Fourfold.CurveMapDerivations.markedSectionsMap_res`: the contraction is bijective over
  affine opens and commutes with restriction.
* `MMP.Fourfold.CurveMapDerivations.derivationOfHom_bijective`: derivations of `Γ(X, W)` are the
  linear maps out of `Γ(Ω_{X/k}, W)` (Stacks 01UT).
* `MMP.Fourfold.CurveMapDerivations.exists_derivationMaps_curveCharts`,
  `MMP.Fourfold.CurveMapDerivations.exists_derivationEquiv_curveCharts`: the derivations of the
  curve charts with values in the ideals of the marked points are the sections of `f^* T_U ⊗ I`,
  compatibly with restriction.
* `MMP.Fourfold.CurveMapDerivations.isCocycle_derivObstruction`: the obstruction cochain is a
  cocycle.
* `MMP.Fourfold.CurveMapDerivations.exists_tangentSubspace_of_charts`: the first-order count.
* `MMP.Fourfold.CurveMapDerivations.algHom_ext_of_ratio`: the chart coordinates of a monomorphism
  into `ℙᵈ_k` separate maps of `k`-algebras.
* `MMP.Fourfold.CurveMapDerivations.finrank_le_finrank_cotangentSpace_of_values`: tangent
  vectors of a local `k`-algebra from `k[ε]`-points.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Kollár–Mori, *Birational geometry of algebraic varieties*, Theorem 1.10 and its proof]
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u v w

namespace MMP.Fourfold.CurveMapDerivations

section Algebra

variable (S : Type u) (O : Type v) (J : Type w) (P : Type u) [CommRing S] [CommRing O]
  [Algebra S O] [AddCommGroup J] [Module O J] [Module S J] [IsScalarTower S O J]
  [AddCommGroup P] [Module S P]

/-- The contraction `(O ⊗_S P^∨) ⊗_O J → Hom_S(P, J)`, `(c ⊗ λ) ⊗ y ↦ (p ↦ λ p • c • y)`, as an
`S`-linear map. -/
def baseChangeDualTensorHomAux : (O ⊗[S] Module.Dual S P) ⊗[O] J →ₗ[S] (P →ₗ[S] J) :=
  dualTensorHom S P J ∘ₗ (TensorProduct.comm S J (Module.Dual S P)).toLinearMap ∘ₗ
    ((AlgebraTensorModule.cancelBaseChange S O O J (Module.Dual S P)).restrictScalars
      S).toLinearMap ∘ₗ
    ((TensorProduct.comm O (O ⊗[S] Module.Dual S P) J).restrictScalars S).toLinearMap

/-- The contraction `baseChangeDualTensorHomAux` sends `(c ⊗ λ) ⊗ y` to `p ↦ λ p • c • y`. -/
theorem baseChangeDualTensorHomAux_tmul (c : O) (l : Module.Dual S P) (y : J) (p : P) :
    baseChangeDualTensorHomAux S O J P ((c ⊗ₜ[S] l) ⊗ₜ[O] y) p = l p • c • y := by
  simp [baseChangeDualTensorHomAux, dualTensorHom_apply]

/-- **The contraction `(O ⊗_S P^∨) ⊗_O J → Hom_S(P, J)`**, `(c ⊗ λ) ⊗ y ↦ (p ↦ λ p • c • y)`,
for an `S`-algebra `O`, an `S`-module `P` and an `O`-module `J`. -/
def baseChangeDualTensorHom : (O ⊗[S] Module.Dual S P) ⊗[O] J →ₗ[O] (P →ₗ[S] J) where
  toFun := baseChangeDualTensorHomAux S O J P
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul z y =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [add_tmul, smul_add, map_add, hz, hz']
      | tmul c' l =>
        ext p
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', baseChangeDualTensorHomAux_tmul]
        simp only [RingHom.id_apply, LinearMap.smul_apply, baseChangeDualTensorHomAux_tmul]
        rw [smul_eq_mul, mul_smul, smul_comm (l p) c]

/-- The contraction `baseChangeDualTensorHom` sends `(c ⊗ λ) ⊗ y` to `p ↦ λ p • c • y`. -/
theorem baseChangeDualTensorHom_tmul (c : O) (l : Module.Dual S P) (y : J) (p : P) :
    baseChangeDualTensorHom S O J P ((c ⊗ₜ[S] l) ⊗ₜ[O] y) p = l p • c • y :=
  baseChangeDualTensorHomAux_tmul S O J P c l y p

/-- For `P` finite projective over `S`, the contraction `(O ⊗_S P^∨) ⊗_O J → Hom_S(P, J)` is
bijective. -/
theorem baseChangeDualTensorHom_bijective [Module.Finite S P] [Module.Projective S P] :
    Function.Bijective (baseChangeDualTensorHom S O J P) := by
  change Function.Bijective (baseChangeDualTensorHomAux S O J P)
  unfold baseChangeDualTensorHomAux
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (dualTensorHom_bijective (R := S) (M := P) (N := J)).comp ((LinearEquiv.bijective _).comp
    ((LinearEquiv.bijective _).comp (LinearEquiv.bijective _)))

end Algebra

section Sections

open AlgebraicGeometry Opposite Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.AffineOpenTensorSections (tensorMod gammaTensorEquiv gammaTmul
  gammaTensorEquiv_tmul)

variable {C U : Scheme.{u}} (f : C ⟶ U) (E : U.Modules) (I : C.Modules)

/-- The sections of the dual `E^∨` over an affine open `W`, for `E` quasi-coherent, are the
`Γ(U, W)`-linear forms on `Γ(E, W)`. -/
def dualSectionsEquiv [E.IsQuasicoherent] {W : U.Opens} (hW : IsAffineOpen W) :
    Γ(dualSheaf E, W) ≃ₗ[Γ(U, W)] Module.Dual Γ(U, W) Γ(E, W) :=
  LinearEquiv.ofBijective
    (Stacks.Algebraization.internalHomEvaluation E
      (SheafOfModules.unit U.ringCatSheaf : U.Modules) W)
    (Stacks.Algebraization.internalHomEvaluation_bijective E _ ⟨W, hW⟩)

/-- `dualSectionsEquiv` sends a section `t` of `E^∨` to the linear form given by the dual pairing
with `t` over `W`. -/
theorem dualSectionsEquiv_apply [E.IsQuasicoherent] {W : U.Opens} (hW : IsAffineOpen W)
    (t : Γ(dualSheaf E, W)) (m : Γ(E, W)) :
    dualSectionsEquiv E hW t m = dualPairing E t (Over.mk (𝟙 W)) m := rfl

/-- The pullback `f^* τ` over `V ≤ f⁻¹ W` of a section `τ` of `F` over `W`. -/
abbrev pullbackSectionΓ (F : U.Modules) {V : C.Opens} {W : U.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (τ : Γ(F, W)) : Γ((Scheme.Modules.pullback f).obj F, V) :=
  Scheme.Modules.pullbackSection f F W V h τ

/-- **Sections of a pullback over affine opens.** For `V ≤ f⁻¹ W` affine and `F` quasi-coherent,
`c ⊗ τ ↦ c • f^* τ` is an isomorphism `Γ(C, V) ⊗_{Γ(U, W)} Γ(F, W) ≃ Γ(f^* F, V)`
(`affinePullbackSectionsBaseChangeIso`). -/
theorem exists_isBaseChange_pullbackSection (F : U.Modules) [F.IsQuasicoherent] {V : C.Opens}
    {W : U.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W) :
    letI := (f.appLE W V h).hom.toAlgebra
    letI : Module Γ(U, W) Γ((Scheme.Modules.pullback f).obj F, V) :=
      Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
    haveI : IsScalarTower Γ(U, W) Γ(C, V) Γ((Scheme.Modules.pullback f).obj F, V) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∃ ρ : Γ(F, W) →ₗ[Γ(U, W)] Γ((Scheme.Modules.pullback f).obj F, V),
      (∀ a, ρ a = pullbackSectionΓ f F h a) ∧ IsBaseChange Γ(C, V) ρ := by
  let := (f.appLE W V h).hom.toAlgebra
  let : Module Γ(U, W) Γ((Scheme.Modules.pullback f).obj F, V) :=
    Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
  have : IsScalarTower Γ(U, W) Γ(C, V) Γ((Scheme.Modules.pullback f).obj F, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρ : Γ(F, W) →ₗ[Γ(U, W)] Γ((Scheme.Modules.pullback f).obj F, V) :=
    { toFun := pullbackSectionHom f F W V h
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => pullbackSectionHom_smul f F W V h r a }
  exact ⟨ρ, fun _ => rfl, AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso
    (f.appLE W V h).hom rfl (affinePullbackSectionsBaseChangeIso f F hW hV h)
    ρ fun m => affinePullbackSectionsBaseChangeIso_one_tmul f F hW hV h m⟩

/-- **Sections of a pullback over affine opens**, as a linear equivalence
`Γ(C, V) ⊗_{Γ(U, W)} Γ(F, W) ≃ Γ(f^* F, V)`, `c ⊗ τ ↦ c • f^* τ`. -/
def pullbackSectionsEquiv (F : U.Modules) [F.IsQuasicoherent] {V : C.Opens} {W : U.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W) :
    letI := (f.appLE W V h).hom.toAlgebra
    (Γ(C, V) ⊗[Γ(U, W)] Γ(F, W)) ≃ₗ[Γ(C, V)] Γ((Scheme.Modules.pullback f).obj F, V) :=
  letI := (f.appLE W V h).hom.toAlgebra
  letI : Module Γ(U, W) Γ((Scheme.Modules.pullback f).obj F, V) :=
    Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
  haveI : IsScalarTower Γ(U, W) Γ(C, V) Γ((Scheme.Modules.pullback f).obj F, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  (exists_isBaseChange_pullbackSection f F hV hW h).choose_spec.2.equiv

/-- `pullbackSectionsEquiv` sends `c ⊗ τ` to `c • f^* τ`. -/
theorem pullbackSectionsEquiv_tmul (F : U.Modules) [F.IsQuasicoherent] {V : C.Opens}
    {W : U.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W) (c : Γ(C, V))
    (τ : Γ(F, W)) :
    letI := (f.appLE W V h).hom.toAlgebra
    pullbackSectionsEquiv f F hV hW h (c ⊗ₜ[Γ(U, W)] τ) = c • pullbackSectionΓ f F h τ := by
  let := (f.appLE W V h).hom.toAlgebra
  let : Module Γ(U, W) Γ((Scheme.Modules.pullback f).obj F, V) :=
    Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
  have : IsScalarTower Γ(U, W) Γ(C, V) Γ((Scheme.Modules.pullback f).obj F, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  rw [pullbackSectionsEquiv, IsBaseChange.equiv_tmul,
    (exists_isBaseChange_pullbackSection f F hV hW h).choose_spec.1]

/-- The sections of `f^* E^∨` over an affine `V ≤ f⁻¹ W` are `Γ(C, V) ⊗ Γ(E, W)^∨`. -/
def pullbackDualSectionsEquiv [E.IsQuasicoherent] [(dualSheaf E).IsQuasicoherent]
    {V : C.Opens} {W : U.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W) :
    letI := (f.appLE W V h).hom.toAlgebra
    Γ((Scheme.Modules.pullback f).obj (dualSheaf E), V) ≃ₗ[Γ(C, V)]
      Γ(C, V) ⊗[Γ(U, W)] Module.Dual Γ(U, W) Γ(E, W) :=
  letI := (f.appLE W V h).hom.toAlgebra
  (pullbackSectionsEquiv f (dualSheaf E) hV hW h).symm.trans
    (AlgebraTensorModule.congr (LinearEquiv.refl Γ(C, V) Γ(C, V)) (dualSectionsEquiv E hW))

/-- `pullbackDualSectionsEquiv` sends `c • f^* τ` to `c ⊗ τ`, with `τ` viewed as a linear form on
`Γ(E, W)`. -/
theorem pullbackDualSectionsEquiv_smul_pullbackSection [E.IsQuasicoherent]
    [(dualSheaf E).IsQuasicoherent] {V : C.Opens} {W : U.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W) (c : Γ(C, V)) (τ : Γ(dualSheaf E, W)) :
    letI := (f.appLE W V h).hom.toAlgebra
    pullbackDualSectionsEquiv f E hV hW h (c • pullbackSectionΓ f (dualSheaf E) h τ) =
      c ⊗ₜ[Γ(U, W)] dualSectionsEquiv E hW τ := by
  let := (f.appLE W V h).hom.toAlgebra
  rw [pullbackDualSectionsEquiv, LinearEquiv.trans_apply, ← pullbackSectionsEquiv_tmul f _ hV hW h,
    LinearEquiv.symm_apply_apply]
  rfl

/-- **The contraction of the sections of `f^* E^∨ ⊗ I`** over an affine `V ≤ f⁻¹ W`: a section
`(c • f^* τ) ⊗ y` goes to the `Γ(U, W)`-linear map `ω ↦ (τ ω) • c • y` on `Γ(E, W)`, with values in
`Γ(I, V)` (a `Γ(U, W)`-module through `f`). -/
def markedSectionsMap [E.IsQuasicoherent] [(dualSheaf E).IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj (dualSheaf E)).IsQuasicoherent] [I.IsQuasicoherent]
    {V : C.Opens} {W : U.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W) :
    letI := (f.appLE W V h).hom.toAlgebra
    letI : Module Γ(U, W) Γ(I, V) := Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
    haveI : IsScalarTower Γ(U, W) Γ(C, V) Γ(I, V) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Γ(tensorMod ((Scheme.Modules.pullback f).obj (dualSheaf E)) I, V) →ₗ[Γ(C, V)]
      (Γ(E, W) →ₗ[Γ(U, W)] Γ(I, V)) :=
  letI := (f.appLE W V h).hom.toAlgebra
  letI : Module Γ(U, W) Γ(I, V) := Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
  haveI : IsScalarTower Γ(U, W) Γ(C, V) Γ(I, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  baseChangeDualTensorHom Γ(U, W) Γ(C, V) Γ(I, V) Γ(E, W) ∘ₗ
    LinearMap.rTensor Γ(I, V) (pullbackDualSectionsEquiv f E hV hW h).toLinearMap ∘ₗ
    (gammaTensorEquiv hV ((Scheme.Modules.pullback f).obj (dualSheaf E)) I).symm.toLinearMap

/-- `markedSectionsMap` sends `(c • f^* τ) ⊗ y` to the map `ω ↦ (f (τ ω) * c) • y`. -/
theorem markedSectionsMap_gammaTmul [E.IsQuasicoherent] [(dualSheaf E).IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj (dualSheaf E)).IsQuasicoherent] [I.IsQuasicoherent]
    {V : C.Opens} {W : U.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W)
    (c : Γ(C, V)) (τ : Γ(dualSheaf E, W)) (y : Γ(I, V)) (ω : Γ(E, W)) :
    markedSectionsMap f E I hV hW h
        (gammaTmul _ I V (c • pullbackSectionΓ f (dualSheaf E) h τ) y) ω =
      (f.appLE W V h (dualPairing E τ (Over.mk (𝟙 W)) ω) * c) • y := by
  let := (f.appLE W V h).hom.toAlgebra
  let : Module Γ(U, W) Γ(I, V) := Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
  have : IsScalarTower Γ(U, W) Γ(C, V) Γ(I, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  simp only [markedSectionsMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← gammaTensorEquiv_tmul hV, LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, pullbackDualSectionsEquiv_smul_pullbackSection,
    baseChangeDualTensorHom_tmul, dualSectionsEquiv_apply, mul_smul]
  rfl

/-- For `Γ(E, W)` finite projective over `Γ(U, W)`, `markedSectionsMap` is bijective. -/
theorem markedSectionsMap_bijective [E.IsQuasicoherent] [(dualSheaf E).IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj (dualSheaf E)).IsQuasicoherent] [I.IsQuasicoherent]
    {V : C.Opens} {W : U.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W)
    [Module.Finite Γ(U, W) Γ(E, W)] [Module.Projective Γ(U, W) Γ(E, W)] :
    Function.Bijective (markedSectionsMap f E I hV hW h) := by
  let := (f.appLE W V h).hom.toAlgebra
  let : Module Γ(U, W) Γ(I, V) := Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
  have : IsScalarTower Γ(U, W) Γ(C, V) Γ(I, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  simp only [markedSectionsMap, LinearMap.coe_comp, LinearEquiv.coe_coe]
  refine (baseChangeDualTensorHom_bijective _ _ _ _).comp (Function.Bijective.comp ?_
    (LinearEquiv.bijective _))
  rw [← LinearEquiv.coe_rTensor]
  exact LinearEquiv.bijective _

section Restriction

/-- Restriction maps of a module compose. -/
theorem presheaf_map_map {X : Scheme.{u}} (M : X.Modules) {A B D : X.Opens} (h₁ : B ≤ A)
    (h₂ : D ≤ B) (x : Γ(M, A)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of a pure tensor of sections is the pure tensor of the restrictions. -/
theorem gammaTmul_res (F G : C.Modules) {V V' : C.Opens} (hV : V' ≤ V) (a : Γ(F, V))
    (b : Γ(G, V)) :
    (tensorMod F G).presheaf.map (homOfLE hV).op (gammaTmul F G V a b) =
      gammaTmul F G V' (F.presheaf.map (homOfLE hV).op a) (G.presheaf.map (homOfLE hV).op b) :=
  Stacks.AlgebraicGeometry.RestrictionSections.tensorSheafUnit_val_map F G (homOfLE hV).op a b

/-- Restricting a pulled-back section in the source. -/
theorem res_pullbackSectionΓ (F : U.Modules) {V V' : C.Opens} {W : U.Opens} (h : V ≤ f ⁻¹ᵁ W)
    (hV : V' ≤ V) (τ : Γ(F, W)) :
    ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hV).op (pullbackSectionΓ f F h τ) =
      pullbackSectionΓ f F (hV.trans h) τ := by
  change ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hV).op
      (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op W) τ)) =
    ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE (hV.trans h)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op W) τ)
  exact presheaf_map_map _ _ _ _

/-- Restricting a section before pulling it back. -/
theorem pullbackSectionΓ_res (F : U.Modules) {V : C.Opens} {W W' : U.Opens}
    (hW : W' ≤ W) (h : V ≤ f ⁻¹ᵁ W') (τ : Γ(F, W)) :
    pullbackSectionΓ f F h (F.presheaf.map (homOfLE hW).op τ) =
      pullbackSectionΓ f F (h.trans (f.preimage_mono hW)) τ := by
  have := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val (homOfLE hW).op τ
  change ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op W')
        (F.presheaf.map (homOfLE hW).op τ)) =
    ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE (h.trans (f.preimage_mono hW))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op W) τ)
  erw [this]
  change ((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE h).op
      (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE (f.preimage_mono hW)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op W) τ)) = _
  exact presheaf_map_map _ _ _ _

/-- The dual pairing commutes with restriction. -/
theorem dualPairing_res (E : U.Modules) {W W' : U.Opens} (hW : W' ≤ W) (τ : Γ(dualSheaf E, W))
    (ω : Γ(E, W)) :
    dualPairing E ((dualSheaf E).presheaf.map (homOfLE hW).op τ) (Over.mk (𝟙 W'))
        (E.presheaf.map (homOfLE hW).op ω) =
      U.presheaf.map (homOfLE hW).op (dualPairing E τ (Over.mk (𝟙 W)) ω) := by
  rw [dualPairing_map]
  exact dualPairing_naturality E τ (Over.homMk (homOfLE hW) rfl :
    Over.mk (𝟙 W' ≫ homOfLE hW) ⟶ Over.mk (𝟙 W)) ω

/-- `f^♯` commutes with restriction. -/
theorem appLE_res {V V' : C.Opens} {W W' : U.Opens} (h : V ≤ f ⁻¹ᵁ W) (h' : V' ≤ f ⁻¹ᵁ W')
    (hVV : V' ≤ V) (hWW : W' ≤ W) (a : Γ(U, W)) :
    f.appLE W' V' h' (U.presheaf.map (homOfLE hWW).op a) =
      C.presheaf.map (homOfLE hVV).op (f.appLE W V h a) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- **The contraction commutes with restriction**: for `V' ≤ V`, `W' ≤ W` affine with
`V ≤ f⁻¹ W`, `V' ≤ f⁻¹ W'`, contracting the restriction of a section with the restriction of a
section of `E` is the restriction of the contraction. -/
theorem markedSectionsMap_res [E.IsQuasicoherent] [(dualSheaf E).IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj (dualSheaf E)).IsQuasicoherent] [I.IsQuasicoherent]
    {V V' : C.Opens} {W W' : U.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hV' : IsAffineOpen V') (hW' : IsAffineOpen W') (h : V ≤ f ⁻¹ᵁ W) (h' : V' ≤ f ⁻¹ᵁ W')
    (hVV : V' ≤ V) (hWW : W' ≤ W)
    (x : Γ(tensorMod ((Scheme.Modules.pullback f).obj (dualSheaf E)) I, V)) (ω : Γ(E, W)) :
    markedSectionsMap f E I hV' hW' h'
        ((tensorMod ((Scheme.Modules.pullback f).obj (dualSheaf E)) I).presheaf.map
          (homOfLE hVV).op x) (E.presheaf.map (homOfLE hWW).op ω) =
      I.presheaf.map (homOfLE hVV).op (markedSectionsMap f E I hV hW h x ω) := by
  let := (f.appLE W V h).hom.toAlgebra
  obtain ⟨t, rfl⟩ :=
    (gammaTensorEquiv hV ((Scheme.Modules.pullback f).obj (dualSheaf E)) I).surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add t t' ht ht' => simp only [map_add, LinearMap.add_apply, ht, ht']
  | tmul e y =>
    obtain ⟨z, rfl⟩ := (pullbackSectionsEquiv f (dualSheaf E) hV hW h).surjective e
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.zero_tmul, LinearMap.zero_apply]
    | add z z' hz hz' => simp only [map_add, TensorProduct.add_tmul, LinearMap.add_apply, hz, hz']
    | tmul c τ =>
      rw [pullbackSectionsEquiv_tmul, gammaTensorEquiv_tmul, gammaTmul_res, Scheme.Modules.map_smul,
        res_pullbackSectionΓ, ← pullbackSectionΓ_res f (dualSheaf E) hWW h',
        markedSectionsMap_gammaTmul, markedSectionsMap_gammaTmul, dualPairing_res,
        appLE_res f h h' hVV hWW, Scheme.Modules.map_smul, map_mul]

end Restriction

end Sections

section Derivations

open AlgebraicGeometry Opposite

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))

/-- The universal differential `d : Γ(X, W) → Γ(Ω_{X/k}, W)`. -/
def universalD (W : X.Opens) : Γ(X, W) →+ Γ(Scheme.Hom.relativeDifferentials g, W) :=
  (Scheme.Hom.universalRelativeDerivation g).d (X := op W)

/-- The Leibniz rule for `universalD`: `d(ab) = a • db + b • da`. -/
theorem universalD_mul (W : X.Opens) (a b : Γ(X, W)) :
    universalD g W (a * b) = a • universalD g W b + b • universalD g W a :=
  (Scheme.Hom.universalRelativeDerivation g).d_mul a b

/-- `universalD` commutes with restriction to a smaller open. -/
theorem universalD_res {W W' : X.Opens} (h : W' ≤ W) (a : Γ(X, W)) :
    universalD g W' (X.presheaf.map (homOfLE h).op a) =
      (Scheme.Hom.relativeDifferentials g).presheaf.map (homOfLE h).op (universalD g W a) :=
  (Scheme.Hom.universalRelativeDerivation g).d_map (homOfLE h).op a

/-- `universalD` vanishes on the image of `k`. -/
theorem universalD_baseRingHom (W : X.Opens) (r : k) :
    universalD g W (Stacks.Cech.baseRingHom g W r) = 0 := by
  change universalD g W (X.presheaf.map (homOfLE _).op (Stacks.Cech.globalRingHom g r)) = 0
  rw [universalD_res]
  change (Scheme.Hom.relativeDifferentials g).presheaf.map _
    ((Scheme.Hom.universalRelativeDerivation g).d ((g.app ⊤).hom _)) = 0
  erw [Scheme.Hom.universalRelativeDerivation_d_app_eq_zero, map_zero]

/-- `universalD` vanishes on `1`. -/
theorem universalD_one (W : X.Opens) : universalD g W 1 = 0 :=
  (Scheme.Hom.universalRelativeDerivation g).d_one (op W)

variable (W : X.Opens) [Algebra k Γ(X, W)]
  (halg : ∀ r, algebraMap k Γ(X, W) r = Stacks.Cech.baseRingHom g W r)
  (M : Type u) [AddCommGroup M] [Module Γ(X, W) M] [Module k M] [IsScalarTower k Γ(X, W) M]

include halg in
/-- `universalD` vanishes on `algebraMap k Γ(X, W)`. -/
theorem universalD_algebraMap (r : k) : universalD g W (algebraMap k Γ(X, W) r) = 0 := by
  rw [halg]
  exact universalD_baseRingHom g W r

/-- The derivation `φ ∘ d` of a `Γ(X, W)`-linear map `φ` out of `Γ(Ω_{X/k}, W)`. -/
def derivationOfHom (φ : Γ(Scheme.Hom.relativeDifferentials g, W) →ₗ[Γ(X, W)] M) :
    Derivation k Γ(X, W) M where
  toFun a := φ (universalD g W a)
  map_add' a b := by simp only [map_add]
  map_smul' r a := by
    rw [Algebra.smul_def, universalD_mul, universalD_algebraMap g W halg, smul_zero, add_zero,
      map_smul, algebraMap_smul]
    rfl
  map_one_eq_zero' := by
    change φ (universalD g W 1) = 0
    rw [universalD_one, map_zero]
  leibniz' a b := by
    change φ (universalD g W (a * b)) = a • φ (universalD g W b) + b • φ (universalD g W a)
    rw [universalD_mul, map_add, map_smul, map_smul]

/-- `derivationOfHom g W halg M φ` sends `a` to `φ (universalD g W a)`. -/
@[simp]
theorem derivationOfHom_apply (φ : Γ(Scheme.Hom.relativeDifferentials g, W) →ₗ[Γ(X, W)] M)
    (a : Γ(X, W)) : derivationOfHom g W halg M φ a = φ (universalD g W a) := rfl

/-- **The differentials of a scheme over `Spec k` on an affine open** (Stacks 01UT,
`isIso_kaehlerToSections`): `Γ(Ω_{X/k}, W) ≃ Ω[Γ(X, W)⁄Γ(Spec k, ⊤)]`. -/
def differentialsSectionsEquiv {W : X.Opens} (hW : IsAffineOpen W) :
    letI := (g.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
    Γ(Scheme.Hom.relativeDifferentials g, W) ≃ₗ[Γ(X, W)]
      Ω[Γ(X, W)⁄Γ(Spec (.of k), ⊤)] :=
  letI := (g.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
  haveI := Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections g hW
    (V := ⊤) (fun _ _ => trivial) (isAffineOpen_top _)
  (asIso (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections g ⊤ W
    (fun _ _ => trivial))).toLinearEquiv.symm

/-- `differentialsSectionsEquiv` identifies the Kähler differential `D a` with
`universalD g W a`. -/
theorem differentialsSectionsEquiv_symm_D {W : X.Opens} (hW : IsAffineOpen W) (a : Γ(X, W)) :
    letI := (g.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
    (differentialsSectionsEquiv g hW).symm (KaehlerDifferential.D Γ(Spec (.of k), ⊤) Γ(X, W) a) =
      universalD g W a :=
  Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d g ⊤ W (fun _ _ => trivial) a

include halg in
/-- **Derivations of the functions on an affine open `W` of a `k`-scheme are the linear maps out of
`Γ(Ω_{X/k}, W)`**: `φ ↦ φ ∘ d` is bijective (Stacks 01UT). -/
theorem derivationOfHom_bijective (hW : IsAffineOpen W) :
    Function.Bijective (derivationOfHom g W halg M) := by
  let := (g.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
  set e := differentialsSectionsEquiv g hW
  have he : ∀ a, e (universalD g W a) = KaehlerDifferential.D Γ(Spec (.of k), ⊤) Γ(X, W) a :=
    fun a => by rw [← differentialsSectionsEquiv_symm_D g hW a, LinearEquiv.apply_symm_apply]
  let : Module Γ(Spec (.of k), ⊤) M := Module.compHom M (algebraMap Γ(Spec (.of k), ⊤) Γ(X, W))
  have : IsScalarTower Γ(Spec (.of k), ⊤) Γ(X, W) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine ⟨fun φ ψ hφψ => ?_, fun D => ?_⟩
  · have hD : ∀ a, φ (universalD g W a) = ψ (universalD g W a) := fun a =>
      congrArg (fun D : Derivation k Γ(X, W) M => D a) hφψ
    have h1 : φ ∘ₗ e.symm.toLinearMap = ψ ∘ₗ e.symm.toLinearMap :=
      Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => by
        change φ (e.symm (KaehlerDifferential.D _ _ a)) = ψ (e.symm (KaehlerDifferential.D _ _ a))
        rw [differentialsSectionsEquiv_symm_D]
        exact hD a)
    ext x
    simpa using LinearMap.congr_fun h1 (e x)
  · have hbase : ∀ r : Γ(Spec (.of k), ⊤), D (algebraMap Γ(Spec (.of k), ⊤) Γ(X, W) r) = 0 := by
      intro r
      obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso (toSpecΓ (CommRingCat.of k))).2 r
      have h1 : algebraMap Γ(Spec (.of k), ⊤) Γ(X, W) ((toSpecΓ (CommRingCat.of k)).hom r) =
          algebraMap k Γ(X, W) r := by
        rw [halg, Stacks.Cech.baseRingHom_eq_appLE g W (fun _ _ => trivial)]
        rfl
      rw [h1, D.map_algebraMap]
    let D' : Derivation Γ(Spec (.of k), ⊤) Γ(X, W) M :=
      { toFun := D
        map_add' := map_add D
        map_smul' := fun r a => by
          rw [Algebra.smul_def, D.leibniz, hbase, smul_zero, add_zero, algebraMap_smul]
          rfl
        map_one_eq_zero' := D.map_one_eq_zero
        leibniz' := D.leibniz }
    refine ⟨D'.liftKaehlerDifferential ∘ₗ e.toLinearMap, ?_⟩
    ext a
    change D'.liftKaehlerDifferential (e (universalD g W a)) = D a
    rw [he, Derivation.liftKaehlerDifferential_comp_D]
    rfl

/-- On an affine open of a smooth scheme over `Spec k`, `Γ(Ω_{X/k}, W)` is a finite projective
`Γ(X, W)`-module. -/
theorem finite_projective_differentialsSections [Smooth g] {W : X.Opens} (hW : IsAffineOpen W) :
    Module.Finite Γ(X, W) Γ(Scheme.Hom.relativeDifferentials g, W) ∧
      Module.Projective Γ(X, W) Γ(Scheme.Hom.relativeDifferentials g, W) := by
  let := (g.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
  have h1 := HasRingHomProperty.appLE @Smooth g (inferInstance : Smooth g)
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  have : Algebra.Smooth Γ(Spec (.of k), ⊤) Γ(X, W) := by
    rw [← RingHom.smooth_algebraMap]
    exact h1
  exact ⟨Module.Finite.equiv (differentialsSectionsEquiv g hW).symm,
    Module.Projective.of_equiv (differentialsSectionsEquiv g hW).symm⟩

end Derivations

section IdealSheaf

open AlgebraicGeometry Opposite

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- The ideal sheaf `ℐ = ker(𝒪_X → i_* 𝒪_Z)` of a morphism of schemes, as a module on `X`. -/
abbrev idealSheafModule : X.Modules := Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom

/-- The inclusion `Γ(ℐ, V) → Γ(X, V)`. -/
def idealSheafSectionsIncl (V : X.Opens) : Γ(idealSheafModule i, V) →ₗ[Γ(X, V)] Γ(X, V) where
  toFun y := (Scheme.Modules.Hom.app
    (Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom :
      idealSheafModule i ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) V) y
  map_add' := map_add _
  map_smul' r y := Scheme.Modules.Hom.app_smul _ r y

/-- The inclusion `Γ(ℐ, V) → Γ(X, V)` is injective. -/
theorem idealSheafSectionsIncl_injective (V : X.Opens) :
    Function.Injective (idealSheafSectionsIncl i V) :=
  Stacks.ClosedImmersion.injective_idealSheafι_val_app i.toLRSHom.toShHom V

/-- A section of the ideal sheaf `ℐ` maps to zero in `Γ(Z, i⁻¹ V)`. -/
theorem app_idealSheafSectionsIncl (V : X.Opens) (y : Γ(idealSheafModule i, V)) :
    (i.app V).hom (idealSheafSectionsIncl i V y) = 0 :=
  congrArg (fun φ => (φ.val.app (op V)).hom y)
    (Limits.kernel.condition (RingedSpaceModuleAdjunction.structureSheafModuleHom
      i.toLRSHom.toShHom))

/-- A section of `𝒪_X` over `V` vanishing in `Γ(Z, i⁻¹ V)` is a section of the ideal sheaf `ℐ`. -/
theorem exists_idealSheafSectionsIncl_eq (V : X.Opens) (a : Γ(X, V))
    (ha : (i.app V).hom a = 0) : ∃ y, idealSheafSectionsIncl i V y = a :=
  Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero i.toLRSHom.toShHom V a ha

/-- The inclusion `Γ(ℐ, V) → Γ(X, V)` commutes with restriction. -/
theorem idealSheafSectionsIncl_res {V V' : X.Opens} (h : V' ≤ V) (y : Γ(idealSheafModule i, V)) :
    idealSheafSectionsIncl i V' ((idealSheafModule i).presheaf.map (homOfLE h).op y) =
      X.presheaf.map (homOfLE h).op (idealSheafSectionsIncl i V y) :=
  PresheafOfModules.naturality_apply
    (Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom).val (homOfLE h).op y

/-- **The sections of the ideal sheaf of a closed subscheme over an affine open** are the ideal
`I(V)`. -/
theorem exists_idealSheafSectionsIncl_eq_iff (I : X.IdealSheafData) {V : X.Opens}
    (hV : IsAffineOpen V) (a : Γ(X, V)) :
    (∃ y, idealSheafSectionsIncl I.subschemeι V y = a) ↔ a ∈ I.ideal ⟨V, hV⟩ := by
  rw [← Scheme.IdealSheafData.ker_subschemeι_app I ⟨V, hV⟩, RingHom.mem_ker]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ app_idealSheafSectionsIncl _ V y,
    exists_idealSheafSectionsIncl_eq _ V a⟩

/-- A function on `V` is killed by `g^♯` iff the images of its germs under the stalk maps of
`g` vanish. -/
theorem app_eq_zero_iff_forall_stalkMap {Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens) (a : Γ(X, V)) :
    (g.app V).hom a = 0 ↔
      ∀ (y : Y) (hy : g.base y ∈ V), g.stalkMap y (X.presheaf.germ V (g.base y) hy a) = 0 := by
  refine ⟨fun h y hy => by rw [Scheme.Hom.germ_stalkMap_apply, h, map_zero],
    fun h => TopCat.Presheaf.section_ext Y.sheaf (g ⁻¹ᵁ V) _ 0 fun y hy => ?_⟩
  change Y.presheaf.germ (g ⁻¹ᵁ V) y hy ((g.app V).hom a) =
    Y.presheaf.germ (g ⁻¹ᵁ V) y hy 0
  rw [map_zero]
  exact (Scheme.Hom.germ_stalkMap_apply g V y hy a).symm.trans (h y hy)

/-- A local map of stalks into a field kills exactly the maximal ideal. -/
theorem stalkMap_eq_zero_iff {Y : Scheme.{u}} (g : Y ⟶ X) (y : Y)
    (hy : IsField (Y.presheaf.stalk y)) (z : X.presheaf.stalk (g.base y)) :
    g.stalkMap y z = 0 ↔ z ∈ IsLocalRing.maximalIdeal _ := by
  rw [IsLocalRing.mem_maximalIdeal, ← map_mem_nonunits_iff (g.stalkMap y).hom,
    ← IsLocalRing.mem_maximalIdeal, IsLocalRing.isField_iff_maximalIdeal_eq.1 hy,
    Ideal.mem_bot]

/-- The stalks of the spectrum of a reduced Artinian ring are fields. -/
theorem isField_stalk_spec (R : CommRingCat.{u}) [IsArtinianRing R] [IsReduced R]
    (y : Spec R) : IsField ((Spec R).presheaf.stalk y) := by
  let := StructureSheaf.stalkAlgebra R y
  have := StructureSheaf.IsLocalization.to_stalk R y
  have : IsArtinianRing ((Spec R).presheaf.stalk y) :=
    IsArtinianRing.localization_artinian y.asIdeal.primeCompl _
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing _

/-- The ideal sheaf of a closed immersion is quasi-coherent. -/
theorem isQuasicoherent_idealSheafModule [IsClosedImmersion i] :
    (idealSheafModule i).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf i

end IdealSheaf

section Tangent

open AlgebraicGeometry Stacks.AlgebraicGeometry.ReflexiveModules

/-- The sheaf of differentials of a morphism of schemes is quasi-coherent. -/
theorem isQuasicoherent_relativeDifferentials {X S : Scheme.{u}} (g : X ⟶ S) :
    (Scheme.Hom.relativeDifferentials g).IsQuasicoherent :=
  Scheme.Hom.isQuasicoherent_relativeDifferentials g

/-- The tangent sheaf `(Ω_{X/S})^∨` of a smooth morphism of relative dimension `n` is
quasi-coherent. -/
theorem isQuasicoherent_dualSheaf_relativeDifferentials {X S : Scheme.{u}} (g : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n g] :
    (dualSheaf (Scheme.Hom.relativeDifferentials g)).IsQuasicoherent := by
  have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials g n
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualSheaf (Scheme.Hom.relativeDifferentials g)) n :=
    isFiniteLocallyFreeOfRank_dualSheaf _ n inferInstance
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf (Scheme.Hom.relativeDifferentials g)) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ n
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _

end Tangent

section MarkedDerivations

open AlgebraicGeometry Opposite Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.AffineOpenTensorSections (tensorMod)

variable {k : Type u} [CommRing k] {C U : Scheme.{u}} (sU : U ⟶ Spec (.of k)) (f : C ⟶ U)
  (I : C.Modules)

/-- **Sections of `f^* T_{U/k} ⊗ I` over affine opens are derivations.** For `V ≤ f⁻¹ W` affine and
`U` smooth over `k`, a section `x` of `f^* (Ω_{U/k})^∨ ⊗ I` over `V` is determined by the map
`a ↦ x(d a) : Γ(U, W) → Γ(I, V)`, and every additive map `Γ(U, W) → Γ(I, V)` satisfying the Leibniz
rule (through `f`) and killing `k` arises this way. -/
theorem markedSectionsMap_universalD_bijective [Smooth sU]
    [(Scheme.Hom.relativeDifferentials sU).IsQuasicoherent]
    [(dualSheaf (Scheme.Hom.relativeDifferentials sU)).IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj
      (dualSheaf (Scheme.Hom.relativeDifferentials sU))).IsQuasicoherent]
    [I.IsQuasicoherent] {V : C.Opens} {W : U.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W) :
    (∀ x x' : Γ(tensorMod ((Scheme.Modules.pullback f).obj
        (dualSheaf (Scheme.Hom.relativeDifferentials sU))) I, V),
      (∀ a, markedSectionsMap f _ I hV hW h x (universalD sU W a) =
        markedSectionsMap f _ I hV hW h x' (universalD sU W a)) → x = x') ∧
    ∀ D : Γ(U, W) → Γ(I, V), (∀ a a', D (a + a') = D a + D a') →
      (∀ a a', D (a * a') = f.appLE W V h a • D a' + f.appLE W V h a' • D a) →
      (∀ r, D (Stacks.Cech.baseRingHom sU W r) = 0) →
      ∃ x, ∀ a, markedSectionsMap f _ I hV hW h x (universalD sU W a) = D a := by
  obtain ⟨hfin, hproj⟩ := finite_projective_differentialsSections sU hW
  let := (f.appLE W V h).hom.toAlgebra
  let : Module Γ(U, W) Γ(I, V) := Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
  have : IsScalarTower Γ(U, W) Γ(C, V) Γ(I, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Algebra k Γ(U, W) := (Stacks.Cech.baseRingHom sU W).hom.toAlgebra
  let : Module k Γ(I, V) := Module.compHom _ (algebraMap k Γ(U, W))
  have : IsScalarTower k Γ(U, W) Γ(I, V) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hbij := (derivationOfHom_bijective sU W (fun _ => rfl) Γ(I, V) hW).comp
    (markedSectionsMap_bijective f _ I hV hW h)
  refine ⟨fun x x' hxx => hbij.1 (Derivation.ext hxx), fun D hadd hmul hbase => ?_⟩
  let D' : Derivation k Γ(U, W) Γ(I, V) :=
    { toFun := D
      map_add' := hadd
      map_smul' := fun r a => by
        rw [Algebra.smul_def, hmul, show algebraMap k Γ(U, W) r =
          Stacks.Cech.baseRingHom sU W r from rfl, hbase, smul_zero, add_zero]
        rfl
      map_one_eq_zero' := by
        have h1 := hmul 1 1
        rw [mul_one, map_one, one_smul] at h1
        change D 1 = 0
        simpa using h1
      leibniz' := fun a a' => hmul a a' }
  obtain ⟨x, hx⟩ := hbij.2 D'
  exact ⟨x, fun a => congrArg (fun D : Derivation k Γ(U, W) Γ(I, V) => D a) hx⟩

end MarkedDerivations

section ChartIdentification

open AlgebraicGeometry Opposite Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.AffineOpenTensorSections (tensorMod)
open MMP.Fourfold.CurveChartDeformations MMP.Fourfold.CurveMapCharts

variable {k : Type u} [Field k] {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (sU : U ⟶ Spec (.of k)) {f : C ⟶ U} (hf : f ≫ sU = sC) {ι : Type u} [DecidableEq ι]
  [LinearOrder ι] (K : ChartCover f ι) {b : ℕ} (pts : Fin b → C) {Z : Scheme.{u}} (i : Z ⟶ C)

/-- The sections of an ideal sheaf whose sections over affine opens are the ideals of the points
`pts`, as those ideals. -/
def chartIdealEquiv (hI : ∀ (V : C.Opens), IsAffineOpen V → ∀ a : Γ(C, V),
      (∃ y, idealSheafSectionsIncl i V y = a) ↔ a ∈ vanishingIdeal pts V)
    {V : C.Opens} (hV : IsAffineOpen V) :
    Γ(idealSheafModule i, V) ≃ₗ[Γ(C, V)] vanishingIdeal pts V :=
  (LinearEquiv.ofInjective (idealSheafSectionsIncl i V)
      (idealSheafSectionsIncl_injective i V)).trans
    (LinearEquiv.ofEq _ _ (by ext a; rw [LinearMap.mem_range]; exact hI V hV a))

/-- The underlying element of `chartIdealEquiv pts i hI hV y` is `idealSheafSectionsIncl i V y`. -/
theorem coe_chartIdealEquiv (hI : ∀ (V : C.Opens), IsAffineOpen V → ∀ a : Γ(C, V),
      (∃ y, idealSheafSectionsIncl i V y = a) ↔ a ∈ vanishingIdeal pts V)
    {V : C.Opens} (hV : IsAffineOpen V) (y : Γ(idealSheafModule i, V)) :
    (chartIdealEquiv pts i hI hV y : Γ(C, V)) = idealSheafSectionsIncl i V y := rfl

variable [Smooth sU]
  [(Scheme.Hom.relativeDifferentials sU).IsQuasicoherent]
  [(dualSheaf (Scheme.Hom.relativeDifferentials sU)).IsQuasicoherent]
  [((Scheme.Modules.pullback f).obj
    (dualSheaf (Scheme.Hom.relativeDifferentials sU))).IsQuasicoherent]
  [(idealSheafModule i).IsQuasicoherent]

include hf in
omit [Smooth sU] [(Scheme.Hom.relativeDifferentials sU).IsQuasicoherent]
  [(dualSheaf (Scheme.Hom.relativeDifferentials sU)).IsQuasicoherent]
  [((Scheme.Modules.pullback f).obj
    (dualSheaf (Scheme.Hom.relativeDifferentials sU))).IsQuasicoherent]
  [(idealSheafModule i).IsQuasicoherent] in
/-- The ideal of the points in `V` is a `Γ(U, W)`-module through `f`, compatibly with `k`. -/
theorem isScalarTower_vanishingIdeal {V : C.Opens} {W : U.Opens} (h : V ≤ f ⁻¹ᵁ W) :
    letI := CurveMapCharts.sectionsAlgebra sU W
    letI := CurveMapCharts.sectionsAlgebra sC V
    letI : Module Γ(U, W) (vanishingIdeal pts V) := Module.compHom _ (f.appLE W V h).hom
    IsScalarTower k Γ(U, W) (vanishingIdeal pts V) := by
  let := CurveMapCharts.sectionsAlgebra sU W
  let := CurveMapCharts.sectionsAlgebra sC V
  let : Module Γ(U, W) (vanishingIdeal pts V) := Module.compHom _ (f.appLE W V h).hom
  refine ⟨fun r a z => Subtype.ext ?_⟩
  change f.appLE W V h (Stacks.Cech.baseRingHom sU W r * a) * (z : Γ(C, V)) =
    Stacks.Cech.baseRingHom sC V r * (f.appLE W V h a * z)
  rw [map_mul, mul_assoc]
  congr 1
  exact congrArg (fun φ => φ.hom r) (baseRingHom_comp_appLE sC sU hf h)

include hf in
/-- **The chart derivations of a section of `f^* T_U ⊗ I`**: for `V ≤ f⁻¹ W` affine, a `k`-linear
bijection from the sections of `f^* T_U ⊗ I` over `V` to `Der_k(Γ(U, W), I(V))`, given by
`a ↦ x(d a)`, where `I(V)` is the ideal of the points `pts` lying in `V`. -/
theorem exists_derivationMap
    (hI : ∀ (V : C.Opens), IsAffineOpen V → ∀ a : Γ(C, V),
      (∃ y, idealSheafSectionsIncl i V y = a) ↔ a ∈ vanishingIdeal pts V)
    {V : C.Opens} {W : U.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : V ≤ f ⁻¹ᵁ W) :
    letI := CurveMapCharts.sectionsAlgebra sU W
    letI := CurveMapCharts.sectionsAlgebra sC V
    letI : Module Γ(U, W) (vanishingIdeal pts V) := Module.compHom _ (f.appLE W V h).hom
    haveI := isScalarTower_vanishingIdeal sC sU hf pts h
    letI := Stacks.Cech.sectionsModule sC (tensorMod ((Scheme.Modules.pullback f).obj
        (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i)) V
    ∃ Ψ : Γ(tensorMod ((Scheme.Modules.pullback f).obj
        (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i), V) →ₗ[k]
        Derivation k Γ(U, W) (vanishingIdeal pts V),
      Function.Bijective Ψ ∧ ∀ x a, ((Ψ x a : vanishingIdeal pts V) : Γ(C, V)) =
        idealSheafSectionsIncl i V (markedSectionsMap f _ (idealSheafModule i) hV hW h x
          (universalD sU W a)) := by
  let := CurveMapCharts.sectionsAlgebra sU W
  let := CurveMapCharts.sectionsAlgebra sC V
  let : Module Γ(U, W) (vanishingIdeal pts V) := Module.compHom _ (f.appLE W V h).hom
  have := isScalarTower_vanishingIdeal sC sU hf pts h
  let := Stacks.Cech.sectionsModule sC (tensorMod ((Scheme.Modules.pullback f).obj
      (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i)) V
  obtain ⟨hinj, hsurj⟩ := markedSectionsMap_universalD_bijective sU f (idealSheafModule i) hV hW h
  let := (f.appLE _ _ h).hom.toAlgebra
  let : Module Γ(U, W) Γ(idealSheafModule i, V) := Module.compHom _ (algebraMap Γ(U, W) Γ(C, V))
  have : IsScalarTower Γ(U, W) Γ(C, V) Γ(idealSheafModule i, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  set F : Γ(tensorMod ((Scheme.Modules.pullback f).obj
      (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i), V) →
      Γ(U, W) → Γ(C, V) := fun x a => idealSheafSectionsIncl i V
        (markedSectionsMap f _ (idealSheafModule i) hV hW h x (universalD sU W a)) with hF
  have hmem : ∀ x a, F x a ∈ vanishingIdeal pts V := fun x a => (hI _ hV _).1 ⟨_, rfl⟩
  have hbase : ∀ r : k, f.appLE _ _ h (Stacks.Cech.baseRingHom sU W r) =
      Stacks.Cech.baseRingHom sC V r := fun r =>
    congrArg (fun φ => φ.hom r) (baseRingHom_comp_appLE sC sU hf h)
  have Fadd : ∀ x a a', F x (a + a') = F x a + F x a' := fun x a a' => by
    simp only [hF, map_add]
  have Fmul : ∀ x a a', F x (a * a') = f.appLE _ _ h a * F x a' + f.appLE _ _ h a' * F x a :=
    fun x a a' => by
      simp only [hF, universalD_mul, map_add, map_smul]
      rw [algebra_compatible_smul Γ(C, V) a, algebra_compatible_smul Γ(C, V) a',
        map_smul, map_smul]
      rfl
  have Fbase : ∀ x r, F x (Stacks.Cech.baseRingHom sU W r) = 0 := fun x r => by
    change idealSheafSectionsIncl i V (markedSectionsMap f _ (idealSheafModule i) hV hW h x
      (universalD sU W (Stacks.Cech.baseRingHom sU W r))) = 0
    rw [universalD_baseRingHom, map_zero, map_zero]
  have Fsmul : ∀ (c : Γ(C, V)) x a, F (c • x) a = c * F x a := fun c x a => by
    simp only [hF, map_smul, LinearMap.smul_apply]
    rfl
  let Ψ0 : Γ(tensorMod ((Scheme.Modules.pullback f).obj
      (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i), V) →
      Derivation k Γ(U, W) (vanishingIdeal pts V) := fun x =>
    { toFun := fun a => ⟨F x a, hmem x a⟩
      map_add' := fun a a' => Subtype.ext (Fadd x a a')
      map_smul' := fun r a => by
        apply Subtype.ext
        change F x (Stacks.Cech.baseRingHom sU W r * a) = Stacks.Cech.baseRingHom sC V r * F x a
        rw [Fmul, Fbase, mul_zero, add_zero, hbase]
      map_one_eq_zero' := by
        apply Subtype.ext
        change F x 1 = 0
        have h1 := Fmul x 1 1
        rw [mul_one, map_one, one_mul] at h1
        linear_combination -1 * h1
      leibniz' := fun a a' => Subtype.ext (Fmul x a a') }
  refine ⟨{ toFun := Ψ0
            map_add' := fun x x' => Derivation.ext fun a => Subtype.ext (by
              change F (x + x') a = F x a + F x' a
              simp only [hF, map_add, LinearMap.add_apply])
            map_smul' := fun r x => Derivation.ext fun a => Subtype.ext (by
              change F (Stacks.Cech.baseRingHom sC V r • x) a =
                Stacks.Cech.baseRingHom sC V r * F x a
              exact Fsmul _ x a) }, ⟨fun x x' hxx => hinj x x' fun a => ?_, fun D => ?_⟩,
    fun x a => rfl⟩
  · have := congrArg (fun D : Derivation k Γ(U, W) (vanishingIdeal pts V) =>
      ((D a : vanishingIdeal pts V) : Γ(C, V))) hxx
    exact idealSheafSectionsIncl_injective i _ this
  · let e := chartIdealEquiv pts i hI hV
    obtain ⟨x, hx⟩ := hsurj (fun a => e.symm (D a)) (fun a a' => by rw [map_add, map_add])
      (fun a a' => by
        rw [D.leibniz, map_add]
        exact congrArg₂ (· + ·) (e.symm.map_smul (f.appLE _ _ h a) (D a'))
          (e.symm.map_smul (f.appLE _ _ h a') (D a)))
      (fun r => by
        rw [show Stacks.Cech.baseRingHom sU W r = algebraMap k Γ(U, W) r from rfl,
          D.map_algebraMap, map_zero])
    refine ⟨x, Derivation.ext fun a => Subtype.ext ?_⟩
    change idealSheafSectionsIncl i V (markedSectionsMap f _ (idealSheafModule i) hV hW h x
      (universalD sU W a)) = _
    rw [hx a, ← coe_chartIdealEquiv pts i hI hV, LinearEquiv.apply_symm_apply]

include hf in
omit [DecidableEq ι] [LinearOrder ι] in
/-- **The chart derivations of the sections of `f^* T_U ⊗ I`**: on each nonempty intersection a
`k`-linear bijection `Ψ_s : Γ(U_s, f^* (Ω_{U/k})^∨ ⊗ I) ≃ Der_k(Γ(W_s, 𝒪_U), I(U_s))`,
`x ↦ (a ↦ x(d a))`, and restriction of sections corresponds to the extension of derivations along
the étale restrictions. -/
theorem exists_derivationMaps_curveCharts [IsSeparated sU] [IsSeparated sC]
    (hI : ∀ (V : C.Opens), IsAffineOpen V → ∀ a : Γ(C, V),
      (∃ y, idealSheafSectionsIncl i V y = a) ↔ a ∈ vanishingIdeal pts V) :
    ∃ Ψ : ∀ s : Finset ι, s.Nonempty →
        ((sectionsCechPresheaf sC K.UC (tensorMod ((Scheme.Modules.pullback f).obj
            (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i))).obj s →ₗ[k]
          Derivation k ((curveCharts sC sU K hf pts).S s) ((curveCharts sC sU K hf pts).𝔟 s)),
      (∀ s hs, Function.Bijective (Ψ s hs)) ∧
      ∀ (s t : Finset ι) (h : s ⊆ t) (hs : s.Nonempty) x,
        Ψ t (hs.mono h) ((sectionsCechPresheaf sC K.UC (tensorMod ((Scheme.Modules.pullback f).obj
            (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i))).res h x) =
          (curveCharts sC sU K hf pts).extDerB h hs (Ψ s hs x) := by
  have key : ∀ (s : Finset ι) (hs : s.Nonempty),
      ∃ Ψ : (sectionsCechPresheaf sC K.UC (tensorMod ((Scheme.Modules.pullback f).obj
          (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i))).obj s →ₗ[k]
          Derivation k ((curveCharts sC sU K hf pts).S s) ((curveCharts sC sU K hf pts).𝔟 s),
        Function.Bijective Ψ ∧ ∀ x a,
          ((Ψ x a : (curveCharts sC sU K hf pts).𝔟 s) : (curveCharts sC sU K hf pts).O s) =
            idealSheafSectionsIncl i _ (markedSectionsMap f _ (idealSheafModule i)
              (K.isAffineOpen_inf_UC sC hs) (K.isAffineOpen_inf_WU sU hs) (K.le_inf s) x
              (universalD sU _ a)) := fun s hs =>
    exists_derivationMap sC sU hf pts i hI (K.isAffineOpen_inf_UC sC hs)
      (K.isAffineOpen_inf_WU sU hs) (K.le_inf s)
  choose Ψ hΨ hΨf using key
  refine ⟨Ψ, hΨ, fun s t h hs x => ?_⟩
  refine (curveCharts sC sU K hf pts).extDerB_unique h hs _ _ fun a => ?_
  apply Subtype.ext
  change ((Ψ t (hs.mono h) ((sectionsCechPresheaf sC K.UC _).res h x)
    ((curveCharts sC sU K hf pts).σ h a) : (curveCharts sC sU K hf pts).𝔟 t) :
      (curveCharts sC sU K hf pts).O t) =
    C.presheaf.map (homOfLE (Finset.inf_mono h)).op
      ((Ψ s hs x a : (curveCharts sC sU K hf pts).𝔟 s) : (curveCharts sC sU K hf pts).O s)
  rw [hΨf, hΨf]
  change idealSheafSectionsIncl i _ (markedSectionsMap f _ (idealSheafModule i) _ _ _
      ((tensorMod ((Scheme.Modules.pullback f).obj
        (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i)).presheaf.map
        (homOfLE (Finset.inf_mono h)).op x)
      (universalD sU _ (U.presheaf.map (homOfLE (Finset.inf_mono h)).op a))) = _
  erw [universalD_res]
  exact (congrArg (idealSheafSectionsIncl i _) (markedSectionsMap_res f _ _
    (K.isAffineOpen_inf_UC sC hs) (K.isAffineOpen_inf_WU sU hs) _ _ _ _ _ _ x _)).trans
    (idealSheafSectionsIncl_res i _ _)

include hf in
omit [DecidableEq ι] [LinearOrder ι] in
/-- **The derivations of the curve charts with values in the ideals of the points are the sections
of `f^* T_U ⊗ I`**, compatibly with restriction: on each nonempty intersection,
`Der_k(Γ(W_s, 𝒪_U), I(U_s)) ≃ Γ(U_s, f^* (Ω_{U/k})^∨ ⊗ I)`, the extension of derivations along
the étale restrictions corresponding to restriction of sections. -/
theorem exists_derivationEquiv_curveCharts [IsSeparated sU] [IsSeparated sC]
    (hI : ∀ (V : C.Opens), IsAffineOpen V → ∀ a : Γ(C, V),
      (∃ y, idealSheafSectionsIncl i V y = a) ↔ a ∈ vanishingIdeal pts V) :
    ∃ θ : ∀ s : Finset ι, s.Nonempty →
        (Derivation k ((curveCharts sC sU K hf pts).S s) ((curveCharts sC sU K hf pts).𝔟 s) ≃ₗ[k]
          (sectionsCechPresheaf sC K.UC (tensorMod ((Scheme.Modules.pullback f).obj
            (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i))).obj s),
      ∀ (s t : Finset ι) (h : s ⊆ t) (hs : s.Nonempty)
        (D : Derivation k ((curveCharts sC sU K hf pts).S s) ((curveCharts sC sU K hf pts).𝔟 s)),
        θ t (hs.mono h) ((curveCharts sC sU K hf pts).extDerB h hs D) =
          (sectionsCechPresheaf sC K.UC (tensorMod ((Scheme.Modules.pullback f).obj
            (dualSheaf (Scheme.Hom.relativeDifferentials sU))) (idealSheafModule i))).res h
            (θ s hs D) := by
  obtain ⟨Ψ, hΨ, hnat⟩ := exists_derivationMaps_curveCharts sC sU hf K pts i hI
  refine ⟨fun s hs => (LinearEquiv.ofBijective (Ψ s hs) (hΨ s hs)).symm, fun s t h hs D => ?_⟩
  obtain ⟨x, rfl⟩ := (hΨ s hs).2 D
  have hθx : (LinearEquiv.ofBijective (Ψ s hs) (hΨ s hs)).symm (Ψ s hs x) = x :=
    (LinearEquiv.ofBijective (Ψ s hs) (hΨ s hs)).symm_apply_apply x
  rw [hθx, LinearEquiv.symm_apply_eq]
  exact (hnat s t h hs x).symm

end ChartIdentification

section FirstOrderPoints

open MMP.Fourfold.CurveChartDeformations

variable {k : Type u} [Field k] {ι : Type u} (Ch : CurveCharts k ι) {s : Finset ι}

/-- The `k`-linear map `a ↦ f0 a ⊗ 1 + D a ⊗ ε` underlying `dualPoint`. -/
def dualPointLinear (D : Derivation k (Ch.S s) (Ch.𝔟 s)) :
    Ch.S s →ₗ[k] Ch.O s ⊗[k] DualNumber k where
  toFun a := Ch.f0 s a ⊗ₜ 1 + ((D a : Ch.𝔟 s) : Ch.O s) ⊗ₜ DualNumber.eps
  map_add' a b := by
    rw [map_add, map_add, Submodule.coe_add, TensorProduct.add_tmul, TensorProduct.add_tmul]
    abel
  map_smul' r a := by
    rw [map_smul, D.map_smul, Submodule.coe_smul_of_tower, RingHom.id_apply, smul_add,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul']

/-- `dualPointLinear Ch D` sends `a` to `f0 a ⊗ 1 + D a ⊗ ε`. -/
theorem dualPointLinear_apply (D : Derivation k (Ch.S s) (Ch.𝔟 s)) (a : Ch.S s) :
    dualPointLinear Ch D a = Ch.f0 s a ⊗ₜ 1 + ((D a : Ch.𝔟 s) : Ch.O s) ⊗ₜ DualNumber.eps := rfl

/-- **The first-order deformation `f0 + ε D` of the chart map along a derivation `D`** with values
in the ideal of the marked points: the `k`-algebra map `S → O ⊗ k[ε]`, `a ↦ f0 a ⊗ 1 + D a ⊗ ε`. -/
def dualPoint (D : Derivation k (Ch.S s) (Ch.𝔟 s)) : Ch.S s →ₐ[k] Ch.O s ⊗[k] DualNumber k :=
  AlgHom.ofLinearMap (dualPointLinear Ch D)
    (by
      rw [dualPointLinear_apply, map_one, D.map_one_eq_zero, Submodule.coe_zero,
        TensorProduct.zero_tmul, add_zero]
      rfl)
    (fun a b => by
      rw [dualPointLinear_apply, dualPointLinear_apply, dualPointLinear_apply, D.leibniz,
        Submodule.coe_add, CurveCharts.coe_smulB, CurveCharts.coe_smulB, map_mul]
      simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        DualNumber.eps_mul_eps, TensorProduct.tmul_zero, add_zero, TensorProduct.add_tmul]
      rw [mul_comm (Ch.f0 s b)]
      abel)

/-- `dualPoint Ch D` sends `a` to `f0 a ⊗ 1 + D a ⊗ ε`. -/
theorem dualPoint_apply (D : Derivation k (Ch.S s) (Ch.𝔟 s)) (a : Ch.S s) :
    dualPoint Ch D a = Ch.f0 s a ⊗ₜ 1 + ((D a : Ch.𝔟 s) : Ch.O s) ⊗ₜ DualNumber.eps := rfl

/-- `f0 + ε D` reduces to `f0` modulo the ideal of the marked points. -/
theorem dualPoint_mod (D : Derivation k (Ch.S s) (Ch.𝔟 s)) (z : Ch.S s) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ch.𝔟 s)) (AlgHom.id k _) (dualPoint Ch D z) =
      Ideal.Quotient.mk _ (Ch.f0 s z) ⊗ₜ[k] 1 := by
  rw [dualPoint_apply, map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  change Ideal.Quotient.mk _ (Ch.f0 s z) ⊗ₜ[k] (1 : DualNumber k) +
    Ideal.Quotient.mk (Ch.𝔟 s) ((D z : Ch.𝔟 s) : Ch.O s) ⊗ₜ[k] DualNumber.eps = _
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (D z).2, TensorProduct.zero_tmul, add_zero]

/-- The first-order frame `1 + ε φ`, a unit of `O ⊗ k[ε]`. -/
def dualFrame (φ : Ch.O s) : (Ch.O s ⊗[k] DualNumber k)ˣ where
  val := 1 + φ ⊗ₜ DualNumber.eps
  inv := 1 - φ ⊗ₜ DualNumber.eps
  val_inv := by
    rw [mul_sub, mul_one, add_mul, one_mul, Algebra.TensorProduct.tmul_mul_tmul,
      DualNumber.eps_mul_eps, TensorProduct.tmul_zero, add_zero, add_sub_cancel_right]
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, Algebra.TensorProduct.tmul_mul_tmul,
      DualNumber.eps_mul_eps, TensorProduct.tmul_zero, add_zero, add_sub_cancel_right]

/-- The underlying element of `dualFrame Ch φ` is `1 + φ ⊗ ε`. -/
theorem dualFrame_val (φ : Ch.O s) :
    ((dualFrame Ch φ : (Ch.O s ⊗[k] DualNumber k)ˣ) : Ch.O s ⊗[k] DualNumber k) =
      1 + φ ⊗ₜ DualNumber.eps := rfl

/-- **The first-order frame equation**: if `∑ aₙ wₙ = f0 X` and `∑ vₙ wₙ = φ f0 X + D X`, then
`∑ wₙ ⊗ (aₙ + ε vₙ) = (1 + ε φ)(f0 + ε D)(X)`. -/
theorem sum_tmul_eq_dualFrame_mul {N : ℕ} (D : Derivation k (Ch.S s) (Ch.𝔟 s)) (φ : Ch.O s)
    (w : Fin N → Ch.O s) (a v : Fin N → k) (X : Ch.S s)
    (ha : ∑ n, a n • w n = Ch.f0 s X)
    (hv : ∑ n, v n • w n = φ * Ch.f0 s X + ((D X : Ch.𝔟 s) : Ch.O s)) :
    ∑ n, w n ⊗ₜ[k] (TrivSqZeroExt.inl (a n) + TrivSqZeroExt.inr (v n) : DualNumber k) =
      (dualFrame Ch φ : Ch.O s ⊗[k] DualNumber k) * dualPoint Ch D X := by
  have e : ∀ n, (TrivSqZeroExt.inl (a n) + TrivSqZeroExt.inr (v n) : DualNumber k) =
      a n • (1 : DualNumber k) + v n • DualNumber.eps := fun n => by
    ext <;> simp
  calc ∑ n, w n ⊗ₜ[k] (TrivSqZeroExt.inl (a n) + TrivSqZeroExt.inr (v n) : DualNumber k)
      = ∑ n, ((a n • w n) ⊗ₜ[k] (1 : DualNumber k) + (v n • w n) ⊗ₜ[k] DualNumber.eps) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [e, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    _ = (∑ n, a n • w n) ⊗ₜ[k] (1 : DualNumber k) + (∑ n, v n • w n) ⊗ₜ[k] DualNumber.eps := by
        rw [Finset.sum_add_distrib, TensorProduct.sum_tmul, TensorProduct.sum_tmul]
    _ = _ := by
        rw [ha, hv, dualFrame_val, dualPoint_apply, add_mul, one_mul, mul_add,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          DualNumber.eps_mul_eps, TensorProduct.tmul_zero, add_zero, TensorProduct.add_tmul]
        abel

end FirstOrderPoints

section FirstOrderGluing

open MMP.Fourfold.CurveChartDeformations MMP.Fourfold CechPresheaf

variable {k : Type u} [Field k] {ι : Type u} [DecidableEq ι] (Ch : CurveCharts k ι)
  {d N : ℕ} (x : Fin (d + 1) → ∀ i : ι, Ch.S {i}) (T : ∀ i j : ι, (Ch.S {i, j})ˣ)

/-- A compatible family of derivations of the charts with values in the ideals of the marked
points: one on each nonempty intersection, each extending the others. -/
def IsCompatibleDerivations (D : ∀ s : Finset ι, s.Nonempty → Derivation k (Ch.S s) (Ch.𝔟 s)) :
    Prop :=
  ∀ (s t : Finset ι) (h : s ⊆ t) (hs : s.Nonempty), Ch.extDerB h hs (D s hs) = D t (hs.mono h)

/-- **The obstruction cochain** `(D_{ij}(t_{ij}) / t_{ij})_{ij}` of a compatible family of
derivations, for the transition functions `t_{ij}` of the coordinates. -/
def derivObstruction (D : ∀ s : Finset ι, s.Nonempty → Derivation k (Ch.S s) (Ch.𝔟 s)) :
    Ch.ringPresheaf.C1 := fun i j =>
  ((D {i, j} (Finset.insert_nonempty i {j}) (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) :
    Ch.O {i, j}) * Ch.f0 {i, j} ((T i j)⁻¹ : (Ch.S {i, j})ˣ)

variable {x T}

/-- **First-order gluing**: if the obstruction cochain of `D` is the coboundary of `φ`, the local
expressions `φ_i f0(x_m) + D_i(x_m)` transform by the transition functions. -/
theorem transition_of_d0_eq_derivObstruction
    (hxT : ∀ m i j, Ch.σ (sub_pair_left i j) (x m i) =
      (T i j : Ch.S {i, j}) * Ch.σ (sub_pair_right i j) (x m j))
    (D : ∀ s : Finset ι, s.Nonempty → Derivation k (Ch.S s) (Ch.𝔟 s))
    (hD : IsCompatibleDerivations Ch D) (φ : ∀ i : ι, Ch.O {i})
    (hφ : Ch.ringPresheaf.d0 φ = derivObstruction Ch T D) (m : Fin (d + 1)) (i j : ι) :
    Ch.ρ (sub_pair_left i j) (φ i * Ch.f0 {i} (x m i) +
        ((D {i} (Finset.singleton_nonempty i) (x m i) : Ch.𝔟 {i}) : Ch.O {i})) =
      Ch.f0 {i, j} (T i j : Ch.S {i, j}) * Ch.ρ (sub_pair_right i j) (φ j * Ch.f0 {j} (x m j) +
        ((D {j} (Finset.singleton_nonempty j) (x m j) : Ch.𝔟 {j}) : Ch.O {j})) := by
  have hφij := congrFun (congrFun hφ i) j
  change Ch.ρ (sub_pair_right i j) (φ j) - Ch.ρ (sub_pair_left i j) (φ i) =
    ((D {i, j} _ (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) : Ch.O {i, j}) *
      Ch.f0 {i, j} ((T i j)⁻¹ : (Ch.S {i, j})ˣ) at hφij
  have hDi : ∀ a, ((D {i, j} (Finset.insert_nonempty i {j}) (Ch.σ (sub_pair_left i j) a) :
      Ch.𝔟 {i, j}) : Ch.O {i, j}) =
      Ch.ρ (sub_pair_left i j) ((D {i} (Finset.singleton_nonempty i) a : Ch.𝔟 {i}) : Ch.O {i}) :=
    fun a => by
      rw [← hD _ _ (sub_pair_left i j) (Finset.singleton_nonempty i), Ch.extDerB_apply]
      rfl
  have hDj : ∀ a, ((D {i, j} (Finset.insert_nonempty i {j}) (Ch.σ (sub_pair_right i j) a) :
      Ch.𝔟 {i, j}) : Ch.O {i, j}) =
      Ch.ρ (sub_pair_right i j) ((D {j} (Finset.singleton_nonempty j) a : Ch.𝔟 {j}) : Ch.O {j}) :=
    fun a => by
      rw [← hD _ _ (sub_pair_right i j) (Finset.singleton_nonempty j), Ch.extDerB_apply]
      rfl
  have hunit : Ch.f0 {i, j} (T i j : Ch.S {i, j}) * Ch.f0 {i, j} ((T i j)⁻¹ : (Ch.S {i, j})ˣ) =
      1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hDT := (D {i, j} (Finset.insert_nonempty i {j})).leibniz (T i j : Ch.S {i, j})
    (Ch.σ (sub_pair_right i j) (x m j))
  rw [← hxT] at hDT
  have hDT' := congrArg (fun z : Ch.𝔟 {i, j} => (z : Ch.O {i, j})) hDT
  simp only [Submodule.coe_add, CurveCharts.coe_smulB] at hDT'
  rw [map_add, map_mul, map_add, map_mul, ← Ch.f0_comm, ← hDi, hDT', hxT, map_mul, ← Ch.f0_comm,
    ← hDj]
  have hφ' : Ch.ρ (sub_pair_left i j) (φ i) = Ch.ρ (sub_pair_right i j) (φ j) -
      ((D {i, j} (Finset.insert_nonempty i {j}) (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) :
        Ch.O {i, j}) *
        Ch.f0 {i, j} ((T i j)⁻¹ : (Ch.S {i, j})ˣ) := by
    rw [← hφij]; ring
  rw [hφ']
  linear_combination (-(Ch.f0 {i, j} (Ch.σ (sub_pair_right i j) (x m j)) *
    ((D {i, j} (Finset.insert_nonempty i {j}) (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) :
      Ch.O {i, j}))) * hunit

/-- **The obstruction cochain is a cocycle**, for transition functions satisfying the cocycle
condition. -/
theorem isCocycle_derivObstruction
    (hT : ∀ i j l, Ch.σ (pair_sub_triple₁₂ i j l) (T i j : Ch.S {i, j}) *
      Ch.σ (pair_sub_triple₂₃ i j l) (T j l : Ch.S {j, l}) =
        Ch.σ (pair_sub_triple₁₃ i j l) (T i l : Ch.S {i, l}))
    (D : ∀ s : Finset ι, s.Nonempty → Derivation k (Ch.S s) (Ch.𝔟 s))
    (hD : IsCompatibleDerivations Ch D) :
    Ch.ringPresheaf.IsCocycle (derivObstruction Ch T D) := by
  intro i j l
  have hne : ({i, j, l} : Finset ι).Nonempty := Finset.insert_nonempty i {j, l}
  -- restriction of the derivation values to the triple intersection
  have hres : ∀ (s : Finset ι) (hs : s.Nonempty) (h : s ⊆ {i, j, l}) (a : Ch.S s),
      Ch.ρ h ((D s hs a : Ch.𝔟 s) : Ch.O s) =
        ((D {i, j, l} hne (Ch.σ h a) : Ch.𝔟 {i, j, l}) : Ch.O {i, j, l}) := fun s hs h a => by
    rw [← hD s _ h hs, Ch.extDerB_apply]
    rfl
  have hinv : ∀ (s : Finset ι) (h : s ⊆ {i, j, l}) (u : (Ch.S s)ˣ),
      Ch.σ h (u : Ch.S s) * Ch.σ h ((u⁻¹ : (Ch.S s)ˣ) : Ch.S s) = 1 := fun s h u => by
    rw [← map_mul, Units.mul_inv, map_one]
  change Ch.ρ (pair_sub_triple₂₃ i j l) (((D {j, l} _ (T j l : Ch.S {j, l}) : Ch.𝔟 {j, l}) :
      Ch.O {j, l}) * Ch.f0 {j, l} ((T j l)⁻¹ : (Ch.S {j, l})ˣ)) -
    Ch.ρ (pair_sub_triple₁₃ i j l) (((D {i, l} _ (T i l : Ch.S {i, l}) : Ch.𝔟 {i, l}) :
      Ch.O {i, l}) * Ch.f0 {i, l} ((T i l)⁻¹ : (Ch.S {i, l})ˣ)) +
    Ch.ρ (pair_sub_triple₁₂ i j l) (((D {i, j} _ (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) :
      Ch.O {i, j}) * Ch.f0 {i, j} ((T i j)⁻¹ : (Ch.S {i, j})ˣ)) = 0
  rw [map_mul, map_mul, map_mul, hres, hres, hres, ← Ch.f0_comm, ← Ch.f0_comm, ← Ch.f0_comm,
    ← hT]
  set A := Ch.σ (pair_sub_triple₁₂ i j l) (T i j : Ch.S {i, j})
  set A' := Ch.σ (pair_sub_triple₁₂ i j l) ((T i j)⁻¹ : (Ch.S {i, j})ˣ)
  set B := Ch.σ (pair_sub_triple₂₃ i j l) (T j l : Ch.S {j, l})
  set B' := Ch.σ (pair_sub_triple₂₃ i j l) ((T j l)⁻¹ : (Ch.S {j, l})ˣ)
  set C' := Ch.σ (pair_sub_triple₁₃ i j l) ((T i l)⁻¹ : (Ch.S {i, l})ˣ)
  have hA := hinv _ (pair_sub_triple₁₂ i j l) (T i j)
  have hB := hinv _ (pair_sub_triple₂₃ i j l) (T j l)
  have hC := hinv _ (pair_sub_triple₁₃ i j l) (T i l)
  rw [← hT] at hC
  have hC' : C' = A' * B' := by
    calc C' = C' * ((A * B) * (A' * B')) := by
          rw [show (A * B) * (A' * B') = (A * A') * (B * B') by ring, hA, hB]; ring
      _ = (A * B * C') * (A' * B') := by ring
      _ = A' * B' := by rw [hC, one_mul]
  rw [hC', (D {i, j, l} hne).leibniz, Submodule.coe_add, CurveCharts.coe_smulB,
    CurveCharts.coe_smulB, map_mul]
  have hA0 := congrArg (Ch.f0 {i, j, l}) hA
  have hB0 := congrArg (Ch.f0 {i, j, l}) hB
  rw [map_mul, map_one] at hA0 hB0
  linear_combination
    (-(((D {i, j, l} hne B : Ch.𝔟 {i, j, l}) : Ch.O {i, j, l}) * Ch.f0 {i, j, l} B')) * hA0 -
    (((D {i, j, l} hne A : Ch.𝔟 {i, j, l}) : Ch.O {i, j, l}) * Ch.f0 {i, j, l} A') * hB0

/-- **The tangent count on the charts.** Let `δ` be a linear family of compatible derivations of
the charts, defined on a finite-dimensional space `H` and injective on the singletons. If the
local expressions `w` of a basis glue uniquely, the chart coordinates `x` separate derivations and
`a` (normalized by `μ`) is the tuple of the base map, then there is a subspace `V` of first-order
tuples of dimension at least `dim H - dim Ȟ¹(𝒪)`, each `v ∈ V` solving the first-order frame
equations `∑ₙ vₘₙ wᵢₙ = φᵢ f0(xₘᵢ) + Dᵢ(xₘᵢ)` for some derivations `D` and frames `φ`, with
`μ(v) = 0`. -/
theorem exists_tangentSubspace_of_charts (l : ι → Fin (d + 1))
    (hx1 : ∀ i, x (l i) i = 1)
    (hxT : ∀ m i j, Ch.σ (sub_pair_left i j) (x m i) =
      (T i j : Ch.S {i, j}) * Ch.σ (sub_pair_right i j) (x m j))
    (hT : ∀ i j l, Ch.σ (pair_sub_triple₁₂ i j l) (T i j : Ch.S {i, j}) *
      Ch.σ (pair_sub_triple₂₃ i j l) (T j l : Ch.S {j, l}) =
        Ch.σ (pair_sub_triple₁₃ i j l) (T i l : Ch.S {i, l}))
    (w : ∀ i : ι, Fin N → Ch.O {i})
    (glue : ∀ u : ∀ i : ι, Ch.O {i}, (∀ i j, Ch.ρ (sub_pair_left i j) (u i) =
        Ch.f0 {i, j} (T i j : Ch.S {i, j}) * Ch.ρ (sub_pair_right i j) (u j)) →
      ∃ c : Fin N → k, ∀ i, u i = ∑ n, c n • w i n)
    (glue_unique : ∀ c : Fin N → k, (∀ i, ∑ n, c n • w i n = 0) → c = 0)
    (a : Fin (d + 1) → Fin N → k) (ha : ∀ i m, ∑ n, a m n • w i n = Ch.f0 {i} (x m i))
    (μ : Fin (d + 1) → Fin N → k) (hμ : ∑ m, ∑ n, μ m n * a m n = 1)
    (hxsep : ∀ i (E : Derivation k (Ch.S {i}) (Ch.𝔟 {i})), (∀ m, E (x m i) = 0) → E = 0)
    (H : Type u) [AddCommGroup H] [Module k H] [FiniteDimensional k H]
    (δ : ∀ s : Finset ι, s.Nonempty → H →ₗ[k] Derivation k (Ch.S s) (Ch.𝔟 s))
    (hδ : ∀ X, IsCompatibleDerivations Ch (fun s hs => δ s hs X))
    (hinj : ∀ X, (∀ i, δ {i} (Finset.singleton_nonempty i) X = 0) → X = 0)
    [FiniteDimensional k Ch.ringPresheaf.H1] :
    ∃ V : Submodule k (Fin (d + 1) × Fin N → k),
      (Module.finrank k H : ℤ) - Module.finrank k Ch.ringPresheaf.H1 ≤ Module.finrank k V ∧
      ∀ v ∈ V, ∃ (D : ∀ i : ι, Derivation k (Ch.S {i}) (Ch.𝔟 {i})) (φ : ∀ i : ι, Ch.O {i}),
        (∀ i m, ∑ n, v (m, n) • w i n =
          φ i * Ch.f0 {i} (x m i) + ((D i (x m i) : Ch.𝔟 {i}) : Ch.O {i})) ∧
        ∑ m, ∑ n, μ m n * v (m, n) = 0 := by
  classical
  -- the obstruction class
  let obsL : H →ₗ[k] Ch.ringPresheaf.Z1 :=
    { toFun := fun X => ⟨derivObstruction Ch T (fun s hs => δ s hs X),
        isCocycle_derivObstruction Ch hT _ (hδ X)⟩
      map_add' := fun X Y => Subtype.ext (funext fun i => funext fun j => by
        change ((δ {i, j} _ (X + Y) (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) : Ch.O {i, j}) * _ =
          ((δ {i, j} _ X (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) : Ch.O {i, j}) * _ +
          ((δ {i, j} _ Y (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) : Ch.O {i, j}) * _
        rw [map_add, Derivation.add_apply, Submodule.coe_add, add_mul])
      map_smul' := fun r X => Subtype.ext (funext fun i => funext fun j => by
        change ((δ {i, j} _ (r • X) (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) : Ch.O {i, j}) * _ =
          r • (((δ {i, j} _ X (T i j : Ch.S {i, j}) : Ch.𝔟 {i, j}) : Ch.O {i, j}) * _)
        rw [map_smul, Derivation.smul_apply, Submodule.coe_smul_of_tower, smul_mul_assoc]) }
  let cl : H →ₗ[k] Ch.ringPresheaf.H1 := Ch.ringPresheaf.B1.mkQ ∘ₗ obsL
  set K0 := LinearMap.ker cl with hK0
  have hmemR : ∀ X : K0, ((obsL X : Ch.ringPresheaf.Z1) : Ch.ringPresheaf.C1) ∈
      LinearMap.range Ch.ringPresheaf.d0 := fun X =>
    (Submodule.Quotient.mk_eq_zero Ch.ringPresheaf.B1).1 X.2
  let obsR : K0 →ₗ[k] LinearMap.range Ch.ringPresheaf.d0 :=
    { toFun := fun X => ⟨(obsL X : Ch.ringPresheaf.C1), hmemR X⟩
      map_add' := fun X Y => Subtype.ext (by
        change ((obsL (X + Y : H) : Ch.ringPresheaf.Z1) : Ch.ringPresheaf.C1) = _
        rw [map_add]; rfl)
      map_smul' := fun r X => Subtype.ext (by
        change ((obsL (r • X : H) : Ch.ringPresheaf.Z1) : Ch.ringPresheaf.C1) = _
        rw [map_smul]; rfl) }
  obtain ⟨sR, hsR⟩ := LinearMap.exists_rightInverse_of_surjective
    Ch.ringPresheaf.d0.rangeRestrict (LinearMap.range_rangeRestrict _)
  let φL : K0 →ₗ[k] Ch.ringPresheaf.C0 := sR ∘ₗ obsR
  have hφL : ∀ X : K0, Ch.ringPresheaf.d0 (φL X) =
      derivObstruction Ch T (fun s hs => δ s hs (X : H)) := fun X =>
    (congrArg (fun g => ((g (obsR X) : LinearMap.range Ch.ringPresheaf.d0) :
      Ch.ringPresheaf.C1)) hsR :)
  let φf : K0 → ∀ i : ι, Ch.O {i} := ⇑φL
  -- the local expressions and their gluing
  set u : K0 → Fin (d + 1) → ∀ i : ι, Ch.O {i} := fun X m i =>
    φf X i * Ch.f0 {i} (x m i) +
      ((δ {i} (Finset.singleton_nonempty i) (X : H) (x m i) : Ch.𝔟 {i}) : Ch.O {i}) with hu
  have hglue : ∀ (X : K0) (m : Fin (d + 1)), ∃ c : Fin N → k, ∀ i, u X m i = ∑ n, c n • w i n :=
    fun X m => glue (u X m) fun i j =>
      transition_of_d0_eq_derivObstruction Ch hxT (fun s hs => δ s hs (X : H)) (hδ X)
        (φf X) (hφL X) m i j
  choose vfun hvfun using hglue
  have hsum_sub : ∀ (c c' : Fin N → k) (i : ι),
      ∑ n, (c - c') n • w i n = ∑ n, c n • w i n - ∑ n, c' n • w i n := fun c c' i => by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have hsum_add : ∀ (c c' : Fin N → k) (i : ι),
      ∑ n, (c + c') n • w i n = ∑ n, c n • w i n + ∑ n, c' n • w i n := fun c c' i => by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hsum_smul : ∀ (r : k) (c : Fin N → k) (i : ι),
      ∑ n, (r • c) n • w i n = r • ∑ n, c n • w i n := fun r c i => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hφf_add : ∀ (X Y : K0) i, φf (X + Y) i = φf X i + φf Y i := fun X Y i =>
    congrFun (map_add φL X Y) i
  have hφf_smul : ∀ (r : k) (X : K0) i, φf (r • X) i = r • φf X i := fun r X i =>
    congrFun (map_smul φL r X) i
  have hu_add : ∀ (X Y : K0) m i, u (X + Y) m i = u X m i + u Y m i := fun X Y m i => by
    simp only [hu, hφf_add, Submodule.coe_add, map_add, Derivation.add_apply, add_mul]
    abel
  have hu_smul : ∀ (r : k) (X : K0) m i, u (r • X) m i = r • u X m i := fun r X m i => by
    simp only [hu, hφf_smul, map_smul, Submodule.coe_smul_of_tower, Derivation.smul_apply,
      smul_add, smul_mul_assoc]
  let vL : K0 →ₗ[k] (Fin (d + 1) → Fin N → k) :=
    { toFun := vfun
      map_add' := fun X Y => funext fun m => sub_eq_zero.1 (glue_unique _ fun i => by
        rw [hsum_sub, Pi.add_apply, hsum_add, ← hvfun, ← hvfun, ← hvfun, hu_add, sub_self])
      map_smul' := fun r X => funext fun m => sub_eq_zero.1 (glue_unique _ fun i => by
        rw [hsum_sub, RingHom.id_apply, Pi.smul_apply, hsum_smul, ← hvfun, ← hvfun, hu_smul,
          sub_self]) }
  let lamL : K0 →ₗ[k] k :=
    { toFun := fun X => ∑ m, ∑ n, μ m n * vL X m n
      map_add' := fun X Y => by
        simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r X => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring }
  let L : K0 →ₗ[k] (Fin (d + 1) × Fin N → k) :=
    { toFun := fun X p => vL X p.1 p.2 - lamL X * a p.1 p.2
      map_add' := fun X Y => funext fun p => by
        simp only [map_add, Pi.add_apply]; ring
      map_smul' := fun r X => funext fun p => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  -- the first-order equations of the tuples
  have hLeq : ∀ (X : K0) i m, ∑ n, L X (m, n) • w i n =
      (φf X i - algebraMap k (Ch.O {i}) (lamL X)) * Ch.f0 {i} (x m i) +
        ((δ {i} (Finset.singleton_nonempty i) (X : H) (x m i) : Ch.𝔟 {i}) : Ch.O {i}) :=
    fun X i m => by
      change ∑ n, (vL X m n - lamL X * a m n) • w i n = _
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ha]
      rw [show ∑ n, vL X m n • w i n = u X m i from (hvfun X m i).symm, sub_mul,
        Algebra.smul_def]
      change φf X i * Ch.f0 {i} (x m i) + _ - _ = _
      ring
  have hLμ : ∀ X : K0, ∑ m, ∑ n, μ m n * L X (m, n) = 0 := fun X => by
    change ∑ m, ∑ n, μ m n * (vL X m n - lamL X * a m n) = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [show ∑ m, ∑ n, μ m n * (lamL X * a m n) = lamL X * ∑ m, ∑ n, μ m n * a m n by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_; ring, hμ, mul_one]
    exact sub_self _
  -- injectivity
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have hφ0 : ∀ i, φf X i - algebraMap k (Ch.O {i}) (lamL X) = 0 := fun i => by
      have h := hLeq X i (l i)
      rw [hX, hx1, map_one, mul_one, Derivation.map_one_eq_zero, Submodule.coe_zero, add_zero]
        at h
      simpa using h.symm
    have hD0 : ∀ i, δ {i} (Finset.singleton_nonempty i) (X : H) = 0 := fun i =>
      hxsep i _ fun m => Subtype.ext (by
        have h := hLeq X i m
        rw [hX, hφ0, zero_mul, zero_add] at h
        simpa using h.symm)
    exact Subtype.ext (hinj _ hD0)
  refine ⟨LinearMap.range L, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_of_inj hLinj
    have h2 := LinearMap.finrank_range_add_finrank_ker cl
    rw [← hK0] at h2
    have h3 : Module.finrank k (LinearMap.range cl) ≤ Module.finrank k Ch.ringPresheaf.H1 :=
      Submodule.finrank_le _
    rw [h1]
    omega
  · rintro v ⟨X, rfl⟩
    exact ⟨fun i => δ {i} (Finset.singleton_nonempty i) (X : H),
      fun i => φf X i - algebraMap k (Ch.O {i}) (lamL X), fun i m => hLeq X i m, hLμ X⟩

end FirstOrderGluing

section ChartCoordinates

open AlgebraicGeometry Limits Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion
  Stacks.TwistPullbackPinned Stacks.SectionsToProjectiveSpace
open Stacks.Ample (IsInvertibleModule)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

variable {k : Type u} [Field k] {U : Scheme.{u}} (sU : U ⟶ Spec (.of k)) {d : ℕ}
  (e : U ⟶ projectiveSpaceOver d (Spec (.of k)))

/-- **The chart coordinates separate points with values in rings.** For a monomorphism
`e : U ⟶ ℙᵈ_k` and an affine open `W` of `U` inside the chart `σ_l ≠ 0` of the pulled-back
coordinates `σ`, two `k`-algebra maps `Γ(U, W) → R` agreeing on the ratios `σ_m / σ_l` are
equal. -/
theorem algHom_ext_of_ratio [Mono e] (he : e ≫ pullback.fst _ _ = sU)
    [IsInvertibleModule U ((Scheme.Modules.pullback
      (e ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} d))]
    (l : Fin (d + 1)) {W : U.Opens} (hW : IsAffineOpen W)
    (hWl : W ≤ nvCover (pullbackCoordSection.{u}
      (e ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) l)
    {R : Type u} [CommRing R] [Algebra k R] :
    letI := CurveMapCharts.sectionsAlgebra sU W
    ∀ y y' : Γ(U, W) →ₐ[k] R, (∀ m, y (resO hWl (ratio (pullbackCoordSection.{u}
        (e ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) l m)) =
        y' (resO hWl (ratio (pullbackCoordSection.{u}
          (e ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)))) l m))) → y = y' := by
  let := CurveMapCharts.sectionsAlgebra sU W
  intro y y' h
  set g := e ≫ projectiveSpaceOver.toIntegralAtUniverse d (Spec (.of k)) with hg
  set Dp := Proj.basicOpen (coordGrading.{u} d) (MvPolynomial.X l) with hDp
  have hle := MMP.Fourfold.nvCover_le_preimage_basicOpen_of_pinned (pullbackCoordSection.{u} g) g
    (𝟙 _) (fun _ => rfl) l
  have hWD : W ≤ g ⁻¹ᵁ Dp := hWl.trans hle
  have hW' : ∀ ψ : Γ(U, W) ⟶ CommRingCat.of R,
      (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (Spec.map ψ ≫ hW.fromSpec) ⁻¹ᵁ W :=
    fun ψ x _ => by
      have : (Spec.map ψ).base x ∈ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self ▸ trivial
      exact this
  have key : ∀ ψ : Γ(U, W) ⟶ CommRingCat.of R,
      (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (Spec.map ψ ≫ hW.fromSpec ≫ g) ⁻¹ᵁ Dp :=
    fun ψ x hx => by
      have h1 : (Spec.map ψ ≫ hW.fromSpec).base x ∈ W := hW' ψ hx
      exact hWD h1
  have happ : ∀ ψ : Γ(U, W) ⟶ CommRingCat.of R,
      (Spec.map ψ ≫ hW.fromSpec ≫ g).appLE Dp ⊤ (key ψ) =
        g.appLE Dp W hWD ≫ ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv := fun ψ => by
    have e1 := Scheme.Hom.appLE_comp_appLE (Spec.map ψ ≫ hW.fromSpec) g Dp W ⊤ hWD (hW' ψ)
    have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map ψ) hW.fromSpec W ⊤ ⊤
      (le_of_eq hW.fromSpec_preimage_self.symm) le_top
    simp only [Category.assoc] at e1
    rw [← e1, ← e2, Stacks.AlgebraicGeometry.AffineDifferentialsIso.fromSpec_appLE_top hW]
    congr 1
    have e3 : (Spec.map ψ).appLE ⊤ ⊤ le_top = (Spec.map ψ).appTop := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
      change (Spec.map ψ).app ⊤ ≫ (Spec (CommRingCat.of R)).presheaf.map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [e3, Scheme.ΓSpecIso_inv_naturality]
  have hcoord : ∀ m, (g.appLE Dp W hWD).hom ((Proj.awayToSection (coordGrading.{u} d)
      (MvPolynomial.X l)).hom (coordFrac.{u} l m)) =
      resO hWl (ratio (pullbackCoordSection.{u} g) l m) := fun m => by
    have e1 := Scheme.Hom.appLE_map g hle (homOfLE hWl).op
    rw [← e1, CommRingCat.comp_apply, MMP.Fourfold.appLE_coordFrac_of_pinned
      (pullbackCoordSection.{u} g) g (𝟙 _) (fun _ => rfl) l m]
  have h2 : Spec.map (CommRingCat.ofHom y.toRingHom) ≫ hW.fromSpec ≫ g =
      Spec.map (CommRingCat.ofHom y'.toRingHom) ≫ hW.fromSpec ≫ g := by
    refine MMP.Fourfold.hom_ext_projectiveSpace_of_appLE_coordFrac l _ _ (key _) (key _)
      fun m => ?_
    rw [happ, happ]
    simp only [CommRingCat.comp_apply, hcoord]
    exact congrArg _ (h m)
  have hbase : sU.appLE ⊤ W (fun _ _ => trivial) ≫ CommRingCat.ofHom y.toRingHom =
      sU.appLE ⊤ W (fun _ _ => trivial) ≫ CommRingCat.ofHom y'.toRingHom := by
    ext r
    obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso (toSpecΓ (CommRingCat.of k))).2 r
    have hx : (sU.appLE ⊤ W (fun _ _ => trivial)).hom ((toSpecΓ (CommRingCat.of k)).hom r) =
        algebraMap k Γ(U, W) r := by
      change _ = (Stacks.Cech.baseRingHom sU W).hom r
      rw [Stacks.Cech.baseRingHom_eq_appLE sU W (fun _ _ => trivial)]
      rfl
    change y ((sU.appLE ⊤ W (fun _ _ => trivial)).hom ((toSpecΓ (CommRingCat.of k)).hom r)) =
      y' ((sU.appLE ⊤ W (fun _ _ => trivial)).hom ((toSpecΓ (CommRingCat.of k)).hom r))
    rw [hx, y.commutes, y'.commutes]
  have h1 : Spec.map (CommRingCat.ofHom y.toRingHom) ≫ hW.fromSpec ≫ sU =
      Spec.map (CommRingCat.ofHom y'.toRingHom) ≫ hW.fromSpec ≫ sU := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec sU (isAffineOpen_top _) hW (fun _ _ => trivial),
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hbase]
  have h3 : Spec.map (CommRingCat.ofHom y.toRingHom) ≫ hW.fromSpec =
      Spec.map (CommRingCat.ofHom y'.toRingHom) ≫ hW.fromSpec := by
    refine (cancel_mono e).1 (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, he]
      exact h1
    · simpa only [Category.assoc] using h2
  exact AlgHom.ext fun a => congrArg (fun φ : Γ(U, W) ⟶ CommRingCat.of R => φ.hom a)
    (Spec.map_injective ((cancel_mono hW.fromSpec).1 h3))

end ChartCoordinates

section DualNumbers

open IsLocalRing

variable (k : Type u) [Field k]

/-- **The dual numbers `k[ε]` as a local Artinian `k`-algebra with residue field `k`.** -/
def dualNumberArtin : ArtinLocalAlgebra k where
  carrier := DualNumber k
  isArtinianRing := by
    have : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
    exact IsArtinianRing.of_finite k (DualNumber k)
  residue_bijective := by
    refine ⟨(algebraMap k (ResidueField (DualNumber k))).injective, fun z => ?_⟩
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    refine ⟨x.fst, ?_⟩
    have hx : x = algebraMap k (DualNumber k) x.fst + TrivSqZeroExt.inr x.snd := by
      rw [TrivSqZeroExt.algebraMap_eq_inl]
      ext <;> simp
    have hnil : TrivSqZeroExt.inr x.snd ∈ maximalIdeal (DualNumber k) := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact not_isUnit_zero (TrivSqZeroExt.inr_mul_inr k x.snd x.snd ▸ hu.mul hu)
    conv_rhs => rw [hx]
    rw [map_add, (IsLocalRing.residue_eq_zero_iff _).2 hnil, add_zero]
    rfl

/-- If `o ⊗ ε = 0` in `O ⊗[k] k[ε]`, then `o = 0`. -/
theorem eq_zero_of_tmul_eps_eq_zero {k : Type*} [CommSemiring k] {O : Type*} [AddCommMonoid O]
    [Module k O] (o : O)
    (h : o ⊗ₜ[k] (DualNumber.eps : DualNumber k) = 0) : o = 0 := by
  simpa using congrArg (fun z => TensorProduct.rid k O
    (LinearMap.lTensor O (TrivSqZeroExt.sndHom k k) z)) h

end DualNumbers

section DualSeparation

open MMP.Fourfold.CurveChartDeformations

variable {k : Type u} [Field k] {ι : Type u} (Ch : CurveCharts k ι) {s : Finset ι}

/-- A derivation whose first-order deformation `f0 + ε D` is `f0` vanishes. -/
theorem eq_zero_of_dualPoint_eq (D : Derivation k (Ch.S s) (Ch.𝔟 s))
    (h : dualPoint Ch D = dualPoint Ch 0) : D = 0 := by
  ext a
  have h1 := congrArg (fun y : Ch.S s →ₐ[k] Ch.O s ⊗[k] DualNumber k => y a) h
  simp only [dualPoint_apply, Derivation.zero_apply, Submodule.coe_zero, TensorProduct.zero_tmul,
    add_zero, add_eq_left] at h1
  exact eq_zero_of_tmul_eps_eq_zero _ h1

end DualSeparation

section CotangentPoints

open IsLocalRing

variable {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]

/-- A `k[ε]`-point of a local `k`-algebra kills the maximal ideal modulo `ε`. -/
theorem fst_apply_eq_zero_of_mem_maximalIdeal (φ : R →ₐ[k] DualNumber k) {x : R}
    (hx : x ∈ maximalIdeal R) : (φ x).fst = 0 := by
  let ψ : R →ₐ[k] k := (TrivSqZeroExt.fstHom k k k).comp φ
  have hs : Function.Surjective ψ := fun c => ⟨algebraMap k R c, by simp [ψ]⟩
  rw [← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hs)] at hx
  exact hx

/-- A `k[ε]`-point of a local `k`-algebra kills the square of the maximal ideal. -/
theorem snd_apply_mul_eq_zero_of_mem_maximalIdeal (φ : R →ₐ[k] DualNumber k) {x y : R}
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) : (φ (x * y)).snd = 0 := by
  rw [map_mul, TrivSqZeroExt.snd_mul, fst_apply_eq_zero_of_mem_maximalIdeal φ hx,
    fst_apply_eq_zero_of_mem_maximalIdeal φ hy]
  simp

/-- The tangent functional on `𝔪` of a `k[ε]`-point. -/
def tangentFunctional (φ : R →ₗ[k] DualNumber k) : maximalIdeal R →ₗ[k] k :=
  (TrivSqZeroExt.sndHom k k).comp (φ.comp ((maximalIdeal R).restrictScalars k).subtype)

/-- The tangent functional of a `k[ε]`-point kills `𝔪²`. -/
theorem le_ker_tangentFunctional (φ : R →ₐ[k] DualNumber k) :
    ((maximalIdeal R) • (⊤ : Submodule R (maximalIdeal R))).restrictScalars k ≤
      LinearMap.ker (tangentFunctional φ.toLinearMap) := by
  intro x hx
  change x ∈ (maximalIdeal R) • (⊤ : Submodule R (maximalIdeal R)) at hx
  rw [LinearMap.mem_ker]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr n _
    change (φ (r * (n : R))).snd = 0
    exact snd_apply_mul_eq_zero_of_mem_maximalIdeal φ hr n.2
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- The tangent functional on `𝔪/𝔪²` of a `k[ε]`-point. -/
def cotangentFunctional (φ : R →ₐ[k] DualNumber k) : CotangentSpace R →ₗ[k] k :=
  (Submodule.liftQ _ (tangentFunctional φ.toLinearMap) (le_ker_tangentFunctional φ)).comp
    (Submodule.Quotient.restrictScalarsEquiv k
      ((maximalIdeal R) • (⊤ : Submodule R (maximalIdeal R)))).symm.toLinearMap

/-- The cotangent functional of a `k[ε]`-point on the class of `x ∈ 𝔪` is the `ε`-part of `x`. -/
@[simp]
theorem cotangentFunctional_toCotangent (φ : R →ₐ[k] DualNumber k) (x : maximalIdeal R) :
    cotangentFunctional φ ((maximalIdeal R).toCotangent x) = (φ x).snd := rfl

/-- **Tangent vectors from coordinates.** If `t : ι → 𝔪` and every `v` in the subspace `V` of
`ι → k` is the vector of `ε`-parts `(φ(t_l))_l` of some `k[ε]`-point `φ`, then
`dim V ≤ dim 𝔪/𝔪²`. -/
theorem finrank_le_finrank_cotangentSpace_of_coords
    (hk : Function.Bijective (algebraMap k (ResidueField R))) [IsNoetherianRing R]
    {ι : Type*} [Finite ι] (t : ι → maximalIdeal R) (V : Submodule k (ι → k))
    (hV : ∀ v ∈ V, ∃ φ : R →ₐ[k] DualNumber k, ∀ l, (φ (t l)).snd = v l) :
    Module.finrank k V ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
  have := Fintype.ofFinite ι
  let Ψ : Module.Dual k (CotangentSpace R) →ₗ[k] (ι → k) :=
    LinearMap.pi fun l => LinearMap.applyₗ ((maximalIdeal R).toCotangent (t l))
  have hle : V ≤ LinearMap.range Ψ := by
    intro v hv
    obtain ⟨φ, hφ⟩ := hV v hv
    exact ⟨cotangentFunctional φ, funext fun l => (hφ l)⟩
  let e : k ≃ₗ[k] ResidueField R := LinearEquiv.ofBijective (Algebra.linearMap k _) hk
  have : Module.Finite k (ResidueField R) := Module.Finite.equiv e
  have : IsScalarTower k (ResidueField R) (CotangentSpace R) :=
    IsScalarTower.of_algebraMap_smul fun c z => by
      rw [IsScalarTower.algebraMap_apply k R (ResidueField R), algebraMap_smul, algebraMap_smul]
  have : Module.Finite k (CotangentSpace R) := Module.Finite.trans (ResidueField R) _
  have h1 : Module.finrank k (ResidueField R) = 1 := by
    rw [← e.finrank_eq, Module.finrank_self]
  have h2 := Module.finrank_mul_finrank k (ResidueField R) (CotangentSpace R)
  rw [h1, one_mul] at h2
  have h3 := Submodule.finrank_mono hle
  have h4 := LinearMap.finrank_range_le Ψ
  rw [Subspace.dual_finrank_eq] at h4
  omega

/-- `finrank_le_finrank_cotangentSpace_of_coords` for elements `t l` of `R` with prescribed
residues `t₀ l`. -/
theorem finrank_le_finrank_cotangentSpace_of_values
    (hk : Function.Bijective (algebraMap k (ResidueField R))) [IsNoetherianRing R]
    {ι : Type*} [Finite ι] (t : ι → R) (t₀ : ι → k) (V : Submodule k (ι → k))
    (hV : ∀ v ∈ V, ∃ φ : R →ₐ[k] DualNumber k, ∀ l,
      φ (t l) = TrivSqZeroExt.inl (t₀ l) + TrivSqZeroExt.inr (v l)) :
    Module.finrank k V ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
  obtain ⟨φ₀, hφ₀⟩ := hV 0 V.zero_mem
  have hmem : ∀ l, t l - algebraMap k R (t₀ l) ∈ maximalIdeal R := by
    intro l
    let ψ : R →ₐ[k] k := (TrivSqZeroExt.fstHom k k k).comp φ₀
    have hs : Function.Surjective ψ := fun c => ⟨algebraMap k R c, by simp [ψ]⟩
    rw [← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hs)]
    change ψ (t l - algebraMap k R (t₀ l)) = 0
    simp [ψ, hφ₀ l, TrivSqZeroExt.algebraMap_eq_inl]
  refine finrank_le_finrank_cotangentSpace_of_coords hk (fun l => ⟨_, hmem l⟩) V ?_
  intro v hv
  obtain ⟨φ, hφ⟩ := hV v hv
  refine ⟨φ, fun l => ?_⟩
  change (φ (t l - algebraMap k R (t₀ l))).snd = v l
  rw [map_sub, hφ l, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl]
  simp

end CotangentPoints

end MMP.Fourfold.CurveMapDerivations
