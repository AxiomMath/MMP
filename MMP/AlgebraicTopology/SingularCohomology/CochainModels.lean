module

public import MMP.AlgebraicTopology.ThomClass.Natural
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder

/-!
# Two models of rational singular cohomology

The rational singular cohomology of a space `Y` has two models in this library. One is the
cohomology of the complex `Hom_ℤ(C_•(Y; ℤ), ℚ)` of abelian groups, built from Mathlib's singular
chain complex with integral coefficients and the Yoneda functor `Hom(-, ℚ)`; this is the form in
which sheaf cohomology of the constant sheaf on a locally contractible space is compared with
singular cohomology. The other is the cohomology `H^n(Y, ∅; ℚ)` of the pair `(Y, ∅)`
(`MMP.relativeSingularCohomology`), with `ℚ`-linear cochains, which is the form in
which Thom classes, Gysin maps and cup products are developed.

Both are the cohomology of the complex of `ℚ`-valued functions on singular simplices with the
alternating coboundary: a homomorphism out of the free abelian group on the `n`-simplices is
its values on the simplices. Under this identification the pull-back along a continuous map is
precomposition of simplices. So the two cohomology groups are isomorphic, naturally in `Y`.

## Main definitions

* `MMP.Topology.SingularCochain.cochainEval`: an integral singular cochain as a function on
  simplices.
* `MMP.Topology.SingularCochain.abCochainIso`: the complex `Hom_ℤ(C_•(Y; ℤ), ℚ)` is the complex
  of functions on simplices vanishing on the empty set.
* `MMP.Topology.SingularCochain.abCohomologyIso`: `H^n(Hom_ℤ(C_•(Y; ℤ), ℚ)) ≅ Z^n(Y, ∅)/B^n(Y, ∅)`.

## Main results

* `MMP.Topology.SingularCochain.abCohomologyIso_hom_naturality`: the isomorphism is natural in `Y`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Simplicial
open MMP MMP.SingularCochain MMP.SingularChain

namespace MMP.Topology.SingularCochain

/-- The singular chain complex of `Y` with integral coefficients, as abelian groups. -/
abbrev abChains (Y : TopCat.{0}) : ChainComplex AddCommGrpCat.{0} ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))).obj Y

/-- The cochain complex `Hom_ℤ(C_•(Y; ℤ), ℚ)` of rational singular cochains, as a functor of the
space. -/
abbrev abCochainFunctor : TopCat.{0}ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))).op ⋙
    HomologicalComplex.opFunctor _ _ ⋙
      (preadditiveYoneda.obj (AddCommGrpCat.of ℚ)).mapHomologicalComplex _

/-- The value of an integral singular cochain on a singular simplex. -/
def cochainEval {Y : TopCat.{0}} {n : ℕ} (φ : (abChains Y).X n ⟶ AddCommGrpCat.of ℚ)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) : ℚ :=
  (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ φ).hom ⟨1⟩

/-- The integral singular cochain with prescribed values on simplices. -/
def cochainOfFun {Y : TopCat.{0}} {n : ℕ} (g : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) → ℚ) :
    (abChains Y).X n ⟶ AddCommGrpCat.of ℚ :=
  Sigma.desc fun σ ↦ AddCommGrpCat.ofHom
    { toFun := fun k ↦ k.down • g σ
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [add_smul] }

/-- The cochain with prescribed values `g` takes the value `g σ` on the simplex `σ`. -/
@[simp]
lemma cochainEval_cochainOfFun {Y : TopCat.{0}} {n : ℕ}
    (g : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) → ℚ) (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    cochainEval (cochainOfFun g) σ = g σ := by
  change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ cochainOfFun g).hom ⟨1⟩ = g σ
  simp [cochainOfFun]

/-- An integral singular cochain is determined by its values on simplices. -/
@[simp]
lemma cochainOfFun_cochainEval {Y : TopCat.{0}} {n : ℕ}
    (φ : (abChains Y).X n ⟶ AddCommGrpCat.of ℚ) :
    cochainOfFun (cochainEval φ) = φ := by
  refine Sigma.hom_ext _ _ fun σ ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun k ↦ ?_)
  change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ cochainOfFun (cochainEval φ)).hom k = _
  rw [cochainOfFun, Sigma.ι_desc]
  change k.down • cochainEval φ σ = (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ φ).hom k
  conv_rhs => rw [show k = k.down • (⟨1⟩ : ULift ℤ) by ext; simp]
  rw [map_zsmul]
  rfl

/-- The value of a sum of cochains on a simplex is the sum of their values. -/
@[simp]
lemma cochainEval_add {Y : TopCat.{0}} {n : ℕ} (φ ψ : (abChains Y).X n ⟶ AddCommGrpCat.of ℚ)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    cochainEval (φ + ψ) σ = cochainEval φ σ + cochainEval ψ σ := by
  simp only [cochainEval, Preadditive.comp_add]
  rfl

private lemma hom_sum' {M N : AddCommGrpCat.{0}} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N))
    (x : M) : (∑ i ∈ s, f i).hom x = ∑ i ∈ s, (f i).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add]
    simp [ih]

/-- The boundary of the generator of an `(n + 1)`-simplex `σ` is the alternating sum of the
generators of its faces `δ i σ`. -/
@[reassoc]
lemma ι_abChains_d {Y : TopCat.{0}} {n : ℕ} (σ : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌)) :
    Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ (abChains Y).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) ((TopCat.toSSet.obj Y).δ i σ) := by
  have : (abChains Y).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      SimplicialObject.δ (TopCat.toSSet.obj Y ⋙ sigmaConst.obj (AddCommGrpCat.of (ULift ℤ))) i :=
    AlternatingFaceMapComplex.obj_d_eq _ n
  rw [this]
  erw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Preadditive.comp_zsmul]
  congr 1
  simp only [SimplicialObject.δ, sigmaConst]
  erw [Sigma.ι_comp_map', Category.id_comp]

/-- The value of the coboundary of a cochain `φ` on an `(n + 1)`-simplex `σ` is the alternating
sum of the values of `φ` on the faces of `σ`. -/
lemma cochainEval_d {Y : TopCat.{0}} {n : ℕ} (φ : (abChains Y).X n ⟶ AddCommGrpCat.of ℚ)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌)) :
    cochainEval ((abChains Y).d (n + 1) n ≫ φ) σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • cochainEval φ ((TopCat.toSSet.obj Y).δ i σ) := by
  unfold cochainEval
  change (Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫ (abChains Y).d (n + 1) n ≫ φ).hom ⟨1⟩ =
    _
  erw [ι_abChains_d_assoc, Preadditive.sum_comp]
  rw [hom_sum']
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [Preadditive.zsmul_comp]
  simp
  rfl

/-- The value of the pull-back of a cochain `φ` along `f` on a simplex `σ` is the value of `φ` on
the composite simplex `f ∘ σ`. -/
lemma cochainEval_map {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {n : ℕ}
    (φ : (abChains Y).X n ⟶ AddCommGrpCat.of ℚ) (σ : (TopCat.toSSet.obj Y').obj (op ⦋n⦌)) :
    cochainEval ((((singularChainComplexFunctor AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift ℤ))).map f).f n ≫ φ) σ =
      cochainEval φ ((TopCat.toSSet.map f).app _ σ) := by
  unfold cochainEval
  have : Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) σ ≫
      (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))).map f).f
        n =
      Sigma.ι (fun _ ↦ AddCommGrpCat.of (ULift ℤ)) ((TopCat.toSSet.map f).app _ σ) := by
    dsimp [singularChainComplexFunctor, SSet.chainComplexFunctor]
    simp [Sigma.ι_comp_map']
  erw [← Category.assoc, this]
  rfl

/-- Every function on simplices vanishes on the simplices of the empty set. -/
lemma mem_vanishing_compl_univ {Y : TopCat.{0}} {n : ℕ} (g : Simplex Y n → ℚ) :
    g ∈ vanishing ℚ n ((Set.univ : Set Y)ᶜ) := fun σ hσ ↦
  absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp)

/-- The additive equivalence between integral singular `n`-cochains and `ℚ`-valued functions on
`n`-simplices vanishing on the simplices of `∅`, given by evaluation on simplices. -/
def abCochainEquiv (Y : TopCat.{0}) (n : ℕ) :
    ((abChains Y).X n ⟶ AddCommGrpCat.of ℚ) ≃+ vanishing ℚ n ((Set.univ : Set Y)ᶜ) where
  toFun φ := ⟨fun τ ↦ cochainEval φ ((simplexEquiv Y n).symm τ), mem_vanishing_compl_univ _⟩
  invFun g := cochainOfFun fun σ ↦ (g : Simplex Y n → ℚ) (simplexEquiv Y n σ)
  left_inv φ := by
    change cochainOfFun (fun σ ↦ cochainEval φ ((simplexEquiv Y n).symm (simplexEquiv Y n σ))) = φ
    simpa only [Equiv.symm_apply_apply] using cochainOfFun_cochainEval φ
  right_inv g := Subtype.ext <| funext fun _ ↦ by
    change cochainEval (cochainOfFun _) _ = _
    rw [cochainEval_cochainOfFun, Equiv.apply_symm_apply]
  map_add' φ ψ := Subtype.ext <| funext fun _ ↦ cochainEval_add φ ψ _

/-- The function on simplices attached to an integral cochain `φ` takes the value of `φ` on the
corresponding singular simplex. -/
@[simp]
lemma abCochainEquiv_apply (Y : TopCat.{0}) (n : ℕ) (φ : (abChains Y).X n ⟶ AddCommGrpCat.of ℚ)
    (τ : Simplex Y n) :
    (abCochainEquiv Y n φ : Simplex Y n → ℚ) τ = cochainEval φ ((simplexEquiv Y n).symm τ) :=
  rfl

/-- The complex `Hom_ℤ(C_•(Y; ℤ), ℚ)` is the complex of `ℚ`-valued functions on
simplices vanishing on `∅`. -/
def abCochainIso (Y : TopCat.{0}) :
    abCochainFunctor.obj (op Y) ≅
      ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex _).obj
        (relComplex ℚ ((Set.univ : Set Y)ᶜ)) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ (abCochainEquiv Y n).toAddCommGrpIso)
    (by
      rintro i j (rfl : i + 1 = j)
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ Subtype.ext (funext fun τ ↦ ?_))
      change (vanishing ℚ (i + 1) _).subtype (((relComplex ℚ _).d i (i + 1)).hom
          (abCochainEquiv Y i φ)) τ =
        (abCochainEquiv Y (i + 1) ((abChains Y).d (i + 1) i ≫ φ) : Simplex Y (i + 1) → ℚ) τ
      refine (congrFun (relComplex_d_apply ℚ _ i (abCochainEquiv Y i φ)) τ).trans ?_
      refine Eq.trans ?_ (cochainEval_d φ ((simplexEquiv Y (i + 1)).symm τ)).symm
      rw [coboundary_apply]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [zsmul_eq_mul, simplexEquiv_symm_δ]
      push_cast
      rfl)

/-- `H^n(Hom_ℤ(C_•(Y; ℤ), ℚ))` is the group `Z^n(Y, ∅)/B^n(Y, ∅)` of rational cocycles on
simplices modulo coboundaries. -/
def abCohomologyIso (Y : TopCat.{0}) (n : ℕ) :
    (abCochainFunctor.obj (op Y)).homology n ≅
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj
        (ModuleCat.of ℚ (relCohomology ℚ ((Set.univ : Set Y)ᶜ) n)) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (abCochainIso Y) ≪≫
    (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}) _ n).app _ ≪≫
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapIso
      (relHomologyEquiv ℚ ((Set.univ : Set Y)ᶜ) n).toModuleIso

/-- The empty subspace of `Y'` is contained in the preimage of the empty subspace of `Y`. -/
lemma compl_univ_subset_preimage {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) :
    (Set.univ : Set Y')ᶜ ⊆ f ⁻¹' (Set.univ : Set Y)ᶜ := by
  simp

/-- The identification of the two cochain complexes is natural in the space. -/
@[reassoc]
lemma abCochainIso_hom_naturality {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) :
    abCochainFunctor.map f.op ≫ (abCochainIso Y').hom =
      (abCochainIso Y).hom ≫ ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex
        _).map (relComplexMap ℚ f (compl_univ_subset_preimage f)) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦
    AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ Subtype.ext (funext fun τ ↦ ?_))
  change cochainEval ((((singularChainComplexFunctor AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift ℤ))).map f).f n ≫ φ) ((simplexEquiv Y' n).symm τ) =
    cochainEval φ ((simplexEquiv Y n).symm (f.hom.comp τ))
  exact (cochainEval_map f φ _).trans rfl

/-- The identification of the two models of rational singular cohomology is natural in the
space: it carries the pull-back of integral cochains to the pull-back of cocycles modulo
coboundaries. -/
theorem abCohomologyIso_hom_naturality {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (abCochainFunctor.map f.op) n ≫ (abCohomologyIso Y' n).hom =
      (abCohomologyIso Y n).hom ≫ (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        (ModuleCat.ofHom (relCohomologyMap ℚ f (compl_univ_subset_preimage f) n)) := by
  let F := forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}
  let g := relComplexMap ℚ f (compl_univ_subset_preimage f)
  have h1 : HomologicalComplex.homologyMap (abCochainFunctor.map f.op) n ≫
      HomologicalComplex.homologyMap (abCochainIso Y').hom n =
      HomologicalComplex.homologyMap (abCochainIso Y).hom n ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map g) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      abCochainIso_hom_naturality]
  have h2 := (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso F
    (ComplexShape.up ℕ) n).hom.naturality g
  have h3 : F.map (HomologicalComplex.homologyMap g n) ≫
      F.map (relHomologyEquiv ℚ ((Set.univ : Set Y')ᶜ) n).toModuleIso.hom =
      F.map (relHomologyEquiv ℚ ((Set.univ : Set Y)ᶜ) n).toModuleIso.hom ≫
        F.map (ModuleCat.ofHom (relCohomologyMap ℚ f (compl_univ_subset_preimage f) n)) := by
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    ext x
    exact relHomologyEquiv_naturality (R := ℚ) f (compl_univ_subset_preimage f) n x
  let C' := (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso F
    (ComplexShape.up ℕ) n).hom.app (relComplex ℚ ((Set.univ : Set Y')ᶜ))
  let C := (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso F
    (ComplexShape.up ℕ) n).hom.app (relComplex ℚ ((Set.univ : Set Y)ᶜ))
  let D' := F.map (relHomologyEquiv ℚ ((Set.univ : Set Y')ᶜ) n).toModuleIso.hom
  let D := F.map (relHomologyEquiv ℚ ((Set.univ : Set Y)ᶜ) n).toModuleIso.hom
  let E := F.map (ModuleCat.ofHom (relCohomologyMap ℚ f (compl_univ_subset_preimage f) n))
  let B := HomologicalComplex.homologyMap (abCochainIso Y).hom n
  let M := HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map g) n
  have h2' : M ≫ C' = C ≫ F.map (HomologicalComplex.homologyMap g n) := h2
  exact (Category.assoc _ _ (C' ≫ D')).symm.trans ((congrArg (· ≫ (C' ≫ D')) h1).trans
    ((Category.assoc B M (C' ≫ D')).trans (congrArg (B ≫ ·)
      ((Category.assoc M C' D').symm.trans ((congrArg (· ≫ D') h2').trans
        ((Category.assoc C _ D').trans (congrArg (C ≫ ·) h3))))) |>.trans
    ((Category.assoc B (C ≫ D) E).trans (congrArg (B ≫ ·) (Category.assoc C D E))).symm))

end MMP.Topology.SingularCochain
