module

public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.AnalyticRestriction
public import MMP.AlgebraicGeometry.Analytic.JacobianLogarithm.PicardLogCoordinates

/-!
# Dimension of the preimage of the restricted `H¹(𝒪)`

Let `X` be a projective scheme over `ℂ` (in the application, a smooth projective surface),
`ι : C ⟶ X` a morphism (in the application, a smooth projective curve on `X`) and
`φ : ℂⁿ ≃ H¹(C^an, 𝒪)` a `ℂ`-linear coordinate system. Multiplication by a constant `a ∈ ℂ` on
`𝒪_{X^an}` and on `𝒪_{C^an}` makes `H¹(X^an, 𝒪)` and `H¹(C^an, 𝒪)` complex vector spaces, and the
restriction `H¹(X^an, 𝒪) → H¹(C^an, 𝒪)` is `ℂ`-linear, because the pullback of analytic
functions is a ring homomorphism sending the constant `a` to the constant `a`. By GAGA,
`H¹(X^an, 𝒪) ≅ H¹(X, 𝒪_X)` compatibly with the scalars. Hence if the restriction is injective, the
preimage `V ⊆ ℂⁿ` of its range is isomorphic to `H¹(X, 𝒪_X)` as a complex vector space, and
`dim V = h¹(X, 𝒪_X)`.

## Main definitions

* `MMP.Analytic.SurfaceHodge.IsSmulConst`: `m a` is multiplication by the constant `a` on
  `𝒪_{X^an}`.
* `MMP.Analytic.SurfaceHodge.smulConst`: multiplication by the constant `a` on `𝒪_{X^an}`.

## Main results

* `MMP.Analytic.SurfaceHodge.sheafHOnePullback_map`: the map `H¹(T, A) → H¹(T', B)` induced by
  `θ : A ⟶ f_* B` intertwines `α : A ⟶ A` and `β : B ⟶ B` when `α ≫ θ = θ ≫ f_* β`.
* `MMP.Analytic.SurfaceHodge.HolomorphicModel.theta_smulConst`: multiplication by the constant
  `a`, read as holomorphic functions, is multiplication by `a`.
* `MMP.Analytic.SurfaceHodge.analyticRestrictionH1_smulConst`: the restriction on `H¹` commutes
  with multiplication by constants.
* `MMP.Analytic.SurfaceHodge.finrank_eq_of_injective_analyticRestrictionH1`: `h¹(X, 𝒪_X) = dim V`.

## References

* [J.-P. Serre, *Géométrie algébrique et géométrie analytique*]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Topology
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff

namespace MMP.Analytic.SurfaceHodge

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf

/-- The pullback on sheaf cohomology is natural in the sheaf. -/
@[reassoc]
theorem sheafCohomology_map_comp_sheafCohomologyPullback {T T' : TopCat.{0}}
    (f : T' ⟶ T) {F G : TopCat.Sheaf AddCommGrpCat.{0} T} (φ : F ⟶ G) (n : ℤ) :
    (sheafCohomology T n).map φ ≫ sheafCohomologyPullback f G n =
      sheafCohomologyPullback f F n ≫
        (sheafCohomology T' n).map ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map φ) := by
  simp only [sheafCohomology, sheafCohomologyPullback, Functor.comp_map]
  rw [hypercohomology_map_comp_hypercohomologyPullback_assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact (HomologicalComplex.singleMapHomologicalComplex
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) (ComplexShape.up ℤ) 0).hom.naturality φ

/-- The map on `H¹` induced by `θ : A ⟶ f_* B` intertwines endomorphisms `α` of `A` and `β` of
`B` with `α ≫ θ = θ ≫ f_* β`. -/
theorem sheafHOnePullback_map {T T' : TopCat.{0}} (f : T' ⟶ T)
    {A : TopCat.Sheaf AddCommGrpCat.{0} T} {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (θ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B) (α : A ⟶ A) (β : B ⟶ B)
    (h : α ≫ θ = θ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map β)
    (x : Sheaf.H A 1) :
    sheafHOnePullback f θ (Sheaf.H.map α 1 x) = Sheaf.H.map β 1 (sheafHOnePullback f θ x) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f
  have hadj : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map α ≫ (adj.homEquiv A B).symm θ =
      (adj.homEquiv A B).symm θ ≫ β := by
    rw [← adj.homEquiv_naturality_left_symm, h, adj.homEquiv_naturality_right_symm]
  let ei := (MMP.JacobianLogarithm.extIso T).inv.app A
  let eh := (MMP.JacobianLogarithm.extIso T').hom.app B
  let PA := sheafCohomologyPullback f A ((1 : ℕ) : ℤ)
  let Hε := (sheafCohomology T' ((1 : ℕ) : ℤ)).map ((adj.homEquiv A B).symm θ)
  have h1 : ei (Sheaf.H.map α 1 x) = (sheafCohomology T ((1 : ℕ) : ℤ)).map α (ei x) :=
    MMP.JacobianLogarithm.extIso_inv_naturality T α x
  have h2 : PA ((sheafCohomology T ((1 : ℕ) : ℤ)).map α (ei x)) =
      (sheafCohomology T' ((1 : ℕ) : ℤ)).map
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map α) (PA (ei x)) :=
    ConcreteCategory.congr_hom
      (sheafCohomology_map_comp_sheafCohomologyPullback f α ((1 : ℕ) : ℤ)) (ei x)
  have h3 : ∀ z, Hε ((sheafCohomology T' ((1 : ℕ) : ℤ)).map
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map α) z) =
      (sheafCohomology T' ((1 : ℕ) : ℤ)).map β (Hε z) := fun z => by
    have := congrArg (fun g => (sheafCohomology T' ((1 : ℕ) : ℤ)).map g) hadj
    simp only [Functor.map_comp] at this
    exact ConcreteCategory.congr_hom this z
  have h4 : ∀ w, eh ((sheafCohomology T' ((1 : ℕ) : ℤ)).map β w) = Sheaf.H.map β 1 (eh w) :=
    fun w => ConcreteCategory.congr_hom ((MMP.JacobianLogarithm.extIso T').hom.naturality β) w
  change eh (Hε (PA (ei (Sheaf.H.map α 1 x)))) = Sheaf.H.map β 1 (eh (Hε (PA (ei x))))
  rw [h1, h2, h3, h4]

/-- `m a` is multiplication by the constant `a` on `𝒪_{X^an}`: on each open `W` it multiplies by
the restriction to `W` of the global constant `a`. -/
def IsSmulConst {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (m : ℂ → (analyticO sX ⟶ analyticO sX)) : Prop :=
  ∀ (a : ℂ) (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)),
    (show (structureSheaf sX).obj.obj (op W) from (m a).hom.app (op W) s) =
      (show (structureSheaf sX).obj.obj (op W) from
        (structureSheaf sX).obj.map (homOfLE (le_top : W ≤ ⊤)).op
          (show (structureSheaf sX).obj.obj (op ⊤) from
            (ringCatSheafHom sX).hom.app (op ⊤) (baseRingHom sX ⊤ a))) * s

/-- Multiplication by the constant `a` on `𝒪_{X^an}`, read as holomorphic functions in a model, is
multiplication by `a`. -/
theorem HolomorphicModel.theta_smulConst {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (M : HolomorphicModel sX) (m : ℂ → (analyticO sX ⟶ analyticO sX)) (hm : IsSmulConst sX m)
    (a : ℂ) (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (y : W) :
    (letI := M.cs; M.Θ.hom.hom.app (op W) ((m a).hom.app (op W) s) y) =
      a * (letI := M.cs; M.Θ.hom.hom.app (op W) s y) := by
  letI := M.cs
  refine (congrArg (fun t => M.Θ.hom.hom.app (op W) t y) (hm a W s)).trans ?_
  simp only [map_mul]
  exact congrArg (· * _) (MMP.JacobianLogarithm.Fam.theta_constSection M.Θ M.hΘ W a y)

/-- The pullback of analytic functions commutes with multiplication by constants. -/
theorem smulConst_comp_analyticPullbackOfModel {X C : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sC : C ⟶ Spec (.of ℂ)} (MX : HolomorphicModel sX) (MC : HolomorphicModel sC) (i : C ⟶ X)
    (hi : i ≫ sX = sC) (mX : ℂ → (analyticO sX ⟶ analyticO sX)) (hmX : IsSmulConst sX mX)
    (mC : ℂ → (analyticO sC ⟶ analyticO sC)) (hmC : IsSmulConst sC mC) (a : ℂ) :
    mX a ≫ analyticPullbackOfModel MX MC i hi =
      analyticPullbackOfModel MX MC i hi ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap i hi)).map (mC a) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  ext s
  refine MC.ext fun y => ?_
  letI := MX.cs
  letI := MC.cs
  have hf := contMDiff_realize i hi MX.atlas_coords MC.Θ MC.hΘ
  have h1 := analyticPullback_apply i hi hf MX.Θ MC.Θ W.unop ((mX a).hom.app W s) y
  have h2 := analyticPullback_apply i hi hf MX.Θ MC.Θ W.unop s y
  have h3 := MX.theta_smulConst mX hmX a W.unop s ⟨realize i hi y.1, y.2⟩
  have h4 := MC.theta_smulConst mC hmC a ((Opens.map (analyticMap i hi)).obj W.unop)
    ((analyticPullback i hi hf MX.Θ MC.Θ).hom.app (op W.unop) s) y
  exact h1.trans (h3.trans ((congrArg (a * ·) h2.symm).trans h4.symm))

/-- **The restriction on `H¹(𝒪)` is `ℂ`-linear**: it intertwines multiplication by a constant on
`𝒪_{X^an}` and on `𝒪_{C^an}`. -/
theorem analyticRestrictionH1_smulConst {X C : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sC : C ⟶ Spec (.of ℂ)} (i : C ⟶ X) (hi : i ≫ sX = sC)
    (mX : ℂ → (analyticO sX ⟶ analyticO sX)) (hmX : IsSmulConst sX mX)
    (mC : ℂ → (analyticO sC ⟶ analyticO sC)) (hmC : IsSmulConst sC mC) (a : ℂ)
    (x : Sheaf.H (analyticO sX) 1) :
    analyticRestrictionH1 i hi (Sheaf.H.map (mX a) 1 x) =
      Sheaf.H.map (mC a) 1 (analyticRestrictionH1 i hi x) := by
  by_cases h : Nonempty (HolomorphicModel sX) ∧ Nonempty (HolomorphicModel sC)
  · rw [analyticRestrictionH1, dif_pos h]
    exact sheafHOnePullback_map (analyticMap i hi) (analyticPullbackOfModel h.1.some h.2.some i hi)
      (mX a) (mC a)
      (smulConst_comp_analyticPullbackOfModel h.1.some h.2.some i hi mX hmX mC hmC a) x
  · simp [analyticRestrictionH1, dif_neg h]

/-- Multiplication by the constant `a` on `𝒪_{X^an}`. -/
noncomputable def smulConst {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (a : ℂ) :
    analyticO sX ⟶ analyticO sX :=
  MMP.JacobianLogarithm.smulTop (SheafOfModules.unit (ringCatSheaf sX))
    ((ringCatSheafHom sX).hom.app (op ⊤) (baseRingHom sX ⊤ a))

/-- `smulConst sX` is multiplication by constants on `𝒪_{X^an}`. -/
theorem isSmulConst_smulConst {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    IsSmulConst sX (smulConst sX) := fun _ _ _ => rfl

/-- **`h¹(X, 𝒪_X) = dim V`.** Let `X` be projective over `ℂ`, `ι : C ⟶ X` with injective analytic
restriction `H¹(X^an, 𝒪) → H¹(C^an, 𝒪)`, and `φ : ℂⁿ ≃ H¹(C^an, 𝒪)` linear for the scalars `m`
(multiplication by constants on `𝒪_{C^an}`). Then the preimage `V` under `φ` of the range of the
restriction has dimension `h¹(X, 𝒪_X)`. -/
theorem finrank_eq_of_injective_analyticRestrictionH1 {X C : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) (ι : C ⟶ X)
    (hinj : Function.Injective (analyticRestrictionH1 (sX := sX) ι rfl))
    (m : ℂ → (analyticO (ι ≫ sX) ⟶ analyticO (ι ≫ sX))) (hm : IsSmulConst (ι ≫ sX) m)
    {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H (analyticO (ι ≫ sX)) 1)
    (hφ : ∀ (a : ℂ) (v : Fin n → ℂ), φ (a • v) = Sheaf.H.map (m a) 1 (φ v))
    (V : Submodule ℂ (Fin n → ℂ))
    (hV : (V : Set (Fin n → ℂ)) = φ ⁻¹' Set.range (analyticRestrictionH1 (sX := sX) ι rfl)) :
    Module.finrank ℂ (cohomologyOverField ℂ sX (SheafOfModules.unit X.ringCatSheaf) 1) =
      Module.finrank ℂ V := by
  set mX := smulConst sX
  have hmX : IsSmulConst sX mX := isSmulConst_smulConst sX
  obtain ⟨hmadd, hmmul, hmone⟩ := MMP.JacobianLogarithm.smulConst_add_mul_one sX mX hmX
  have hmzero (x : Sheaf.H (analyticO sX) 1) : Sheaf.H.map (mX 0) 1 x = 0 := by
    have h := Sheaf.H.map_add_apply (mX 0) (mX 0) x
    rw [← hmadd, add_zero] at h
    exact left_eq_add.mp h
  letI hmod : Module ℂ (Sheaf.H (analyticO sX) 1) :=
    { smul := fun a x => Sheaf.H.map (mX a) 1 x
      one_smul := fun x => by
        change Sheaf.H.map (mX 1) 1 x = x
        rw [hmone, Sheaf.H.map_id_apply]
      mul_smul := fun a b x => by
        change Sheaf.H.map (mX (a * b)) 1 x = Sheaf.H.map (mX a) 1 (Sheaf.H.map (mX b) 1 x)
        rw [hmmul, Sheaf.H.map_comp_apply]
      smul_zero := fun a => map_zero (Sheaf.H.map (mX a) 1)
      smul_add := fun a x y => map_add (Sheaf.H.map (mX a) 1) x y
      add_smul := fun a b x => by
        change Sheaf.H.map (mX (a + b)) 1 x = Sheaf.H.map (mX a) 1 x + Sheaf.H.map (mX b) 1 x
        rw [hmadd, Sheaf.H.map_add_apply]
      zero_smul := hmzero }
  obtain ⟨E, hE⟩ := MMP.JacobianLogarithm.exists_addEquiv_H1 sX hX mX hmX
  let L : Sheaf.H (analyticO sX) 1 ≃ₗ[ℂ]
      cohomologyOverField ℂ sX (SheafOfModules.unit X.ringCatSheaf) 1 :=
    { E with map_smul' := fun a x => hE a x }
  let res := analyticRestrictionH1 (sX := sX) ι rfl
  let ψ : Sheaf.H (analyticO sX) 1 →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x => φ.symm (res x)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        change φ.symm (res (Sheaf.H.map (mX a) 1 x)) = a • φ.symm (res x)
        rw [analyticRestrictionH1_smulConst ι rfl mX hmX m hm a x]
        apply φ.injective
        rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] }
  have hrange : LinearMap.range ψ = V := by
    ext v
    rw [← SetLike.mem_coe (p := V), hV, LinearMap.mem_range, Set.mem_preimage, Set.mem_range]
    exact exists_congr fun x => φ.symm_apply_eq
  rw [← L.finrank_eq,
    ← LinearMap.finrank_range_of_inj (f := ψ) fun x y hxy => hinj (φ.symm.injective hxy), hrange]

end MMP.Analytic.SurfaceHodge
