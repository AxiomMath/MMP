module

public import MMP.AlgebraicGeometry.Vanishing.LogDeligneIllusie
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.CharZero
public import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveParts.Cohomology
public import MMP.AlgebraicGeometry.Analytic.GAGA.Differentials
public import MMP.AlgebraicTopology.ConstantSheafSingularCohomology
public import MMP.AlgebraicGeometry.Analytic.RationalSingularComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialCech

/-!
# Algebraic de Rham cohomology of a smooth projective complex variety is singular cohomology

Let `X` be a smooth projective variety over `ℂ` and `X^an` its complex realization. For every
`n` we construct a `ℂ`-linear isomorphism `H^n_dR(X/ℂ) ≃ H^n(X^an, ℂ)` between algebraic de Rham
cohomology and singular cohomology, natural for morphisms of smooth projective varieties over
`ℂ`, and deduce that `b₁(X) = h⁰(X, Ω¹_X) + h¹(X, 𝒪_X)` and that every global algebraic one-form
is closed.

The comparison is the composite
`H^n_dR(X) ≅ ℍ^n(X, Ω^•_X) ⟶ ℍ^n(X^an, α⁻¹Ω^•_X) ⟶ ℍ^n(X^an, Ω^•_{X^an}) ≅ H^n(X^an, ℂ)`,
followed by the comparison of sheaf and singular cohomology of the constant sheaf on a locally
contractible metrizable space. Derived hypercohomology is computed by Godement resolutions; the
analytification map is an isomorphism by the termwise coherent GAGA comparison filtered by form
degree; the holomorphic Poincaré lemma identifies the constant sheaf with the holomorphic de Rham
complex.

Naturality is proved by pulling holomorphic forms back along the realization `g^an` of a morphism
`g`. A holomorphic form is recorded by its values in the GAGA charts; the pull-back is the form
whose value at `x` is the value at `g^an x` composed with the derivative of `g^an` in charts, and
it is holomorphic because the chart coordinates of `g^an` are algebraic functions. It commutes
with the holomorphic exterior derivative by the chain rule for pull-backs of forms, with the
inclusion of the constants, and with the analytification of algebraic forms; the last is reduced,
by additivity, linearity over regular functions and compatibility with `d`, to the unit form.

## Main results

* `MMP.Analytic.exists_deRhamCohomology_linearEquiv_singularCohomology`: the natural `ℂ`-linear
  isomorphisms `H^n_{dR}(X/ℂ) ≃ H^n(X^an; ℂ)`, the formula for `b₁(X)`, and the closedness of global one-forms.
* `MMP.DeRhamBetti.Assemble.exists_natural_comparison`: the natural comparison isomorphisms.
* `MMP.DeRhamBetti.NatCmp.Φ_natural`: the comparison commutes with the pull-back along a morphism
  over `ℂ`.
* `MMP.DeRhamBetti.AnPull.θS`, `MMP.DeRhamBetti.AnPull.θS_δan`: the pull-back of holomorphic forms
  and its compatibility with the holomorphic exterior derivative.

## Implementation notes

* Holomorphic forms are the analytifications `Ωan` of the algebraic forms; they are handled
  through their values `AnPull.val` in the chart at each point, which determine a section and glue
  (`AnPull.val_injective`, `AnPull.exists_of_val`). The pull-back on Godement hypercohomology
  along a map of complexes `K ⟶ f_* L` is the map `GodPull.secDC` of section double complexes,
  which composes and transports along equal continuous maps.
* `H^n_{dR}(X/ℂ)` is the Stacks project's relative de Rham cohomology of `X ⟶ Spec ℂ` with its
  `H⁰(Spec ℂ, 𝒪)`-module structure (`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyBaseModule`),
  read over `ℂ` along `Scheme.ΓSpecIso`. Its pullback along a morphism is defined on the
  abelian-sheaf realization `AlgebraicGeometry.Scheme.Hom.deRhamCohomology`, so naturality is
  stated through the identification of the two realizations,
  `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology`.
* `H^n(X^an; ℂ)` is `MMP.cohomologyWithSupports` of the space of complex points
  `MMP.Analytic.ComplexPoints.analyticSpace` with full support, and the pullback along a morphism
  `g` over `ℂ` is singular pullback along its realization `MMP.Analytic.ComplexPoints.analyticMap`.
* `h^q(X, F)` is `Module.finrank ℂ` of `cohomologyOverField ℂ sX F q`.

## References

* [A. Grothendieck, *On the de Rham cohomology of algebraic varieties*]
* [J.-P. Serre, *Géométrie algébrique et géométrie analytique*]
* [R. Godement, *Topologie algébrique et théorie des faisceaux*]
* [P. Deligne, *Théorème de Lefschetz et critères de dégénérescence de suites spectrales*]
-/

open CategoryTheory AlgebraicGeometry Opposite MMP MMP.Analytic

universe u

namespace MMP.DeRhamBetti

/-! ### Godement hypercohomology computes derived hypercohomology -/

section GodementBridge

open Limits TopologicalSpace HomologicalComplex

variable (T : TopCat.{u})

/-- The Godement augmentation `F[0] ⟶ G^•(F)` is a quasi-isomorphism. -/
lemma quasiIso_godementAugmentation (F : (TopCat.Sheaf AddCommGrpCat.{u} T)) : QuasiIso (godementAugmentation T F) :=
  ((sheafCohomology_toolkit.{u, 0, 0, 0, 0} T).2.1.2.2.2 F).1

/-- In degree `0`, the Godement augmentation is the unit `F ⟶ G^0(F)`. -/
lemma godementAugmentation_f_zero (F : (TopCat.Sheaf AddCommGrpCat.{u} T)) :
    (godementAugmentation T F).f 0 =
      (singleObjXSelf _ 0 F).hom ≫ (godementUnit T).app F :=
  CokernelCoresolution.augmentation_f_zero F

/-- `A ≫ s⁻¹ ≫ (s ≫ u) ≫ g = A ≫ u ≫ g` for an isomorphism `s`. -/
lemma aux_inv_hom' {C : Type*} [Category C] {X Y Z W V : C} (A : X ⟶ Y) (s : Z ≅ Y)
    (u : Y ⟶ W) (g : W ⟶ V) : A ≫ s.inv ≫ (s.hom ≫ u) ≫ g = A ≫ u ≫ g := by
  simp

/-- A square `φ ≫ η' = η ≫ g` stays commutative after conjugating its ends by isomorphisms. -/
lemma aux_nat {C : Type*} [Category C] {X Y Y' Z Z' W W' V : C} (A : X ⟶ Y) (η : Y ⟶ Z)
    (e : W ≅ Z) (g : Z ⟶ Z') (e' : W' ≅ Z') (φ : Y ⟶ Y') (B : V ≅ Y') (η' : Y' ⟶ Z')
    (h : φ ≫ η' = η ≫ g) :
    (A ≫ η ≫ e.inv) ≫ e.hom ≫ g ≫ e'.inv = (A ≫ φ ≫ B.inv) ≫ B.hom ≫ η' ≫ e'.inv := by
  simp [reassoc_of% h]

/-- The embedding `ℕ ↪ ℤ` of complex shapes sends `0` to `0`. -/
lemma embeddingUpNat_f_zero : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl

/-- The Godement double complex `(q, p) ↦ G^p(K^q)`, the Godement degree extended by zero. -/
noncomputable abbrev godDC (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) : HomologicalComplex₂ (TopCat.Sheaf AddCommGrpCat.{u} T) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) :=
  ((godementResolution T ⋙ ComplexShape.embeddingUpNat.extendFunctor (TopCat.Sheaf AddCommGrpCat.{u} T)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)

/-- The augmentation `F[0] ⟶ G^•(F)`, extended to `ℤ`-indexed complexes. -/
noncomputable def colAugS (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (single (TopCat.Sheaf AddCommGrpCat.{u} T) (ComplexShape.up ℤ) 0).obj F ⟶
    ((godementResolution T).obj F).extend ComplexShape.embeddingUpNat :=
  (extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
    extendMap (godementAugmentation T F) ComplexShape.embeddingUpNat

/-- The augmentation `colAugS T F : F[0] ⟶ G^•(F)` is a quasi-isomorphism. -/
theorem quasiIso_colAugS (F : TopCat.Sheaf AddCommGrpCat.{u} T) : QuasiIso (colAugS T F) := by
  have := quasiIso_godementAugmentation T F
  have hext : QuasiIso (extendMap (godementAugmentation T F) ComplexShape.embeddingUpNat) :=
    (quasiIso_extendMap_iff (godementAugmentation T F) ComplexShape.embeddingUpNat).2 this
  dsimp only [colAugS]
  infer_instance

attribute [local instance] quasiIso_colAugS

/-- In degree `0`, `colAugS T F` is the Godement unit `F ⟶ G^0(F)`. -/
lemma colAugS_f_zero (F : TopCat.Sheaf AddCommGrpCat.{u} T) : (colAugS T F).f 0 =
    (singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (godementUnit T).app F ≫
      (((godementResolution T).obj F).extendXIso ComplexShape.embeddingUpNat
        embeddingUpNat_f_zero).inv := by
  have h0 := embeddingUpNat_f_zero
  have e1 := extendSingleIso_inv_f ComplexShape.embeddingUpNat F 0 0 h0
  have e2 := extendMap_f (godementAugmentation T F) ComplexShape.embeddingUpNat h0
  have e3 := godementAugmentation_f_zero T F
  change (extendSingleIso ComplexShape.embeddingUpNat F 0 0 h0).inv.f 0 ≫
    (extendMap (godementAugmentation T F) ComplexShape.embeddingUpNat).f 0 = _
  rw [e1, e2, e3]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact aux_inv_hom' _ _ _ _

/-- The augmentation `colAugS T F : F[0] ⟶ G^•(F)` is natural in the sheaf `F`. -/
lemma colAugS_naturality {F F' : TopCat.Sheaf AddCommGrpCat.{u} T} (φ : F ⟶ F') :
    colAugS T F ≫ extendMap ((godementResolution T).map φ) ComplexShape.embeddingUpNat =
      (single (TopCat.Sheaf AddCommGrpCat.{u} T) (ComplexShape.up ℤ) 0).map φ ≫ colAugS T F' := by
  apply HomologicalComplex.from_single_hom_ext
  rw [comp_f, comp_f, colAugS_f_zero, colAugS_f_zero, single_map_f_self]
  erw [extendMap_f _ _ embeddingUpNat_f_zero]
  have h := (godementUnit T).naturality φ
  simp only [Functor.id_map] at h
  exact aux_nat _ _ _ _ _ _ _ _ h

/-- The column augmentation `K^p[0] ⟶ G^•(K^p)`. -/
noncomputable abbrev colAug (p : ℤ) := colAugS T (K.X p)

/-- The column augmentations `K^p[0] ⟶ G^•(K^p)` are natural in maps `K^p ⟶ K^{p'}`. -/
lemma colAug_naturality {p p' : ℤ} (φ : K.X p ⟶ K.X p') :
    colAug T K p ≫ extendMap ((godementResolution T).map φ) ComplexShape.embeddingUpNat =
      (single (TopCat.Sheaf AddCommGrpCat.{u} T) (ComplexShape.up ℤ) 0).map φ ≫ colAug T K p' :=
  colAugS_naturality T φ

/-- The row augmentation `K ⟶ rowZero (godDC K)`. -/
noncomputable def rowAug : K ⟶ rowZero (godDC T K) where
  f p := (singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).inv ≫ (colAug T K p).f 0
  comm' p p' _ := by
    have h := congrArg (fun φ => φ.f 0) (colAug_naturality T K (K.d p p'))
    simp only [comp_f, single_map_f_self] at h
    change (singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).inv ≫ (colAug T K p).f 0 ≫
        (extendMap ((godementResolution T).map (K.d p p')) ComplexShape.embeddingUpNat).f 0 =
      K.d p p' ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p')).inv ≫ (colAug T K p').f 0
    rw [h]
    simp

/-- The component of `rowAug T K` in degree `p` is the degree `0` component of `colAug T K p`. -/
lemma rowAug_f (p : ℤ) : (singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).hom ≫ (rowAug T K).f p =
    (colAug T K p).f 0 :=
  Iso.hom_inv_id_assoc _ _

/-- The Godement double complex vanishes in Godement degree `q < 0`. -/
lemma isZero_godDC_X_X_neg (p q : ℤ) (hq : q < 0) : IsZero (((godDC T K).X p).X q) :=
  ((godementResolution T).obj (K.X p)).isZero_extend_X ComplexShape.embeddingUpNat q
    (by intro n hn; change ((n : ℕ) : ℤ) = q at hn; omega)

/-- The column `p` of the Godement double complex vanishes when `K^p` is zero. -/
lemma isZero_godDC_X (p : ℤ) (hp : IsZero (K.X p)) : IsZero ((godDC T K).X p) :=
  (godementResolution T ⋙ ComplexShape.embeddingUpNat.extendFunctor (TopCat.Sheaf AddCommGrpCat.{u} T)).map_isZero hp

/-- For `K` strictly concentrated in degrees `≥ a`, the row augmentation `K ⟶ rowZero (godDC K)`
satisfies the `Hypotheses` of the total complex comparison. -/
lemma hypotheses_rowAug (a : ℤ) [K.IsStrictlyGE a] : Hypotheses K (godDC T K) (rowAug T K) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    refine (Set.finite_Icc a n).subset fun p hp => ⟨?_, ?_⟩
    · by_contra h
      exact hp ((HomologicalComplex.eval _ _ (n - p)).map_isZero
        (isZero_godDC_X T K p (K.isZero_of_isStrictlyGE a p (by omega))))
    · by_contra h
      exact hp (isZero_godDC_X_X_neg T K p (n - p) (by omega))
  · exact isZero_godDC_X_X_neg T K
  · intro p q hq
    exact (exactAt_and_isIso_kernelLift_of_quasiIso_single (K.X p)
      ((godDC T K).X p) (colAug T K p) (quasiIso_colAugS T (K.X p))
      (isZero_godDC_X_X_neg T K p (-1) (by omega))).1 q hq
  · intro p
    obtain ⟨hβ, hiso⟩ := (exactAt_and_isIso_kernelLift_of_quasiIso_single (K.X p)
      ((godDC T K).X p) (colAug T K p) (quasiIso_colAugS T (K.X p))
      (isZero_godDC_X_X_neg T K p (-1) (by omega))).2
    set u := singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p) with hu
    have hβ' : (rowAug T K).f p ≫ ((godDC T K).X p).d 0 1 = 0 := by
      apply (cancel_epi u.hom).1
      rw [← Category.assoc, rowAug_f, hβ, comp_zero]
    refine ⟨hβ', ?_⟩
    have heq : u.hom ≫ kernel.lift (((godDC T K).X p).d 0 1) ((rowAug T K).f p) hβ' =
        kernel.lift (((godDC T K).X p).d 0 1) ((colAug T K p).f 0) hβ := by
      apply (cancel_mono (kernel.ι (((godDC T K).X p).d 0 1))).mp
      simp only [Category.assoc, kernel.lift_ι]
      exact (rowAug_f T K p).trans (kernel.lift_ι _ _ _).symm
    have hcomp : IsIso (u.hom ≫ kernel.lift
        (((godDC T K).X p).d 0 1) ((rowAug T K).f p) hβ') := by
      rw [heq]
      exact hiso
    exact IsIso.of_isIso_comp_left u.hom _

/-- Each term `G^q(F)` of the Godement resolution is flasque. -/
lemma isFlasque_godementResolution_X (F : TopCat.Sheaf AddCommGrpCat.{u} T) (q : ℕ) :
    TopCat.Sheaf.IsFlasque (((godementResolution T).obj F).X q) :=
  ((sheafCohomology_toolkit.{u, 0, 0, 0, 0} T).2.1.2.2.2 F).2 q

/-- A coproduct of flasque sheaves, with finitely many nonzero terms, is flasque. -/
lemma isFlasque_cofan_pt {J : Type*} (A : J → TopCat.Sheaf AddCommGrpCat.{u} T) (c : Cofan A)
    (hc : IsColimit c) (S : Set J) [Finite S] (hS : ∀ j, j ∉ S → IsZero (A j))
    (hA : ∀ j ∈ S, (A j).IsFlasque) : c.pt.IsFlasque := by
  have : HasFiniteBiproducts (TopCat.Sheaf AddCommGrpCat.{u} T) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let hcS := StacksDraft.TotalComplexQuasiIso.isColimitRestrictCofan c hc S hS
  let B := ⨁ fun j : S => A (j : J)
  let e : c.pt ≅ B := hcS.coconePointUniqueUpToIso (biproduct.isColimit _)
  have hB : B.IsFlasque := TopCat.Sheaf.isFlasque_biproduct (Y := T) (I := ↥S)
      (fun j : S => A (j : J)) (fun j => hA j.1 j.2)
  exact TopCat.Sheaf.IsFlasque.of_iso e hB

section Tot

/-- For `K` strictly concentrated in degrees `≥ a`, so is the total complex of `godDC T K`. -/
lemma isStrictlyGE_total_godDC (a : ℤ) [K.IsStrictlyGE a] [(godDC T K).HasTotal (ComplexShape.up ℤ)] :
    CochainComplex.IsStrictlyGE ((godDC T K).total (ComplexShape.up ℤ)) a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact StacksDraft.TotalComplexQuasiIso.isZero_total_X (godDC T K) a
    (isZero_godDC_X_X_neg T K) (fun p hp => isZero_godDC_X T K p
      (K.isZero_of_isStrictlyGE a p hp)) n hn

/-- For a bounded below complex `K`, every term of the total complex of `godDC T K` is flasque. -/
lemma isFlasque_total_godDC (a : ℤ) [K.IsStrictlyGE a] [(godDC T K).HasTotal (ComplexShape.up ℤ)]
    (n : ℤ) : TopCat.Sheaf.IsFlasque (((godDC T K).total (ComplexShape.up ℤ)).X n) := by
  classical
  let Z := (godDC T K).toGradedObject
  let c := Z.cofanMapObj (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)) n
  let hc := Z.isColimitCofanMapObj
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n
  let J := ↑((ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⁻¹' {n})
  let S : Set J := {i | ¬ IsZero (Z i.1)}
  let f : J → ℤ := fun i => i.1.1
  have hinj : Function.Injective f := by
    rintro ⟨⟨p, q⟩, hpq⟩ ⟨⟨p', q'⟩, hpq'⟩ (h : p = p')
    have e1 : p + q = n := hpq
    have e2 : p' + q' = n := hpq'
    subst h
    have : q = q' := by omega
    subst this
    rfl
  have hfin : S.Finite := by
    refine ((Set.finite_Icc a n).preimage hinj.injOn).subset ?_
    rintro ⟨⟨p, q⟩, hpq⟩ hj
    have e1 : p + q = n := hpq
    have hq : 0 ≤ q := by
      by_contra h
      exact hj (isZero_godDC_X_X_neg T K p q (by omega))
    have hp : a ≤ p := by
      by_contra h
      exact hj ((HomologicalComplex.eval _ _ q).map_isZero
        (isZero_godDC_X T K p (K.isZero_of_isStrictlyGE a p (by omega))))
    exact ⟨hp, by change p ≤ n; omega⟩
  have : Finite S := hfin.to_subtype
  refine isFlasque_cofan_pt T _ c hc S (fun j hj => by by_contra h; exact hj h) ?_
  rintro ⟨⟨p, q⟩, hpq⟩ hj
  have hq : 0 ≤ q := by
    by_contra h
    exact hj (isZero_godDC_X_X_neg T K p q (by omega))
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℤ) = q := ⟨q.toNat, Int.toNat_of_nonneg hq⟩
  have := isFlasque_godementResolution_X T (K.X p) k
  exact TopCat.Sheaf.IsFlasque.of_iso
    (((godementResolution T).obj (K.X p)).extendXIso ComplexShape.embeddingUpNat
      (i := k) rfl) this

end Tot

attribute [local instance] globalSections_additive

/-- The Godement double complex, as a functor of the complex. -/
noncomputable abbrev godDCFunctor : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ ⥤
    HomologicalComplex₂ (TopCat.Sheaf AddCommGrpCat.{u} T) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (godementResolution T ⋙ ComplexShape.embeddingUpNat.extendFunctor
    (TopCat.Sheaf AddCommGrpCat.{u} T)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The row augmentation `K ⟶ rowZero (godDC K)` is natural in the complex `K`. -/
lemma rowAug_naturality {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ} (φ : K ⟶ K') :
    rowAug T K ≫ rowZeroMap ((godDCFunctor T).map φ) = φ ≫ rowAug T K' := by
  ext p
  have h := congrArg (fun ψ => ψ.f 0) (colAugS_naturality T (φ.f p))
  simp only [comp_f, single_map_f_self] at h
  change (singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).inv ≫ (colAugS T (K.X p)).f 0 ≫
      (extendMap ((godementResolution T).map (φ.f p)) ComplexShape.embeddingUpNat).f 0 =
    φ.f p ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (K'.X p)).inv ≫ (colAugS T (K'.X p)).f 0
  rw [h]
  simp

/-- The Godement total complex, as a functor on complexes. -/
noncomputable abbrev godTot : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ ⥤
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ :=
  godDCFunctor T ⋙ HomologicalComplex₂.totalFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (c₁₂ := ComplexShape.up ℤ)

/-- For a bounded below complex `L`, the row augmentation satisfies the `Hypotheses` of the total
complex comparison. -/
lemma hypotheses_rowAug_plus (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) :
    Hypotheses L.obj (godDC T L.obj) (rowAug T L.obj) := by
  obtain ⟨a, ha⟩ := L.2
  exact hypotheses_rowAug T L.obj a

/-- The Godement total complex, on bounded below complexes. -/
noncomputable def godTotPlus : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T) ⥤
    CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T) where
  obj L := ⟨(godDC T L.obj).total (ComplexShape.up ℤ), by
    obtain ⟨a, ha⟩ := L.2
    exact ⟨a, isStrictlyGE_total_godDC T L.obj a⟩⟩
  map φ := ObjectProperty.homMk
    (HomologicalComplex₂.total.map ((godDCFunctor T).map φ.hom) (ComplexShape.up ℤ))
  map_id L := by
    ext : 1
    change HomologicalComplex₂.total.map ((godDCFunctor T).map (𝟙 L.obj)) _ = 𝟙 _
    rw [CategoryTheory.Functor.map_id, HomologicalComplex₂.total.map_id]
  map_comp φ ψ := by
    ext : 1
    change HomologicalComplex₂.total.map ((godDCFunctor T).map (φ.hom ≫ ψ.hom)) _ = _
    rw [CategoryTheory.Functor.map_comp, HomologicalComplex₂.total.map_comp]
    rfl

/-- The comparison `L ⟶ Tot G(L)`, a natural quasi-isomorphism. -/
noncomputable def compNat : CochainComplex.Plus.ι (TopCat.Sheaf AddCommGrpCat.{u} T) ⟶
    CochainComplex.Plus.ι _ ⋙ godTot T where
  app L := comparisonMapP L.obj (godDC T L.obj) (rowAug T L.obj) (hypotheses_rowAug_plus T L)
  naturality L L' φ :=
    (comparisonMapP_naturality L.obj (godDC T L.obj) (rowAug T L.obj) (hypotheses_rowAug_plus T L)
      (hypotheses_rowAug_plus T L') φ.hom ((godDCFunctor T).map φ.hom)
      (rowAug_naturality T φ.hom)).symm

/-- The comparison `L ⟶ Tot G(L)` is a quasi-isomorphism for bounded below `L`. -/
theorem quasiIso_compNat_app (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) :
    QuasiIso ((compNat T).app L) :=
  quasiIso_comparisonMapP L.obj (godDC T L.obj) (rowAug T L.obj) (hypotheses_rowAug_plus T L)

attribute [local instance] quasiIso_compNat_app

/-- The comparison on bounded below complexes. -/
noncomputable def compNatPlus : 𝟭 (CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) ⟶
    godTotPlus T where
  app L := ObjectProperty.homMk ((compNat T).app L)
  naturality L L' φ := by
    ext : 1
    exact (compNat T).naturality φ

/-- The Godement sections double complex, as the sections of the Godement double complex. -/
noncomputable def secIso (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) :
    HomologicalComplex₂.mapBicomplex (globalSections T) (godDC T K) ≅
      godementSectionsDoubleComplex T K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (HomologicalComplex.mapHomologicalComplexExtendIso (globalSections T)
      ((godementResolution T).obj (K.X p)) ComplexShape.embeddingUpNat).symm)
    (fun p p' _ => (HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality
      (globalSections T) _ ((godementResolution T).map (K.d p p')) ComplexShape.embeddingUpNat).symm)

/-- The isomorphism `secIso T K` is natural in the complex `K`. -/
lemma secIso_naturality {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ} (φ : K ⟶ K') :
    (((globalSections T).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((godDCFunctor T).map φ) ≫ (secIso T K').hom =
      (secIso T K).hom ≫ ((godementSections T).mapHomologicalComplex _).map φ := by
  ext p : 1
  exact HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality
      (globalSections T) _ ((godementResolution T).map (φ.f p)) ComplexShape.embeddingUpNat

/-- For bounded below `L`, only finitely many terms of `godDC T L` on the antidiagonal
`p + q = n` are nonzero. -/
lemma finite_antidiagonal_godDC (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) (n : ℤ) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq = n ∧
      ¬ IsZero (((godDC T L.obj).X pq.1).X pq.2)}.Finite := by
  refine ((hypotheses_rowAug_plus T L).diagonalFinite n).image (fun p => (p, n - p)) |>.subset ?_
  rintro ⟨p, q⟩ ⟨hpq, hnz⟩
  have hpq' : p + q = n := hpq
  refine ⟨p, ?_, ?_⟩
  · change ¬ IsZero (((godDC T L.obj).X p).X (n - p))
    rwa [show n - p = q by omega]
  · change (p, n - p) = (p, q)
    exact Prod.ext rfl (by omega)

/-- `Γ(T, Tot G(L)) ≅ Tot Γ(T, G(L))` for a bounded below complex `L`. -/
noncomputable def gammaTotIso (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) :
    ((globalSections T).mapHomologicalComplex _).obj ((godDC T L.obj).total (ComplexShape.up ℤ)) ≅
      (godementSectionsDoubleComplex T L.obj).total (ComplexShape.up ℤ) :=
  (HomologicalComplex₂.TotalMap.totalIsoOfFinite (globalSections T) (godDC T L.obj)
      (finite_antidiagonal_godDC T L)).symm ≪≫
    HomologicalComplex₂.total.mapIso (secIso T L.obj) _

/-- `gammaTotIso T L` is the inverse of `totalIsoOfFinite` followed by the total map of
`secIso T L.obj`. -/
lemma gammaTotIso_hom_eq (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) :
    (gammaTotIso T L).hom =
      (HomologicalComplex₂.TotalMap.totalIsoOfFinite (globalSections T) (godDC T L.obj)
        (finite_antidiagonal_godDC T L)).inv ≫
      (HomologicalComplex₂.total.mapIso (secIso T L.obj) (ComplexShape.up ℤ)).hom :=
  rfl

/-- The isomorphism `Γ(T, Tot G(L)) ≅ Tot Γ(T, G(L))` is natural in `L`. -/
lemma gammaTotIso_naturality {L L' : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)}
    (φ : L ⟶ L') :
    ((globalSections T).mapHomologicalComplex _).map
        (HomologicalComplex₂.total.map ((godDCFunctor T).map φ.hom) (ComplexShape.up ℤ)) ≫
        (gammaTotIso T L').hom =
      (gammaTotIso T L).hom ≫ HomologicalComplex₂.total.map
        (((godementSections T).mapHomologicalComplex _).map φ.hom) (ComplexShape.up ℤ) := by
  set e := HomologicalComplex₂.TotalMap.totalIsoOfFinite (globalSections T) (godDC T L.obj)
    (finite_antidiagonal_godDC T L)
  set e' := HomologicalComplex₂.TotalMap.totalIsoOfFinite (globalSections T) (godDC T L'.obj)
    (finite_antidiagonal_godDC T L')
  have h1 := HomologicalComplex₂.totalMap_naturality (c₁₂ := ComplexShape.up ℤ) (globalSections T)
    (godDC T L.obj) ((godDCFunctor T).map φ.hom)
  have h2 : ((globalSections T).mapHomologicalComplex _).map
        (HomologicalComplex₂.total.map ((godDCFunctor T).map φ.hom) (ComplexShape.up ℤ)) ≫ e'.inv =
      e.inv ≫ HomologicalComplex₂.total.map
        ((((globalSections T).mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((godDCFunctor T).map φ.hom)) (ComplexShape.up ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact h1.symm
  have h3 := congrArg (fun ψ => HomologicalComplex₂.total.map ψ (ComplexShape.up ℤ))
    (secIso_naturality T φ.hom)
  simp only [HomologicalComplex₂.total.map_comp] at h3
  change ((globalSections T).mapHomologicalComplex _).map
        (HomologicalComplex₂.total.map ((godDCFunctor T).map φ.hom) (ComplexShape.up ℤ)) ≫
      (e'.inv ≫ HomologicalComplex₂.total.map (secIso T L'.obj).hom _) =
    (e.inv ≫ HomologicalComplex₂.total.map (secIso T L.obj).hom _) ≫ _
  rw [← Category.assoc, h2, Category.assoc, h3, Category.assoc]

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The category of sheaves of abelian groups on `T` has enough injectives. -/
theorem enoughInjectives_sheaf : EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} T) :=
  (sheafCohomology_toolkit.{u, 0, 0, 0, 0} T).1.1

attribute [local instance] enoughInjectives_sheaf

/-- A flasque sheaf is acyclic for the global sections functor. -/
lemma rightAcyclic_of_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hF : F.IsFlasque) :
    (globalSections T).rightAcyclic F :=
  Stacks.Cohomology.FlasqueAbelian.rightAcyclic_abSections_of_isFlasque (X := T) ⊤ F hF

/-- The comparison `L ⟶ Tot G(L)` becomes an isomorphism in the bounded below derived category. -/
theorem isIso_Q_map_compNatPlus (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) :
    IsIso (DerivedCategory.Plus.Q.map ((compNatPlus T).app L)) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ((compNatPlus T).app L))) := by
    change IsIso (DerivedCategory.Q.map ((compNat T).app L))
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

attribute [local instance] isIso_Q_map_compNatPlus

/-- `Q ≅ quotient ⋙ Qh` on bounded below complexes. -/
noncomputable def plusQIso (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] :
    DerivedCategory.Plus.Q (C := C) ≅
      HomotopyCategory.Plus.quotient C ⋙ DerivedCategory.Plus.Qh :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι C) (DerivedCategory.quotientCompQhIso C).symm ≪≫
      (Functor.isoWhiskerRight (HomotopyCategory.Plus.quotientCompιIso C).symm
        DerivedCategory.Qh) ≪≫
      Functor.isoWhiskerLeft (HomotopyCategory.Plus.quotient C)
        (DerivedCategory.Plus.QhCompιIsoιCompQh C).symm)

variable (n : ℤ)

/-- Derived hypercohomology of `L` is that of its Godement total complex. -/
noncomputable def stepA :
    DerivedCategory.Plus.Q ⋙ (globalSections T).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n ≅
      godTotPlus T ⋙ DerivedCategory.Plus.Q ⋙ (globalSections T).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n :=
  NatIso.ofComponents (fun L => ((globalSections T).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso
      (asIso (DerivedCategory.Plus.Q.map ((compNatPlus T).app L))))
    (fun {L L'} φ => by
      simp only [Functor.mapIso_hom, asIso_hom, Functor.comp_map, ← Functor.map_comp]
      exact congrArg (fun x => ((globalSections T).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
          (DerivedCategory.Plus.Q.map x)) ((compNatPlus T).naturality φ))

/-- The localisation `Q` factors through the homotopy category: `Q ≅ quotient ⋙ Qh`. -/
noncomputable def stepB :
    godTotPlus T ⋙ DerivedCategory.Plus.Q ⋙ (globalSections T).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n ≅
      godTotPlus T ⋙ HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh ⋙
        (globalSections T).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n :=
  Functor.isoWhiskerLeft (godTotPlus T) (Functor.isoWhiskerRight (plusQIso _) _)

/-- The unit of the right derived functor of global sections is an isomorphism on the Godement
total complex of a bounded below complex of sheaves. -/
theorem isIso_unit_godTot (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) :
    IsIso ((globalSections T).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient _).obj ((godTotPlus T).obj L))) := by
  refine Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun m => ?_
  obtain ⟨a, ha⟩ := L.2
  exact rightAcyclic_of_isFlasque T _ (isFlasque_total_godDC T L.obj a m)

attribute [local instance] isIso_unit_godTot

/-- The derived-functor unit, invertible on the flasque Godement total complexes. -/
noncomputable def stepC :
    godTotPlus T ⋙ HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh ⋙
        (globalSections T).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n ≅
      godTotPlus T ⋙ HomotopyCategory.Plus.quotient _ ⋙
        (globalSections T).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n :=
  haveI : ∀ X, IsIso ((Functor.whiskerLeft (godTotPlus T ⋙ HomotopyCategory.Plus.quotient _)
      (globalSections T).rightDerivedFunctorPlusUnith).app X) := fun X => isIso_unit_godTot T X
  haveI : IsIso (Functor.whiskerLeft (godTotPlus T ⋙ HomotopyCategory.Plus.quotient _)
      (globalSections T).rightDerivedFunctorPlusUnith) :=
    NatIso.isIso_of_isIso_app _
  (Functor.isoWhiskerRight (asIso (Functor.whiskerLeft
    (godTotPlus T ⋙ HomotopyCategory.Plus.quotient _)
      (globalSections T).rightDerivedFunctorPlusUnith))
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n)).symm

/-- Homology on the bounded below derived category is homology in the homotopy category. -/
noncomputable def stepD :
    godTotPlus T ⋙ HomotopyCategory.Plus.quotient _ ⋙
        (globalSections T).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n ≅
      godTotPlus T ⋙ HomotopyCategory.Plus.quotient _ ⋙
        (globalSections T).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι _ ⋙
          HomotopyCategory.homologyFunctor _ (ComplexShape.up ℤ) n :=
  Functor.isoWhiskerLeft (godTotPlus T ⋙ HomotopyCategory.Plus.quotient _ ⋙
    (globalSections T).mapHomotopyCategoryPlus) (Stacks.DerivedIndexing.plusHomologyIso n)

/-- The homotopy category of the sections. -/
noncomputable def quotMapIso :
    HomotopyCategory.Plus.quotient (TopCat.Sheaf AddCommGrpCat.{u} T) ⋙
        (globalSections T).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι _ ≅
      CochainComplex.Plus.ι _ ⋙ (globalSections T).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient _ (ComplexShape.up ℤ) :=
  Functor.isoWhiskerRight (HomotopyCategory.Plus.quotientCompιIso _)
      ((globalSections T).mapHomotopyCategory (ComplexShape.up ℤ)) ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι _)
      ((globalSections T).mapHomotopyCategoryFactors (ComplexShape.up ℤ))

/-- Homology in the homotopy category of sections is homology of the complex of sections. -/
noncomputable def stepE :
    godTotPlus T ⋙ HomotopyCategory.Plus.quotient _ ⋙
        (globalSections T).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι _ ⋙
          HomotopyCategory.homologyFunctor _ (ComplexShape.up ℤ) n ≅
      godTotPlus T ⋙ CochainComplex.Plus.ι _ ⋙
        (globalSections T).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n :=
  Functor.isoWhiskerLeft (godTotPlus T)
    (Functor.isoWhiskerRight (quotMapIso T) (HomotopyCategory.homologyFunctor _ _ n) ≪≫
      Functor.isoWhiskerLeft (CochainComplex.Plus.ι _ ⋙
        (globalSections T).mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.homologyFunctorFactors _ _ n))

/-- Sections of the Godement total complex, naturally. -/
noncomputable def gammaTotNat :
    godTotPlus T ⋙ CochainComplex.Plus.ι _ ⋙
        (globalSections T).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      CochainComplex.Plus.ι _ ⋙ (godementSections T).mapHomologicalComplex _ ⋙
        HomologicalComplex₂.totalFunctor _ _ _ (c₁₂ := ComplexShape.up ℤ) :=
  NatIso.ofComponents (fun L => gammaTotIso T L) (fun {L L'} φ => gammaTotIso_naturality T φ)

/-- Sections of the Godement total complex are the total complex of the Godement sections. -/
noncomputable def stepF :
    godTotPlus T ⋙ CochainComplex.Plus.ι _ ⋙
        (globalSections T).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n ≅
      CochainComplex.Plus.ι _ ⋙ hypercohomology T n :=
  Functor.isoWhiskerRight (gammaTotNat T) (HomologicalComplex.homologyFunctor _ _ n)

/-- **The Godement hypercohomology of a bounded below complex is its derived hypercohomology.** -/
noncomputable def bridgeIso :
    DerivedCategory.Plus.Q ⋙ (globalSections T).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n ≅
      CochainComplex.Plus.ι _ ⋙ hypercohomology T n :=
  stepA T n ≪≫ stepB T n ≪≫ stepC T n ≪≫ stepD T n ≪≫ stepE T n ≪≫ stepF T n

end Derived

end GodementBridge

attribute [local instance] enoughInjectives_sheaf quasiIso_colAugS quasiIso_compNat_app
  isIso_Q_map_compNatPlus isIso_unit_godTot

/-! ### Counting along the stupid filtration -/

section Counting

open Limits TopologicalSpace

/-! ### The stupid filtration -/

section Trunc

open ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

/-- The stupid truncation `σ^{≥ i} Y` of a cochain complex: `Y^m` in degrees `m ≥ i`, zero
below. -/
noncomputable def stupidGE (Y : CochainComplex C ℤ) (i : ℤ) : CochainComplex C ℤ where
  X m := if i ≤ m then Y.X m else 0
  d m m' := if h : i ≤ m ∧ i ≤ m' then
      eqToHom (if_pos h.1) ≫ Y.d m m' ≫ eqToHom (if_pos h.2).symm else 0
  shape m m' hmm' := by
    by_cases h : i ≤ m ∧ i ≤ m'
    · rw [dif_pos h, Y.shape _ _ hmm', zero_comp, comp_zero]
    · rw [dif_neg h]
  d_comp_d' m m' m'' _ _ := by
    by_cases h₁ : i ≤ m
    · by_cases h₂ : i ≤ m'
      · by_cases h₃ : i ≤ m''
        · rw [dif_pos ⟨h₁, h₂⟩, dif_pos ⟨h₂, h₃⟩]
          simp
        · rw [dif_neg (show ¬(i ≤ m' ∧ i ≤ m'') from fun h => h₃ h.2), comp_zero]
      · rw [dif_neg (show ¬(i ≤ m ∧ i ≤ m') from fun h => h₂ h.2), zero_comp]
    · rw [dif_neg (show ¬(i ≤ m ∧ i ≤ m') from fun h => h₁ h.1), zero_comp]

/-- In degrees `m ≥ i`, the stupid truncation `σ^{≥ i} Y` agrees with `Y`. -/
lemma stupidGE_X_of_le (Y : CochainComplex C ℤ) {i m : ℤ} (h : i ≤ m) :
    (stupidGE Y i).X m = Y.X m := if_pos h

/-- In degrees `m < i`, the stupid truncation `σ^{≥ i} Y` is zero. -/
lemma isZero_stupidGE_X_of_lt (Y : CochainComplex C ℤ) {i m : ℤ} (h : m < i) :
    IsZero ((stupidGE Y i).X m) := by
  change IsZero (if i ≤ m then Y.X m else 0)
  rw [if_neg (by omega)]
  exact isZero_zero C

/-- In degrees `m, m' ≥ i`, the differential of `σ^{≥ i} Y` is that of `Y`. -/
lemma stupidGE_d (Y : CochainComplex C ℤ) {i m m' : ℤ} (h : i ≤ m) (h' : i ≤ m') :
    (stupidGE Y i).d m m' =
      eqToHom (stupidGE_X_of_le Y h) ≫ Y.d m m' ≫ eqToHom (stupidGE_X_of_le Y h').symm :=
  dif_pos ⟨h, h'⟩

/-- The inclusion `σ^{≥ i} Y ⟶ Y`. -/
noncomputable def stupidGEι (Y : CochainComplex C ℤ) (i : ℤ) : stupidGE Y i ⟶ Y where
  f m := if h : i ≤ m then eqToHom (stupidGE_X_of_le Y h) else 0
  comm' m m' hmm' := by
    obtain rfl : m + 1 = m' := hmm'
    by_cases h₁ : i ≤ m
    · rw [dif_pos h₁, dif_pos (by omega : i ≤ m + 1), stupidGE_d Y h₁ (by omega)]
      simp
    · exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _

/-- In degrees `m ≥ i`, the inclusion `σ^{≥ i} Y ⟶ Y` is the identity. -/
lemma stupidGEι_f_of_le (Y : CochainComplex C ℤ) {i m : ℤ} (h : i ≤ m) :
    (stupidGEι Y i).f m = eqToHom (stupidGE_X_of_le Y h) := dif_pos h

/-- The inclusion `σ^{≥ i + 1} Y ⟶ σ^{≥ i} Y`. -/
noncomputable def stupidGEMap (Y : CochainComplex C ℤ) (i : ℤ) :
    stupidGE Y (i + 1) ⟶ stupidGE Y i where
  f m := if h : i + 1 ≤ m then
      eqToHom (stupidGE_X_of_le Y h) ≫ eqToHom (stupidGE_X_of_le Y (by omega : i ≤ m)).symm else 0
  comm' m m' hmm' := by
    obtain rfl : m + 1 = m' := hmm'
    by_cases h₁ : i + 1 ≤ m
    · rw [dif_pos h₁, dif_pos (by omega : i + 1 ≤ m + 1), stupidGE_d Y h₁ (by omega),
        stupidGE_d Y (by omega : i ≤ m) (by omega : i ≤ m + 1)]
      simp
    · exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _

/-- The projection `σ^{≥ i} Y ⟶ Y^i[-i]`. -/
noncomputable def stupidGEπ (Y : CochainComplex C ℤ) (i : ℤ) :
    stupidGE Y i ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) i).obj (Y.X i) :=
  HomologicalComplex.mkHomToSingle (eqToHom (stupidGE_X_of_le Y le_rfl)) fun j hj => by
    exact (isZero_stupidGE_X_of_lt Y (by simp at hj; omega)).eq_of_src _ _

/-- In degrees `m ≥ i + 1`, the inclusion `σ^{≥ i + 1} Y ⟶ σ^{≥ i} Y` is the identity. -/
lemma stupidGEMap_f_of_le (Y : CochainComplex C ℤ) {i m : ℤ} (h : i + 1 ≤ m) :
    (stupidGEMap Y i).f m =
      eqToHom (stupidGE_X_of_le Y h) ≫ eqToHom (stupidGE_X_of_le Y (by omega : i ≤ m)).symm :=
  dif_pos h

/-- In degree `i`, the projection `σ^{≥ i} Y ⟶ Y^i[-i]` is the identity of `Y^i`. -/
lemma stupidGEπ_f (Y : CochainComplex C ℤ) (i : ℤ) :
    (stupidGEπ Y i).f i = eqToHom (stupidGE_X_of_le Y le_rfl) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i (Y.X i)).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- The composite `σ^{≥ i + 1} Y ⟶ σ^{≥ i} Y ⟶ Y^i[-i]` is zero. -/
lemma stupidGEMap_π (Y : CochainComplex C ℤ) (i : ℤ) :
    stupidGEMap Y i ≫ stupidGEπ Y i = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun m => ?_
  by_cases h : m = i
  · subst h
    exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i (Y.X i) m h).eq_of_tgt _ _

/-- The short complex `σ^{≥ i + 1} Y ⟶ σ^{≥ i} Y ⟶ Y^i[-i]`. -/
noncomputable def stupidGEShortComplex (Y : CochainComplex C ℤ) (i : ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (stupidGEMap Y i) (stupidGEπ Y i) (stupidGEMap_π Y i)

end Trunc

section TruncAbelian

variable {C : Type*} [Category C] [Abelian C]

/-- The short complex `σ^{≥ i + 1} Y ⟶ σ^{≥ i} Y ⟶ Y^i[-i]` is short exact in each degree. -/
lemma stupidGEShortComplex_shortExact (Y : CochainComplex C ℤ) (i m : ℤ) :
    ((stupidGEShortComplex Y i).map (HomologicalComplex.eval _ _ m)).ShortExact := by
  set S := (stupidGEShortComplex Y i).map (HomologicalComplex.eval _ _ m)
  rcases lt_trichotomy m i with h | rfl | h
  · have h₁ : IsZero S.X₁ := isZero_stupidGE_X_of_lt Y (by omega)
    have h₂ : IsZero S.X₂ := isZero_stupidGE_X_of_lt Y h
    have h₃ : IsZero S.X₃ :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i (Y.X i) m (by omega)
    haveI : Mono S.f := h₁.mono _
    haveI : Epi S.g := h₃.epi _
    exact ⟨ShortComplex.exact_of_isZero_X₂ _ h₂⟩
  · have h₁ : IsZero S.X₁ := isZero_stupidGE_X_of_lt Y (by omega)
    haveI : IsIso S.g := by
      change IsIso ((stupidGEπ Y m).f m)
      rw [stupidGEπ_f]
      infer_instance
    haveI : Mono S.f := h₁.mono _
    exact ⟨(ShortComplex.exact_iff_mono _ (h₁.eq_of_src _ _)).2 inferInstance⟩
  · have h₃ : IsZero S.X₃ :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i (Y.X i) m (by omega)
    haveI : IsIso S.f := by
      change IsIso ((stupidGEMap Y i).f m)
      rw [stupidGEMap_f_of_le Y (by omega)]
      infer_instance
    haveI : Epi S.g := h₃.epi _
    exact ⟨(ShortComplex.exact_iff_epi _ (h₃.eq_of_tgt _ _)).2 inferInstance⟩

/-- If `Y` vanishes in degrees below `i`, the inclusion `σ^{≥ i} Y ⟶ Y` is an isomorphism. -/
lemma isIso_stupidGEι (Y : CochainComplex C ℤ) (i : ℤ) (hY : ∀ m, m < i → IsZero (Y.X m)) :
    IsIso (stupidGEι Y i) := by
  haveI : ∀ m, IsIso ((stupidGEι Y i).f m) := fun m => by
    by_cases h : i ≤ m
    · rw [stupidGEι_f_of_le Y h]
      infer_instance
    · exact isIso_of_source_target_iso_zero _ (isZero_stupidGE_X_of_lt Y (by omega)).isoZero
        (hY m (by omega)).isoZero
  exact HomologicalComplex.Hom.isIso_of_components _

/-- If `Y` vanishes in degrees `m ≥ i`, the stupid truncation `σ^{≥ i} Y` is zero. -/
lemma isZero_stupidGE (Y : CochainComplex C ℤ) (i : ℤ) (hY : ∀ m, i ≤ m → IsZero (Y.X m)) :
    IsZero (stupidGE Y i) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.hom_ext _ _ fun m => ?_
  by_cases h : i ≤ m
  · exact ((hY m h).of_iso (eqToIso (stupidGE_X_of_le Y h))).eq_of_src _ _
  · exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _

end TruncAbelian

section Counting

/-- In a short exact sequence `A ↪ B ↠ C` of finite abelian groups, `#B = #A · #C`. -/
lemma card_eq_mul_of_exact {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (φ : A →+ B) (ψ : B →+ C) (hφ : Function.Injective φ)
    (hψ : Function.Surjective ψ) (h : ∀ b, ψ b = 0 ↔ b ∈ φ.range) [Finite B] :
    Nat.card B = Nat.card A * Nat.card C := by
  have hker : ψ.ker = φ.range := by ext b; exact h b
  have e := QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  rw [hc, Nat.card_congr e.toEquiv, mul_comm, hker,
    Nat.card_congr (AddMonoidHom.ofInjective hφ).toEquiv.symm]

variable {T : TopCat.{u}} {C : Type*} [Category C] [Abelian C]
  (G : C ⥤ TopCat.Sheaf AddCommGrpCat.{u} T) [G.Additive] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G]

/-- The Godement hypercohomology of the image of a complex under `G`. -/
noncomputable abbrev hypG (m : ℤ) (K : CochainComplex C ℤ) : AddCommGrpCat.{u} :=
  (hypercohomology T m).obj ((G.mapHomologicalComplex _).obj K)

/-- Godement hypercohomology in degree `m` preserves zero morphisms. -/
lemma preservesZeroMorphisms_hypercohomology (m : ℤ) :
    (hypercohomology T m).PreservesZeroMorphisms :=
  inferInstanceAs ((godementSections T).mapHomologicalComplex _ ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (c₁₂ := ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor _ _ m).PreservesZeroMorphisms

/-- The Godement hypercohomology of a zero complex is zero. -/
lemma isZero_hypercohomology {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    (hK : IsZero K) (m : ℤ) : IsZero ((hypercohomology T m).obj K) := by
  haveI := preservesZeroMorphisms_hypercohomology (T := T) m
  exact (hypercohomology T m).map_isZero hK

/-- The Godement hypercohomology of the image under `G` of a zero complex is zero. -/
lemma isZero_hypG {K : CochainComplex C ℤ} (hK : IsZero K) (m : ℤ) : IsZero (hypG G m K) :=
  isZero_hypercohomology ((G.mapHomologicalComplex _).map_isZero hK) m

/-- The inclusions `σ^{≥ i + 1} Y ⟶ σ^{≥ i} Y ⟶ Y` compose to `σ^{≥ i + 1} Y ⟶ Y`. -/
lemma stupidGEMap_ι (Y : CochainComplex C ℤ) (i : ℤ) :
    stupidGEMap Y i ≫ stupidGEι Y i = stupidGEι Y (i + 1) := by
  ext m
  by_cases h : i + 1 ≤ m
  · rw [HomologicalComplex.comp_f, stupidGEMap_f_of_le Y h, stupidGEι_f_of_le Y (by omega),
      stupidGEι_f_of_le Y h]
    simp
  · exact (isZero_stupidGE_X_of_lt Y (by omega)).eq_of_src _ _

/-- The Godement long exact sequence of a degreewise short exact sequence of bounded complexes,
in the form of the toolkit. -/
lemma shortExact_total_of_shortExact (S : ShortComplex (CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ))
    (hS : ∀ i : ℤ, (S.map (HomologicalComplex.eval _ _ i)).ShortExact)
    (hb : ∃ a b : ℤ, S.X₁.IsStrictlyGE a ∧ S.X₁.IsStrictlyLE b ∧ S.X₂.IsStrictlyGE a ∧
      S.X₂.IsStrictlyLE b ∧ S.X₃.IsStrictlyGE a ∧ S.X₃.IsStrictlyLE b) :
    (ShortComplex.mk
      (HomologicalComplex₂.total.map
        (((godementSections T).mapHomologicalComplex _).map S.f) (ComplexShape.up ℤ))
      (HomologicalComplex₂.total.map
        (((godementSections T).mapHomologicalComplex _).map S.g) (ComplexShape.up ℤ))
      (by
        rw [← HomologicalComplex₂.total.map_comp, ← Functor.map_comp, S.zero, Functor.map_zero]
        ext n : 1
        exact HomologicalComplex₂.total.hom_ext _ fun _ _ _ => by simp)).ShortExact :=
  ((sheafCohomology_toolkit.{u, 0, 0, 0, 0} T).2.2.1.2.1 S hS hb).1

/-- If `K` is concentrated in degrees `[0, n]`, so is its image under `G`. -/
lemma bounds_mapHC {K : CochainComplex C ℤ} (n : ℕ)
    (hK : ∀ m : ℤ, m < 0 ∨ (n : ℤ) < m → IsZero (K.X m)) :
    CochainComplex.IsStrictlyGE ((G.mapHomologicalComplex _).obj K) 0 ∧
      CochainComplex.IsStrictlyLE ((G.mapHomologicalComplex _).obj K) n :=
  ⟨(CochainComplex.isStrictlyGE_iff _ _).2 fun m hm => Functor.map_isZero G (hK m (Or.inl hm)),
    (CochainComplex.isStrictlyLE_iff _ _).2 fun m hm => Functor.map_isZero G (hK m (Or.inr hm))⟩

/-- If `Y` is concentrated in degrees `[0, n]`, so is each stupid truncation `σ^{≥ j} Y`. -/
lemma isZero_stupidGE_X_out (Y : CochainComplex C ℤ) (n : ℕ) (j : ℤ)
    (hY : ∀ m : ℤ, m < 0 ∨ (n : ℤ) < m → IsZero (Y.X m)) (m : ℤ) (hm : m < 0 ∨ (n : ℤ) < m) :
    IsZero ((stupidGE Y j).X m) := by
  by_cases h : j ≤ m
  · exact (hY m hm).of_iso (eqToIso (stupidGE_X_of_le Y h))
  · exact isZero_stupidGE_X_of_lt Y (by omega)

/-- In an exact sequence `A → B → C` of abelian groups with `A` and `C` finite, `B` is finite. -/
lemma finite_of_exact {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (φ : A →+ B) (ψ : B →+ C) (h : ∀ b, ψ b = 0 ↔ b ∈ φ.range) [Finite A]
    [Finite C] : Finite B := by
  have hker : ψ.ker = φ.range := by ext b; exact h b
  have e := QuotientAddGroup.quotientKerEquivRange ψ
  haveI : Finite φ.range := (Set.finite_range φ).to_subtype
  haveI : Finite ψ.ker := by rw [hker]; infer_instance
  haveI : Finite (B ⧸ ψ.ker) := Finite.of_equiv _ e.toEquiv.symm
  apply Nat.finite_of_card_ne_zero
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/-- **Counting along a short exact sequence of complexes of abelian groups** whose first map is
injective on homology in degrees `m` and `m + 1`. -/
lemma card_homology_eq_mul (S : ShortComplex (CochainComplex AddCommGrpCat.{u} ℤ))
    (hS : S.ShortExact) (m : ℤ)
    (h₁ : Function.Injective (HomologicalComplex.homologyMap S.f m).hom)
    (h₁' : Function.Injective (HomologicalComplex.homologyMap S.f (m + 1)).hom)
    [Finite (S.X₁.homology m)] [Finite (S.X₃.homology m)] :
    Finite (S.X₂.homology m) ∧
      Nat.card (S.X₂.homology m) = Nat.card (S.X₁.homology m) * Nat.card (S.X₃.homology m) := by
  have e2 := (ShortComplex.ab_exact_iff _).1 (hS.homology_exact₂ m)
  have e3 := (ShortComplex.ab_exact_iff _).1 (hS.homology_exact₃ m (m + 1) rfl)
  have e1 := hS.δ_comp m (m + 1) rfl
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap S.g m).hom := by
    intro x₃
    refine e3 x₃ (h₁' ?_)
    rw [map_zero]
    exact (ConcreteCategory.comp_apply _ _ x₃).symm.trans (by rw [e1]; rfl)
  have hex : ∀ b, (HomologicalComplex.homologyMap S.g m).hom b = 0 ↔
      b ∈ (HomologicalComplex.homologyMap S.f m).hom.range := fun b => ⟨fun hb => e2 b hb, by
    rintro ⟨a, rfl⟩
    exact (ConcreteCategory.comp_apply _ _ a).symm.trans (by
      rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero]
      rfl)⟩
  haveI := finite_of_exact _ _ hex
  exact ⟨inferInstance, card_eq_mul_of_exact _ _ h₁ hsurj hex⟩

/-- For `Y` concentrated in degrees `[0, n]`, if the hypercohomology of each `Y^a[-a]` is finite
and each inclusion `σ^{≥ i} Y ⟶ Y` is injective on hypercohomology, then the hypercohomology of
`σ^{≥ i} Y` is finite, of cardinality the product over `i ≤ a ≤ n` of those of `Y^a[-a]`. -/
lemma card_hypG_stupidGE (Y : CochainComplex C ℤ) (n : ℕ)
    (hY : ∀ m : ℤ, m < 0 ∨ (n : ℤ) < m → IsZero (Y.X m))
    (hfin : ∀ a m : ℤ, Finite (hypG G m ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj
      (Y.X a))))
    (hinj : ∀ i m : ℤ, Function.Injective
      ((hypercohomology T m).map ((G.mapHomologicalComplex _).map (stupidGEι Y i))).hom) :
    ∀ (d i : ℕ), i + d = n + 1 → ∀ m : ℤ,
      Finite (hypG G m (stupidGE Y i)) ∧
      Nat.card (hypG G m (stupidGE Y i)) =
        ∏ a ∈ Finset.Ico i (n + 1), Nat.card (hypG G m
          ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (Y.X a))) := by
  intro d
  induction d with
  | zero =>
    intro i hi m
    obtain rfl : i = n + 1 := by omega
    have hz := isZero_hypG G (isZero_stupidGE Y ((n + 1 : ℕ) : ℤ)
      (fun m hm => hY m (Or.inr (by push_cast at hm; omega)))) m
    haveI : Subsingleton (hypG G m (stupidGE Y ((n + 1 : ℕ) : ℤ))) :=
      (AddCommGrpCat.isZero_iff_subsingleton).1 hz
    refine ⟨inferInstance, ?_⟩
    rw [Finset.Ico_self, Finset.prod_empty]
    exact Nat.card_of_subsingleton 0
  | succ d ih =>
    intro i hi m
    have ih' := fun m => ih (i + 1) (by omega) m
    simp only [Nat.cast_add, Nat.cast_one] at ih'
    set S := (stupidGEShortComplex Y (i : ℤ)).map (G.mapHomologicalComplex _) with hSdef
    have hSex : ∀ j, (S.map (HomologicalComplex.eval _ _ j)).ShortExact := fun j =>
      (stupidGEShortComplex_shortExact Y i j).map_of_exact G
    have hb : ∃ a b : ℤ, CochainComplex.IsStrictlyGE S.X₁ a ∧ CochainComplex.IsStrictlyLE S.X₁ b ∧
        CochainComplex.IsStrictlyGE S.X₂ a ∧ CochainComplex.IsStrictlyLE S.X₂ b ∧
        CochainComplex.IsStrictlyGE S.X₃ a ∧ CochainComplex.IsStrictlyLE S.X₃ b := by
      obtain ⟨h1, h2⟩ := bounds_mapHC G n (isZero_stupidGE_X_out Y n ((i : ℤ) + 1) hY)
      obtain ⟨h3, h4⟩ := bounds_mapHC G n (isZero_stupidGE_X_out Y n (i : ℤ) hY)
      obtain ⟨h5, h6⟩ := bounds_mapHC G n (K := (HomologicalComplex.single C (ComplexShape.up ℤ)
        (i : ℤ)).obj (Y.X i)) (fun m hm => by
          by_cases h : m = (i : ℤ)
          · subst h
            exact (hY _ hm).of_iso (HomologicalComplex.singleObjXSelf _ _ _)
          · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
      exact ⟨0, n, h1, h2, h3, h4, h5, h6⟩
    have hS := shortExact_total_of_shortExact S hSex hb
    have hinjm : ∀ m', Function.Injective
        ((hypercohomology T m').map ((G.mapHomologicalComplex _).map (stupidGEMap Y i))).hom := by
      intro m'
      have h := hinj ((i : ℤ) + 1) m'
      rw [← stupidGEMap_ι, Functor.map_comp, Functor.map_comp] at h
      exact Function.Injective.of_comp h
    obtain ⟨hfin₁, hcard₁⟩ := ih' m
    haveI : Finite (hypG G m (stupidGE Y ((i : ℤ) + 1))) := hfin₁
    haveI : Finite (hypG G m ((HomologicalComplex.single C (ComplexShape.up ℤ) (i : ℤ)).obj
      (Y.X i))) := hfin i m
    obtain ⟨hfin₂, key⟩ := @card_homology_eq_mul _ hS m (hinjm m) (hinjm (m + 1)) hfin₁ (hfin i m)
    have key' : Nat.card (hypG G m (stupidGE Y i)) =
        Nat.card (hypG G m (stupidGE Y ((i : ℤ) + 1))) * Nat.card (hypG G m
          ((HomologicalComplex.single C (ComplexShape.up ℤ) (i : ℤ)).obj (Y.X i))) := key
    refine ⟨hfin₂, ?_⟩
    rw [key', hcard₁, mul_comm]
    conv_rhs => rw [Finset.prod_eq_prod_Ico_succ_bot (show i < n + 1 by omega)]

end Counting

section Shift

section RowIso

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  (B : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [B.HasTotal (ComplexShape.up ℤ)] (p : ℤ)

/-- The total degree of the bidegree `(a, b)` for the upward shapes is `a + b`. -/
lemma π_up (a b : ℤ) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) =
      a + b := rfl

/-- The inclusion of the row `p` of a bicomplex, shifted by `-p`, into its total complex. -/
noncomputable def rowToTotal (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-p)).obj (B.X p) ⟶
      B.total (ComplexShape.up ℤ) where
  f i := B.ιTotal (ComplexShape.up ℤ) p (i + -p) i (by rw [π_up]; omega)
  comm' i j hij := by
    have hj : i + 1 = j := hij
    have h1 : IsZero ((B.X (p + 1)).X (i + -p)) :=
      (HomologicalComplex.eval _ _ _).map_isZero (hB _ (by omega))
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl)
        _ _ (by rw [π_up]; omega),
      HomologicalComplex₂.d₂_eq _ _ _ (show (ComplexShape.up ℤ).Rel (i + -p) (j + -p) by
        change i + -p + 1 = j + -p; omega) _ (by rw [π_up]; omega)]
    rw [h1.eq_of_tgt ((B.d p (p + 1)).f (i + -p)) 0]
    simp [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg]

/-- For a bicomplex concentrated in row `p`, the inclusion of that row into the total complex
is an isomorphism. -/
lemma isIso_rowToTotal (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) :
    IsIso (rowToTotal B p hB) := by
  suffices h : ∀ i, IsIso ((rowToTotal B p hB).f i) from
    HomologicalComplex.Hom.isIso_of_components _
  intro i
  refine ⟨B.totalDesc (fun i₁ i₂ h => if h₁ : i₁ = p then
    (B.XXIsoOfEq _ _ _ h₁ (show i₂ = i + -p by
      have h' : i₁ + i₂ = i := h
      omega)).hom
      else 0), ?_, ?_⟩
  · simp [rowToTotal]
  · refine HomologicalComplex₂.total.hom_ext _ fun i₁ i₂ h => ?_
    by_cases h₁ : i₁ = p
    · subst h₁
      have h₂ : i₂ = i + -i₁ := by
        have h' : i₁ + i₂ = i := h
        omega
      subst h₂
      simp [rowToTotal]
    · exact ((HomologicalComplex.eval _ _ i₂).map_isZero (hB _ h₁)).eq_of_src _ _

/-- The inclusion `rowToTotal` is natural in the bicomplex. -/
@[reassoc]
lemma rowToTotal_naturality
    {B B' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [B.HasTotal (ComplexShape.up ℤ)] [B'.HasTotal (ComplexShape.up ℤ)]
    (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) (hB' : ∀ q : ℤ, q ≠ p → IsZero (B'.X q))
    (φ : B ⟶ B') :
    rowToTotal B p hB ≫ HomologicalComplex₂.total.map φ (ComplexShape.up ℤ) =
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-p)).map (φ.f p) ≫
        rowToTotal B' p hB' := by
  ext i : 1
  simp [rowToTotal]

end RowIso

section RowHomology

variable {C : Type*} [Category C] [Abelian C]
  (B : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [B.HasTotal (ComplexShape.up ℤ)] (p : ℤ)

/-- `H^n(K⟦x⟧) ≅ H^m(K)` for `x + n = m`. -/
noncomputable def shiftHomologyIso (K : CochainComplex C ℤ) (x n m : ℤ)
    (h : x + n = m) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) x).obj K).homology n ≅ K.homology m :=
  (CochainComplex.ShiftSequence.shiftIso C x n m h).app K

/-- The isomorphism `shiftHomologyIso` is natural in the complex. -/
@[reassoc]
lemma shiftHomologyIso_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (x n m : ℤ) (h : x + n = m) :
    HomologicalComplex.homologyMap
        ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) x).map φ) n ≫
      (shiftHomologyIso L x n m h).hom =
    (shiftHomologyIso K x n m h).hom ≫ HomologicalComplex.homologyMap φ m :=
  (CochainComplex.ShiftSequence.shiftIso C x n m h).hom.naturality φ

/-- The cohomology of a bicomplex concentrated in the row `p`: `H^n(Tot B) ≅ H^m(B^{p,•})` for
`-p + n = m`. -/
noncomputable def rowHomologyIso (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) (n m : ℤ)
    (h : -p + n = m) :
    (B.total (ComplexShape.up ℤ)).homology n ≅ (B.X p).homology m :=
  haveI := isIso_rowToTotal B p hB
  (asIso (HomologicalComplex.homologyMap (rowToTotal B p hB) n)).symm ≪≫
    shiftHomologyIso (B.X p) (-p) n m h

/-- The isomorphism `rowHomologyIso` is natural in the bicomplex. -/
lemma rowHomologyIso_naturality
    {B B' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [B.HasTotal (ComplexShape.up ℤ)] [B'.HasTotal (ComplexShape.up ℤ)]
    (hB : ∀ q : ℤ, q ≠ p → IsZero (B.X q)) (hB' : ∀ q : ℤ, q ≠ p → IsZero (B'.X q))
    (φ : B ⟶ B') (n m : ℤ) (h : -p + n = m) :
    (rowHomologyIso B p hB n m h).hom ≫ HomologicalComplex.homologyMap (φ.f p) m =
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) n ≫
        (rowHomologyIso B' p hB' n m h).hom := by
  haveI := isIso_rowToTotal B p hB
  haveI := isIso_rowToTotal B' p hB'
  have h2 := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (rowToTotal_naturality p hB hB' φ)
  simp only [HomologicalComplex.homologyMap_comp] at h2
  simp only [rowHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.app_hom,
    Category.assoc]
  rw [← cancel_epi (HomologicalComplex.homologyMap (rowToTotal B p hB) n),
    IsIso.hom_inv_id_assoc, reassoc_of% h2, IsIso.hom_inv_id_assoc]
  exact (shiftHomologyIso_naturality (φ.f p) (-p) n m h).symm

end RowHomology

section Godement

variable {T : TopCat.{u}}

/-- If `K` is concentrated in degree `p`, its Godement sections bicomplex is concentrated in
row `p`. -/
lemma isZero_godementSectionsDoubleComplex_X
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ} {p : ℤ}
    (hK : ∀ i, i ≠ p → IsZero (K.X i)) :
    ∀ q, q ≠ p → IsZero ((godementSectionsDoubleComplex T K).X q) :=
  fun q hq => (godementSections T).map_isZero (hK q hq)

/-- The map on Godement hypercohomology induced by `φ` is the map on homology of the total
complexes of the Godement sections bicomplexes. -/
lemma hypercohomology_map_heq {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    (φ : K ⟶ L) (n : ℤ) :
    HEq ((hypercohomology T n).map φ) (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map
        (((godementSections T).mapHomologicalComplex _).map φ) (ComplexShape.up ℤ)) n) := HEq.rfl

/-- The hypercohomology of a complex concentrated in degree `p`: `ℍ^n(T, K) ≅ H^m(Γ(T, G^•K^p))`
for `-p + n = m`. -/
noncomputable def hyperRowIso (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)
    (p : ℤ) (hK : ∀ i, i ≠ p → IsZero (K.X i)) (n m : ℤ) (h : -p + n = m) :
    (hypercohomology T n).obj K ≅ ((godementSectionsDoubleComplex T K).X p).homology m :=
  eqToIso (hypercohomology_obj T n K) ≪≫
    rowHomologyIso _ p (isZero_godementSectionsDoubleComplex_X hK) n m h

/-- The isomorphism `hyperRowIso` is natural in the complex. -/
lemma hyperRowIso_naturality {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    (φ : K ⟶ L) (p : ℤ) (hK : ∀ i, i ≠ p → IsZero (K.X i)) (hL : ∀ i, i ≠ p → IsZero (L.X i))
    (n m : ℤ) (h : -p + n = m) :
    (hyperRowIso K p hK n m h).hom ≫
        HomologicalComplex.homologyMap
          ((((godementSections T).mapHomologicalComplex _).map φ).f p) m =
      (hypercohomology T n).map φ ≫ (hyperRowIso L p hL n m h).hom := by
  have e := (conj_eqToHom_iff_heq _ _ (hypercohomology_obj T n K)
    (hypercohomology_obj T n L)).2 (hypercohomology_map_heq φ n)
  simp only [hyperRowIso, Iso.trans_hom, eqToIso.hom, Category.assoc, e, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  congr 1
  exact rowHomologyIso_naturality p _ _ _ n m h

end Godement

/-- The component at `G` of `singleHyperIso`. -/
noncomputable def singleHyperIsoApp (T : TopCat.{u}) (p n m : ℤ) (h : -p + n = m)
    (G : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (hypercohomology T n).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj G) ≅
      ((godementSections T).obj G).homology m :=
  hyperRowIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj G) p
      (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi) n m h ≪≫
    (HomologicalComplex.homologyFunctor _ _ m).mapIso
      ((godementSections T).mapIso (HomologicalComplex.singleObjXSelf _ p G))

/-- The forward map of `singleHyperIsoApp` is `hyperRowIso` followed by the homology map induced
by `singleObjXSelf`. -/
lemma singleHyperIsoApp_hom (T : TopCat.{u}) (p n m : ℤ) (h : -p + n = m)
    (G : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (singleHyperIsoApp T p n m h G).hom =
      (hyperRowIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj G) p
          (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi) n m h).hom ≫
        HomologicalComplex.homologyMap
          ((godementSections T).map (HomologicalComplex.singleObjXSelf _ p G).hom) m :=
  rfl

/-- `singleHyperIsoApp` is natural in the sheaf `G`. -/
lemma singleHyperIsoApp_naturality (T : TopCat.{u}) (p n m : ℤ) (h : -p + n = m)
    {G G' : TopCat.Sheaf AddCommGrpCat.{u} T} (g : G ⟶ G') :
    (hypercohomology T n).map ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).map g) ≫
        (singleHyperIsoApp T p n m h G').hom =
      (singleHyperIsoApp T p n m h G).hom ≫
        HomologicalComplex.homologyMap ((godementSections T).map g) m := by
  have e := hyperRowIso_naturality ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).map g)
    p (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    (fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi) n m h
  rw [singleHyperIsoApp_hom, singleHyperIsoApp_hom, ← reassoc_of% e, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 2
  rw [Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, ← Functor.map_comp,
    HomologicalComplex.single_map_f_self]
  simp

/-- The hypercohomology of the one-term complex `G[-p]`: `ℍ^n(T, G[-p]) ≅ H^m(Γ(T, G^•G))` for
`-p + n = m`, naturally in `G`. -/
noncomputable def singleHyperIso (T : TopCat.{u}) (p n m : ℤ) (h : -p + n = m) :
    HomologicalComplex.single _ (ComplexShape.up ℤ) p ⋙ hypercohomology T n ≅
      godementSections T ⋙ HomologicalComplex.homologyFunctor _ _ m :=
  NatIso.ofComponents (singleHyperIsoApp T p n m h)
    (fun g => singleHyperIsoApp_naturality T p n m h g)

/-- The identification `ℍ^n(T, G[-p]) ≅ H^m(T, G)` for `-p + n = m`, natural in `G`. -/
noncomputable def singleHyperShift (T : TopCat.{u}) (p n m : ℤ) (h : -p + n = m) :
    HomologicalComplex.single _ (ComplexShape.up ℤ) p ⋙ hypercohomology T n ≅
      sheafCohomology T m :=
  singleHyperIso T p n m h ≪≫ (singleHyperIso T 0 m m (by omega)).symm

end Shift

end Counting

/-! ### The Frobenius pushforward of the de Rham complex -/

noncomputable section Frobenius

open Limits
open scoped Stacks.SmallDerivedModel

/-- **A differential operator of order one commutes with `p`-th powers in characteristic `p`.**
If every commutator `s ↦ D(g s) - g D s` is `R`-linear and `p = 0` in `R`, then
`D(g^p s) = g^p D s`: the commutator `c_g` is a derivation in `g`, so `c_{g^p} = p g^{p-1} c_g`. -/
theorem pow_smul_of_commutator {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (D : M →+ N)
    (hD : ∀ (g r : R) (s : M), D (g • r • s) - g • D (r • s) = r • (D (g • s) - g • D s))
    (p : ℕ) (hp : (p : R) = 0) (g : R) (s : M) : D (g ^ p • s) = g ^ p • D s := by
  have hpow : ∀ m : ℕ, D (g ^ (m + 1) • s) - g ^ (m + 1) • D s =
      ((m + 1 : ℕ) : R) • g ^ m • (D (g • s) - g • D s) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : D (g ^ (m + 1 + 1) • s) - g ^ (m + 1 + 1) • D s =
          (D (g • g ^ (m + 1) • s) - g • D (g ^ (m + 1) • s)) +
            g • (D (g ^ (m + 1) • s) - g ^ (m + 1) • D s) := by
        rw [pow_succ' g (m + 1), mul_smul, mul_smul, smul_sub]
        abel
      rw [h1, hD, ih]
      simp only [smul_smul]
      rw [← add_smul]
      congr 1
      push_cast
      ring
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have := hpow m
  rw [hp, zero_smul, sub_eq_zero] at this
  exact this

section CharP

variable (p : ℕ) [Fact p.Prime] {F : Type u} [Field F] [Finite F] [CharP F p]
  {V : Scheme.{u}} (f : V ⟶ Spec (.of F))

include f in
/-- A scheme over a field of characteristic `p` is in characteristic `p`. -/
theorem isInCharacteristic_of_charP : Stacks.Frobenius.IsInCharacteristic V p := by
  have h : ((p : ℕ) : Γ(Spec (.of F), ⊤)) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso (.of F)).inv.hom, CharP.cast_eq_zero, map_zero]
  change ((p : ℕ) : Γ(V, ⊤)) = 0
  rw [← map_natCast f.appTop.hom, h, map_zero]

variable {p} (hV : Stacks.Frobenius.IsInCharacteristic V p)

/-- `F_*Ω^q`, the Frobenius pushforward of the sheaf of differential `q`-forms. -/
abbrev frobeniusForms (q : ℕ) : V.Modules :=
  (Scheme.Modules.pushforward (Stacks.Frobenius.absoluteFrobenius V p hV)).obj
    (Scheme.Hom.relativeDifferentialForms f (q : ℤ))

include hV in
/-- The de Rham differential commutes with `p`-th powers of functions in characteristic `p`. -/
theorem deRhamGlobalOp_pow_smul (q : ℕ) (U : V.Opensᵒᵖ)
    (g : V.toRingedSpace.sheaf.obj.obj U)
    (s : ((Scheme.Hom.deRhamAlgebras f).exteriorPower q).val.obj U) :
    AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q U
        (g ^ p • s) =
      g ^ p • AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q U s :=
  pow_smul_of_commutator _
    (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp_commutator_smul _ q U) p
    (Stacks.Frobenius.cast_eq_zero_of_isInCharacteristic hV U.unop) g s

/-- The de Rham differential `F_*Ω^q ⟶ F_*Ω^{q+1}` on the underlying presheaves of abelian
groups. -/
def frobeniusDeRhamDPresheaf (q : ℕ) :
    (frobeniusForms f hV q).val.presheaf ⟶ (frobeniusForms f hV (q + 1)).val.presheaf := by
  let φ₀ := (PresheafOfModules.toPresheaf _).map
    (AlgebraicGeometry.SheafOfModules.deRhamDifferentialHom (Scheme.Hom.deRhamAlgebras f) q).val
  exact φ₀

include hV in
/-- `d(r^p s) = r^p ds`, for the `𝒪_V`-module structure on the sheaves of forms. -/
theorem deRhamGlobalOp_pow_smul' (q : ℕ) (W : V.Opensᵒᵖ) (r : Γ(V, W.unop))
    (s : Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W.unop)) :
    (show Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop) from
      AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W
        (r ^ p • s)) =
      r ^ p • (show Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop) from
        AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W s) :=
  deRhamGlobalOp_pow_smul f hV q W r s

/-- The de Rham differential `F_*Ω^q ⟶ F_*Ω^{q+1}`: it is `𝒪_V`-linear for the Frobenius-twisted
module structures because `d(a^p ω) = a^p dω` in characteristic `p`. -/
def frobeniusDeRhamD (q : ℕ) : frobeniusForms f hV q ⟶ frobeniusForms f hV (q + 1) :=
  _root_.SheafOfModules.Hom.mk (PresheafOfModules.homMk (frobeniusDeRhamDPresheaf f hV q)
    fun W r s => by
      change @id Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop)
          (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W
            (@id Γ(V, W.unop) ((Stacks.Frobenius.absoluteFrobenius V p hV).app W.unop r) •
              @id Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W.unop) s)) =
        @id Γ(V, W.unop) ((Stacks.Frobenius.absoluteFrobenius V p hV).app W.unop r) •
          @id Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop)
            (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W s)
      have h := Stacks.Frobenius.absoluteFrobenius_app_apply V p hV W.unop r
      exact (congrArg (fun x : Γ(V, W.unop) =>
        @id Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop)
            (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W
              (x • @id Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W.unop) s)) =
          x • @id Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W.unop)
            (AlgebraicGeometry.SheafOfModules.deRhamGlobalOp (Scheme.Hom.deRhamAlgebras f) q W s))
        h).mpr (deRhamGlobalOp_pow_smul' f hV q W r s))

/-- On sections over `W`, `frobeniusDeRhamD` is the de Rham differential `d^q` of
`deRhamComplex f` on sections over the preimage of `W` under the absolute Frobenius. -/
theorem frobeniusDeRhamD_app (q : ℕ) (W : V.Opens)
    (s : Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ),
      Stacks.Frobenius.absoluteFrobenius V p hV ⁻¹ᵁ W)) :
    (frobeniusDeRhamD f hV q).app W s =
      ((Scheme.Hom.deRhamComplex f).d q (q + 1)).val.app (Opposite.op W) s := by
  rw [Scheme.Hom.deRhamComplex_d]
  rfl

/-- Two consecutive Frobenius-twisted de Rham differentials compose to zero: `d ∘ d = 0`. -/
theorem frobeniusDeRhamD_comp (q : ℕ) :
    frobeniusDeRhamD f hV q ≫ frobeniusDeRhamD f hV (q + 1) = 0 := by
  ext W s
  have h := congrArg (fun φ => φ.val.app (Opposite.op W) s)
    ((AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)).squared q)
  exact h

/-- The Frobenius pushforward `F_*Ω^•_V` of the de Rham complex, as a complex of `𝒪_V`-modules
indexed by `ℤ`. -/
abbrev frobeniusDeRhamComplex : CochainComplex V.Modules ℤ :=
  (CochainComplex.of (frobeniusForms f hV) (frobeniusDeRhamD f hV)
    (frobeniusDeRhamD_comp f hV)).extend ComplexShape.embeddingUpNat

/-- Restricting twice is restricting once. -/
theorem presheaf_map_map_apply {X : Scheme.{u}} (M : X.Modules) {A B C : X.Opens}
    (h₁ : B ≤ A) (h₂ : C ≤ B) (x : Γ(M, A)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting to the same open is the identity. -/
theorem presheaf_map_self_apply {X : Scheme.{u}} (M : X.Modules) {A : X.Opens}
    (h : A ≤ A) (x : Γ(M, A)) : M.presheaf.map (homOfLE h).op x = x := by
  rw [show (homOfLE h).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- A smooth morphism of relative dimension `n`, read through the empty simple normal crossing
divisor: the conditions of
`MMP.DeRham.nonempty_logDeRham_decomposition_and_injective_hypercohomology_of_wittTwoLift` at
`ι = Empty`. -/
theorem smoothOfRelativeDimension_iSup_empty {Y T : Scheme.{u}} (h : Y ⟶ T) (n : ℕ)
    [SmoothOfRelativeDimension n h] (K : Empty → Y.IdealSheafData) (Tf : Finset Empty) :
    SmoothOfRelativeDimension (n - Tf.card) ((⨆ j ∈ Tf, K j).subschemeι ≫ h) ∧
      (n < Tf.card → IsEmpty (⨆ j ∈ Tf, K j).subscheme) := by
  obtain rfl : Tf = ∅ := Subsingleton.elim _ _
  have hbot : (⨆ j ∈ (∅ : Finset Empty), K j) = ⊥ := iSup_of_empty _
  rw [hbot]
  refine ⟨?_, fun h => absurd h (Nat.not_lt_zero _)⟩
  have := (inferInstance :
    SmoothOfRelativeDimension (0 + n) ((⊥ : Y.IdealSheafData).subschemeι ≫ h))
  rw [zero_add] at this
  simpa using this

/-- **The Deligne--Illusie decomposition** `⨁_{q ≤ n} Ω^q[-q] ≅ F_*Ω^•` in `D(𝒪_V)`. -/
theorem injective_hyp_frobeniusDeRhamComplex (n : ℕ) (hpn : n < p) [IsProper f]
    [SmoothOfRelativeDimension n f]
    {𝒱 : Scheme.{u}} (g : 𝒱 ⟶ Spec (.of (TruncatedWittVector p 2 F)))
    [SmoothOfRelativeDimension n g]
    (π : TruncatedWittVector p 2 F →+* F) (hπ : ∀ x, π x = x.coeff 0) (i : V ⟶ 𝒱)
    (hi : IsPullback i f g (Spec.map (CommRingCat.ofHom π))) :
    ∀ (i : ℕ) (L : CochainComplex V.Modules ℤ) (φ : L ⟶ frobeniusDeRhamComplex f hV),
      (∀ m : ℤ, m < i → IsZero (L.X m)) → (∀ m : ℤ, (i : ℤ) ≤ m → IsIso (φ.f m)) →
      ∀ m : ℤ, Function.Injective ((MMP.Analytic.hypercohomology V.toTopCat m).map
        (((SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).hom := by
  let J : Empty → V.IdealSheafData := fun j => j.elim
  let I : Empty → 𝒱.IdealSheafData := fun j => j.elim
  set U : V.Opens := ((⨅ j, J j).support).compl with hUdef
  have hUtop : U = ⊤ := by
    rw [hUdef, iInf_of_empty]
    ext x
    simp [Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.compl]
  have hle : ∀ W : V.Opens, W ≤ W ⊓ U := fun W => by rw [hUtop, inf_top_eq]
  let K : ℕ → V.Modules := fun q => Scheme.Hom.relativeDifferentialForms f (q : ℤ)
  let e : ∀ (q : ℕ) (W : V.Opens), Γ(K q, W) →+
      Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W ⊓ U) :=
    fun q W => ((K q).presheaf.map (homOfLE inf_le_left).op).hom
  have he_inj : ∀ (q : ℕ) W, Function.Injective (e q W) := by
    intro q W x y hxy
    have h := congrArg ((K q).presheaf.map (homOfLE (hle W)).op).hom hxy
    simp only [e] at h
    rwa [presheaf_map_map_apply, presheaf_map_map_apply, presheaf_map_self_apply,
      presheaf_map_self_apply] at h
  have he_smul : ∀ (q : ℕ) W (a : Γ(V, W)) (s : Γ(K q, W)),
      e q W (a • s) = V.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op a • e q W s :=
    fun q W a s => Scheme.Modules.map_smul (K q) (homOfLE inf_le_left) a s
  have he_res : ∀ (q : ℕ) (W₁ W₂ : V.Opens) (h : W₁ ≤ W₂) (s : Γ(K q, W₂)),
      e q W₁ ((K q).presheaf.map (homOfLE h).op s) =
        (Scheme.Hom.relativeDifferentialForms f (q : ℤ)).presheaf.map
          (homOfLE (inf_le_inf_right _ h)).op (e q W₂ s) := by
    intro q W₁ W₂ h s
    simp only [e]
    rw [presheaf_map_map_apply, presheaf_map_map_apply]
  have he_range : ∀ (q : ℕ) (W : V.Opens)
      (ω : Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W ⊓ U)),
      ω ∈ Set.range (e q W) ↔
        ∀ (W' : V.affineOpens) (hW' : (W' : V.Opens) ≤ W) (c : Empty → Γ(V, W')),
          (∀ j, c j ∈ (J j).ideal W') →
          (∃ η : Γ(Scheme.Hom.relativeDifferentialForms f (q : ℤ), W'),
            (Scheme.Hom.relativeDifferentialForms f (q : ℤ)).presheaf.map
                (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op η =
              V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op (∏ j, c j) •
                (Scheme.Hom.relativeDifferentialForms f (q : ℤ)).presheaf.map
                  (homOfLE (inf_le_inf_right U hW')).op ω) ∧
          (∃ η : Γ(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ), W'),
            (Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map
                (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op η =
              V.presheaf.map (homOfLE (inf_le_left : (W' : V.Opens) ⊓ U ≤ W')).op (∏ j, c j) •
                (Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map
                  (homOfLE (inf_le_inf_right U hW')).op
                    (((f.deRhamComplex).d q (q + 1)).val.app (Opposite.op (W ⊓ U)) ω)) := by
    intro q W ω
    refine iff_of_true ⟨(K q).presheaf.map (homOfLE (hle W)).op ω, ?_⟩ fun W' hW' c _ => ⟨?_, ?_⟩
    · simp only [e]
      rw [presheaf_map_map_apply, presheaf_map_self_apply]
    · refine ⟨(Scheme.Hom.relativeDifferentialForms f (q : ℤ)).presheaf.map
        (homOfLE ((hle _).trans (inf_le_inf_right U hW'))).op ω, ?_⟩
      rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_smul]
      exact presheaf_map_map_apply _ _ _ ω
    · refine ⟨(Scheme.Hom.relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).presheaf.map
        (homOfLE ((hle _).trans (inf_le_inf_right U hW'))).op
          (((f.deRhamComplex).d q (q + 1)).val.app (Opposite.op (W ⊓ U)) ω), ?_⟩
      rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_smul]
      exact presheaf_map_map_apply _ _ _ _
  have he_d : ∀ (q : ℕ) (W : V.Opens) (s : Γ(K q, Stacks.Frobenius.absoluteFrobenius V p hV ⁻¹ᵁ W)),
      e (q + 1) (Stacks.Frobenius.absoluteFrobenius V p hV ⁻¹ᵁ W)
          ((frobeniusDeRhamD f hV q).app W s) =
        ((f.deRhamComplex).d q (q + 1)).val.app
          (Opposite.op (Stacks.Frobenius.absoluteFrobenius V p hV ⁻¹ᵁ W ⊓ U)) (e q _ s) := by
    intro q W s
    rw [frobeniusDeRhamD_app]
    exact (PresheafOfModules.naturality_apply ((Scheme.Hom.deRhamComplex f).d q (q + 1)).val
      (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s).symm
  exact (MMP.DeRham.nonempty_logDeRham_decomposition_and_injective_hypercohomology_of_wittTwoLift
    p n hpn f hV J (smoothOfRelativeDimension_iSup_empty f n J) g I π hπ i hi (fun j => j.elim)
    (smoothOfRelativeDimension_iSup_empty g n I) U hUdef K e he_inj he_smul he_res he_range
    (frobeniusDeRhamD f hV) (frobeniusDeRhamD_comp f hV) he_d).2

end CharP

end Frobenius

/-! ### Hodge numbers and de Rham numbers -/

section CharPCount

open Limits

open scoped Stacks.SmallDerivedModel

attribute [local implicit_reducible] TopCat.Sheaf

variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F] [CharP F p]
  {V : Scheme.{u}} (f : V ⟶ Spec (.of F)) (hV : Stacks.Frobenius.IsInCharacteristic V p)

/-- The underlying complex of abelian sheaves of the Frobenius pushforward of the de Rham
complex, before extension to `ℤ`. -/
noncomputable def frobAbIsoNat :
    ((SheafOfModules.toSheaf V.ringCatSheaf).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (CochainComplex.of (frobeniusForms f hV) (frobeniusDeRhamD f hV)
        (frobeniusDeRhamD_comp f hV)) ≅
    AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) :=
  HomologicalComplex.Hom.isoOfComponents (fun q => Iso.refl _) (by
    rintro q _ rfl
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d]
    refine (Category.id_comp _).trans (Eq.trans ?_ (Category.comp_id _).symm)
    have h : CochainComplex.of.d (frobeniusForms f hV) (frobeniusDeRhamD f hV) q (q + 1) =
        frobeniusDeRhamD f hV q := by
      simp [CochainComplex.of.d]
    refine Eq.trans ?_ (congrArg (SheafOfModules.toSheaf V.ringCatSheaf).map h).symm
    ext U x
    exact (frobeniusDeRhamD_app f hV q U.unop x).symm)

section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Stacks' de Rham cohomology in the abelian realization is Godement hypercohomology. -/
noncomputable def deRhamAbelianIsoHyp {X S : Scheme.{u}} (g : X ⟶ S) (m : ℤ) :
    Scheme.Hom.deRhamCohomology g m ≅
      (hypercohomology X.toTopCat m).obj
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexInt (Scheme.Hom.deRhamAlgebras g)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g))) :=
  (bridgeIso X.toTopCat m).app
    (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (Scheme.Hom.deRhamAlgebras g)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)))

end

/-- The Frobenius pushforward of the de Rham complex has the de Rham complex as underlying complex
of abelian sheaves. -/
noncomputable def frobAbIso :
    ((SheafOfModules.toSheaf V.ringCatSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (frobeniusDeRhamComplex f hV) ≅
      AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexInt (Scheme.Hom.deRhamAlgebras f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (SheafOfModules.toSheaf V.ringCatSheaf)
      (CochainComplex.of (frobeniusForms f hV) (frobeniusDeRhamD f hV)
        (frobeniusDeRhamD_comp f hV)) ComplexShape.embeddingUpNat).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (frobAbIsoNat f hV)

/-- The de Rham cohomology `H^m_dR(V/F)` has the same cardinality as the hypercohomology
`ℍ^m(V, F_*Ω^•)` of the Frobenius-twisted de Rham complex `frobeniusDeRhamComplex`. -/
lemma card_deRham_eq_card_hyp (m : ℤ) :
    Nat.card ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of F)).inv.hom).obj
      (f.deRhamCohomologyBaseModule m)) =
    Nat.card ((hypercohomology V.toTopCat m).obj
      (((SheafOfModules.toSheaf V.ringCatSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (frobeniusDeRhamComplex f hV))) := by
  let e₁ := (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (Scheme.Hom.deRhamAlgebras f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m).symm
  let e₂ := deRhamAbelianIsoHyp f m
  let e₃ := (hypercohomology V.toTopCat m).mapIso (frobAbIso f hV).symm
  exact Nat.card_congr ((e₁ ≪≫ e₂ ≪≫ e₃).addCommGroupIsoToAddEquiv.toEquiv)

/-- For a complex `K` of abelian sheaves concentrated in degrees `≥ a`, `ℍ^k(T, K) = 0` for
`k < a`. -/
lemma isZero_hypercohomology_of_lt {T : TopCat.{u}} (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ)
    (a : ℤ) [K.IsStrictlyGE a] (k : ℤ) (hk : k < a) : IsZero ((hypercohomology T k).obj K) :=
  StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X k
    (StacksDraft.TotalComplexQuasiIso.isZero_total_X (godementSectionsDoubleComplex T K) a
      (fun p q hq => HomologicalComplex.isZero_extend_X _ _ q
        (by intro n hn; change ((n : ℕ) : ℤ) = q at hn; omega))
      (fun p hp => (godementSections T).map_isZero (K.isZero_of_isStrictlyGE a p hp)) k hk)

/-- For an abelian sheaf `G` and `k < 0`, the group `H^k(T, G)` has exactly one element. -/
lemma card_sheafCohomology_neg {T : TopCat.{u}} (G : TopCat.Sheaf AddCommGrpCat.{u} T) (k : ℤ)
    (hk : k < 0) : Nat.card ((sheafCohomology T k).obj G) = 1 := by
  have h := isZero_hypercohomology_of_lt ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)
    0 k hk
  haveI : Subsingleton ((sheafCohomology T k).obj G) := (AddCommGrpCat.isZero_iff_subsingleton).1 h
  exact Nat.card_of_subsingleton 0

/-- For `g : X ⟶ S` smooth of relative dimension `n`, every exterior power `Λ^a Ω_{X/S}` is
finite locally free. -/
lemma isFiniteLocallyFree_exteriorPower {X S : Scheme.{u}} (g : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n g] (a : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials g) a) :=
  haveI := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials g n
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (hM := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
      (Scheme.Hom.relativeDifferentials g) n a) _ (n.choose a)

/-- For `g : X ⟶ S` smooth of relative dimension `d`, the sheaf `Ω^m_{X/S}` is zero for
`m > d`. -/
lemma isZero_relativeDifferentialForms_of_lt {X S : Scheme.{u}} (g : X ⟶ S) (d : ℕ)
    [SmoothOfRelativeDimension d g] (m : ℤ) (hm : (d : ℤ) < m) :
    IsZero (Scheme.Hom.relativeDifferentialForms g m) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ m by omega)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf)
      (Scheme.Hom.relativeDifferentials g) d :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials g d
  refine (IsZero.iff_id_eq_zero _).2 (_root_.SheafOfModules.hom_ext ?_)
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  exact Stacks.SheafOfModules.TopWedge.exteriorPower_eq_zero_of_lt
    (_root_.SheafOfModules.algebras _ (Scheme.Hom.relativeDifferentials g)) d m (by omega) U z

/-- The underlying abelian sheaf, as a functor to `TopCat.Sheaf`. -/
noncomputable abbrev Gv (V : Scheme.{u}) : V.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} V.toTopCat :=
  SheafOfModules.toSheaf V.ringCatSheaf

/-- The functor `Gv V` is additive. -/
lemma Gv_additive (V : Scheme.{u}) : (Gv V).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf V.ringCatSheaf).Additive

/-- The functor `Gv V` preserves finite limits. -/
lemma Gv_preservesFiniteLimits (V : Scheme.{u}) : PreservesFiniteLimits (Gv V) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf V.ringCatSheaf))

/-- The functor `Gv V` preserves finite colimits. -/
lemma Gv_preservesFiniteColimits (V : Scheme.{u}) : PreservesFiniteColimits (Gv V) :=
  Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits _ V.ringCatSheaf

attribute [local instance] Gv_additive Gv_preservesFiniteLimits Gv_preservesFiniteColimits

/-- The hypercohomology `ℍ^m` of the one-term complex `(F_*Ω^a)[-a]` has cardinality
`|F| ^ dim_F H^{m-a}(V, Ω^a)` if `a ≤ m`, and `1` otherwise. -/
lemma card_hyp_single_frob [IsProper f] (n : ℕ) [SmoothOfRelativeDimension n f] (a : ℕ) (m : ℤ) :
    Nat.card (hypG (Gv V) m
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) (a : ℤ)).obj
        ((frobeniusDeRhamComplex f hV).X a))) =
      if (a : ℤ) ≤ m then Nat.card F ^ Module.finrank F
        (cohomologyOverField F f (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) (m - a).toNat)
      else 1 := by
  let G := Gv V
  let e₀ := (hypercohomology V.toTopCat m).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) (a : ℤ)).app
      ((frobeniusDeRhamComplex f hV).X a))
  let e₁ := (singleHyperShift V.toTopCat (a : ℤ) m (m - a) (by omega)).app
    (G.obj ((frobeniusDeRhamComplex f hV).X a))
  let e₂ := (sheafCohomology V.toTopCat (m - a)).mapIso (G.mapIso
    ((CochainComplex.of (frobeniusForms f hV) (frobeniusDeRhamD f hV)
      (frobeniusDeRhamD_comp f hV)).extendXIso ComplexShape.embeddingUpNat (i := a) rfl))
  have hc : Nat.card (hypG G m ((HomologicalComplex.single _ (ComplexShape.up ℤ) (a : ℤ)).obj
      ((frobeniusDeRhamComplex f hV).X a))) =
      Nat.card ((sheafCohomology V.toTopCat (m - a)).obj
        (G.obj (Scheme.Hom.relativeDifferentialForms f (a : ℤ)))) :=
    Nat.card_congr ((e₀ ≪≫ e₁ ≪≫ e₂).addCommGroupIsoToAddEquiv.toEquiv)
  rw [hc]
  split_ifs with ha
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, m - a = j := ⟨(m - a).toNat, by omega⟩
    rw [hj, Int.toNat_natCast]
    obtain ⟨e, -⟩ := MMP.Analytic.exists_addEquiv_sheafCohomology_cohomologyOverField f
      (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) j
    rw [Nat.card_congr e.toEquiv]
    haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian f
    haveI := isFiniteLocallyFree_exteriorPower f n a
    haveI hc := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree V
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) a)
    haveI : (Scheme.Hom.relativeDifferentialForms f (a : ℤ)).IsCoherent := hc
    haveI := finiteDimensional_cohomologyOverField_of_isProper F f
      (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) j
    exact Module.natCard_eq_pow_finrank
  · exact card_sheafCohomology_neg _ _ (by omega)

include hV in
/-- The degree-`m` term of `frobeniusDeRhamComplex` is zero when `m < 0` or `m > n`. -/
lemma isZero_frob_X [IsProper f] (n : ℕ) [SmoothOfRelativeDimension n f] (m : ℤ)
    (hm : m < 0 ∨ (n : ℤ) < m) : IsZero ((frobeniusDeRhamComplex f hV).X m) := by
  rcases hm with hm | hm
  · exact HomologicalComplex.isZero_extend_X _ _ _ fun i' h' => by
      rw [ComplexShape.embeddingUpNat_f] at h'; omega
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, m = (a : ℤ) := ⟨m.toNat, by omega⟩
    exact IsZero.of_iso ((Scheme.Modules.pushforward _).map_isZero
      (isZero_relativeDifferentialForms_of_lt f n (a : ℤ) hm))
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f a))

/-- **Hodge numbers add up to de Rham numbers in characteristic `p`**, for a proper smooth
scheme of relative dimension `n < p` over a finite field with a lift over `W₂`. -/
theorem sum_finrank_eq_finrank_deRham_charP [IsProper f] (n : ℕ) (hpn : n < p)
    [SmoothOfRelativeDimension n f]
    {𝒱 : Scheme.{u}} (g : 𝒱 ⟶ Spec (.of (TruncatedWittVector p 2 F)))
    [SmoothOfRelativeDimension n g]
    (π : TruncatedWittVector p 2 F →+* F) (hπ : ∀ x, π x = x.coeff 0) (i : V ⟶ 𝒱)
    (hi : IsPullback i f g (Spec.map (CommRingCat.ofHom π))) (m : ℕ) :
    ∑ a ∈ Finset.range (m + 1), Module.finrank F
        (cohomologyOverField F f (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) (m - a)) =
      Module.finrank F ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of F)).inv.hom).obj
        (f.deRhamCohomologyBaseModule (m : ℤ))) := by
  set hV := isInCharacteristic_of_charP p f
  set Y := frobeniusDeRhamComplex f hV
  have hY : ∀ m' : ℤ, m' < 0 ∨ (n : ℤ) < m' → IsZero (Y.X m') := isZero_frob_X f hV n
  have hfin : ∀ a m' : ℤ, Finite (hypG (Gv V) m'
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj (Y.X a))) := by
    intro a m'
    rcases lt_or_ge a 0 with ha | ha
    · have hz := isZero_hypG (Gv V) ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).map_isZero
        (hY a (Or.inl ha))) m'
      haveI := (AddCommGrpCat.isZero_iff_subsingleton).1 hz
      exact Finite.of_subsingleton
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = (k : ℤ) := ⟨a.toNat, by omega⟩
      apply Nat.finite_of_card_ne_zero
      rw [card_hyp_single_frob f hV n k m']
      split_ifs
      · exact pow_ne_zero _ Nat.card_pos.ne'
      · exact one_ne_zero
  have hinj : ∀ i' m' : ℤ, Function.Injective ((hypercohomology V.toTopCat m').map
      (((Gv V).mapHomologicalComplex _).map (stupidGEι Y i'))).hom := by
    intro i' m'
    rcases lt_or_ge i' 0 with hi' | hi'
    · haveI := isIso_stupidGEι Y i' (fun m'' hm'' => hY m'' (Or.inl (by omega)))
      exact (ConcreteCategory.bijective_of_isIso _).1
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i' = (k : ℤ) := ⟨i'.toNat, by omega⟩
      refine injective_hyp_frobeniusDeRhamComplex f hV n hpn g π hπ i hi k (stupidGE Y k)
        (stupidGEι Y k) (fun m'' hm'' => isZero_stupidGE_X_of_lt Y hm'') (fun m'' hm'' => ?_) m'
      rw [stupidGEι_f_of_le Y hm'']
      infer_instance
  have hcount := card_hypG_stupidGE (Gv V) Y n hY hfin hinj (n + 1) 0 (by omega) m
  haveI : IsIso (stupidGEι Y ((0 : ℕ) : ℤ)) :=
    isIso_stupidGEι Y _ (fun m'' hm'' => hY m'' (Or.inl (by omega)))
  let e₀ := (hypercohomology V.toTopCat m).mapIso
    (((Gv V).mapHomologicalComplex _).mapIso (asIso (stupidGEι Y ((0 : ℕ) : ℤ))))
  have hcardY : Nat.card ((hypercohomology V.toTopCat m).obj
      (((Gv V).mapHomologicalComplex _).obj Y)) =
      ∏ a ∈ Finset.range (n + 1), Nat.card F ^ (if (a : ℤ) ≤ (m : ℤ) then Module.finrank F
        (cohomologyOverField F f (Scheme.Hom.relativeDifferentialForms f (a : ℤ))
          ((m : ℤ) - a).toNat) else 0) := by
    rw [← Nat.card_congr e₀.addCommGroupIsoToAddEquiv.toEquiv, hcount.2, Finset.range_eq_Ico]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [card_hyp_single_frob f hV n a m]
    split_ifs <;> simp
  set dR := (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of F)).inv.hom).obj
    (f.deRhamCohomologyBaseModule (m : ℤ))
  have hdR : Nat.card dR = Nat.card F ^ ∑ a ∈ Finset.range (n + 1),
      (if (a : ℤ) ≤ (m : ℤ) then Module.finrank F
        (cohomologyOverField F f (Scheme.Hom.relativeDifferentialForms f (a : ℤ))
          ((m : ℤ) - a).toNat) else 0) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← hcardY]
    exact card_deRham_eq_card_hyp f hV m
  haveI : Finite dR := Nat.finite_of_card_ne_zero (by rw [hdR]; exact pow_ne_zero _ Nat.card_pos.ne')
  haveI : Module.Finite F dR := Module.Finite.of_finite
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [Module.natCard_eq_pow_finrank (K := F) (V := dR)] at hdR
  rw [Nat.pow_right_injective h1 hdR]
  have key : ∀ N : ℕ, n ≤ N → m ≤ N →
      ∑ a ∈ Finset.range (N + 1), (if (a : ℤ) ≤ (m : ℤ) then Module.finrank F
        (cohomologyOverField F f (Scheme.Hom.relativeDifferentialForms f (a : ℤ))
          ((m : ℤ) - a).toNat) else 0) =
      ∑ a ∈ Finset.range (m + 1), Module.finrank F
        (cohomologyOverField F f (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) (m - a)) := by
    intro N hnN hmN
    rw [← Finset.sum_range_add_sum_Ico _ (show m + 1 ≤ N + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (m + 1) (N + 1)) (fun a ha => by
      rw [Finset.mem_Ico] at ha
      rw [if_neg (by omega)]), add_zero]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_range] at ha
    rw [if_pos (by omega), show ((m : ℤ) - a).toNat = m - a by omega]
  have key2 : ∑ a ∈ Finset.range (n + m + 1), (if (a : ℤ) ≤ (m : ℤ) then Module.finrank F
        (cohomologyOverField F f (Scheme.Hom.relativeDifferentialForms f (a : ℤ))
          ((m : ℤ) - a).toNat) else 0) =
      ∑ a ∈ Finset.range (n + 1), (if (a : ℤ) ≤ (m : ℤ) then Module.finrank F
        (cohomologyOverField F f (Scheme.Hom.relativeDifferentialForms f (a : ℤ))
          ((m : ℤ) - a).toNat) else 0) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ n + m + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (n + 1) (n + m + 1)) (fun a ha => by
      rw [Finset.mem_Ico] at ha
      split_ifs
      · have hz := isZero_relativeDifferentialForms_of_lt f n (a : ℤ) (by omega)
        have hz' : IsZero (cohomologyOverField F f (Scheme.Hom.relativeDifferentialForms f (a : ℤ))
            ((m : ℤ) - a).toNat) :=
          (ModuleCat.restrictScalars _).map_isZero
            (((SheafOfModules.evaluation V.ringCatSheaf (op (⊤ : V.Opens))).rightDerived
              _).map_isZero hz)
        haveI := ModuleCat.subsingleton_of_isZero hz'
        exact Module.finrank_zero_of_subsingleton
      · rfl), add_zero]
  rw [← key2, key (n + m) (by omega) (by omega)]

end CharPCount

section CharZeroCount

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open AlgebraicGeometry.HodgeSpreadingOut

/-- Let `h : Y ⟶ Spec R` be smooth over a domain `R`, and let `f : X ⟶ Spec k` be its base change
along an injective ring map `R →+* k` to a field. If `f` is smooth of relative dimension `n`, so
is `h`. -/
theorem smoothOfRelativeDimension_of_isPullback {R : Type u} [CommRing R] [IsDomain R]
    {k : Type u} [Field k] (φ : R →+* k) (hφ : Function.Injective φ) {X Y : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {h : Y ⟶ Spec (.of R)} {q' : X ⟶ Y}
    (hpb : IsPullback q' f h (Spec.map (CommRingCat.ofHom φ))) [Smooth h] (n : ℕ)
    [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n h := by
  classical
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq h n fun y => ?_
  set F : Y → WithBot ℕ∞ := fun y => topologicalKrullDimAt (h.fiber (h y)) (h.asFiber y) with hFdef
  have hWo : IsOpen {y' | F y' = F y} :=
    (isLocallyConstant_fiberDimensionAt h (syntomic_of_smooth h)).isOpen_fiber (F y)
  have himg : IsOpen (h.base '' {y' | F y' = F y}) := h.isOpenMap _ hWo
  let ptk : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : ∀ s : Spec (.of R), (Spec.map (CommRingCat.ofHom φ)).base ptk ⤳ s := fun s =>
    (PrimeSpectrum.le_iff_specializes _ _).mp (by
      change Ideal.comap φ ⊥ ≤ s.asIdeal
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot φ).mp hφ]
      exact bot_le)
  obtain ⟨y', hy'F, hy'η⟩ := (hη (h y)).mem_open himg ⟨y, rfl, rfl⟩
  obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback y' ptk hy'η
  have hx : q' (hpb.isoPullback.inv z) = y' := by
    rw [← hz₁, ← hpb.isoPullback_inv_fst]
    rfl
  change F y = n
  rw [← show F y' = F y from hy'F, ← hx]
  exact (topologicalKrullDimAt_fiber_eq_of_isPullback hpb _).symm.trans
    (fiberDimensionAt_eq_of_smoothOfRelativeDimension f n _)

section

attribute [local instance 10000] HasDerivedCategory.standard

open DeRhamCohomologyDirectImage

/-- For `X` smooth and proper over a field `k` of characteristic zero, the dimension of the de
Rham cohomology `H^m_{dR}(X/k)` is the sum over `i ≤ m` of the dimensions of
`H^{m - i}(X, Ω^i_{X/k})`. -/
theorem sum_finrank_eq_finrank_deRham_charZero (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (n : ℕ) [SmoothOfRelativeDimension n f]
    (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), Module.finrank k
        (cohomologyOverField k f (Scheme.Hom.relativeDifferentialForms f (i : ℤ)) (m - i)) =
      Module.finrank k ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule f (m : ℤ))) := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨R, _, φ, Y, h, q', hft, hinj, hpr, hsm, hpb⟩ :=
    exists_isPullback_finiteType_properSmooth k f
  have : IsDomain R := hinj.isDomain φ
  have : CharZero R := ⟨fun a b hab => Nat.cast_injective (R := k) (by
    rw [← map_natCast φ a, ← map_natCast φ b, hab])⟩
  have : Algebra.FinitePresentation ℤ R := Algebra.FinitePresentation.of_finiteType.mp hft
  haveI := smoothOfRelativeDimension_of_isPullback φ hinj hpb n
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let pt : Spec (.of k) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : (Spec.map (CommRingCat.ofHom φ)).base pt = η := by
    refine PrimeSpectrum.ext ?_
    ext x
    change x ∈ Ideal.comap φ ⊥ ↔ x ∈ (⊥ : Ideal R)
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot φ).mp hinj]
  have hspec : ∀ x : PrimeSpectrum R, η ⤳ x := fun x =>
    (PrimeSpectrum.le_iff_specializes η x).mp bot_le
  let βH : ℕ → Spec (.of R) → ℕ := fun i =>
    DerivedFibreBetti.derivedFiberBetti (Spec (.of R)) (hodgeDirectImage h i)
      (isPseudoCoherent_hodgeDirectImage h i) ((m - i : ℕ) : ℤ)
  let βD : Spec (.of R) → ℕ :=
    DerivedFibreBetti.derivedFiberBetti (Spec (.of R)) (derivedDeRhamDirectImageUnbounded h)
      (isPseudoCoherent_derivedDeRhamDirectImageUnbounded h) (m : ℤ)
  have hβH : ∀ i, UpperSemicontinuous (βH i) := fun i =>
    DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti _ _ _ _
  have hβD : UpperSemicontinuous βD :=
    DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti _ _ _ _
  let U : Set (PrimeSpectrum R) := Algebra.smoothLocus ℤ R ∩ {x | βD x ≤ βD η} ∩
    ⋂ i ∈ Finset.range (m + 1), {x | βH i x ≤ βH i η}
  have hUo : IsOpen U :=
    (Algebra.isOpen_smoothLocus.inter (isOpen_setOf_le hβD _)).inter
      (isOpen_biInter_finset fun i _ => isOpen_setOf_le (hβH i) _)
  have hηU : η ∈ U :=
    ⟨⟨mem_smoothLocus_int_bot R, show βD η ≤ βD η from le_rfl⟩,
      Set.mem_iInter₂.mpr fun i _ => show βH i η ≤ βH i η from le_rfl⟩
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
  obtain ⟨s, hsU, hsmax, hsfin, hsN⟩ := exists_isMaximal_finite_lt_ringChar R hUo ⟨η, hηU⟩ n
  set κ := s.asIdeal.ResidueField
  set p := ringChar κ
  have hp : p.Prime := (CharP.char_is_prime_or_zero κ p).resolve_right (by omega)
  have : Fact p.Prime := ⟨hp⟩
  let gs : Spec (.of κ) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R κ))
  have hsq : IsPullback (pullback.fst h gs) (pullback.snd h gs) h gs :=
    IsPullback.of_hasPullback h gs
  let ps : Spec (.of κ) := ⟨⊥, Ideal.isPrime_bot⟩
  have hs : gs.base ps = s := by
    refine PrimeSpectrum.ext ?_
    ext x
    change x ∈ Ideal.comap (algebraMap R κ) ⊥ ↔ x ∈ s.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  obtain ⟨ψ, hψ⟩ := exists_wittTwo_lift R hsU.1.1 p
  let gW : Spec (.of (TruncatedWittVector p 2 κ)) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom ψ)
  let πs : Spec (.of κ) ⟶ Spec (.of (TruncatedWittVector p 2 κ)) :=
    Spec.map (CommRingCat.ofHom (wittTwoToField p κ))
  have hcomp : πs ≫ gW = gs := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  have hW : IsPullback (pullback.fst h gW) (pullback.snd h gW) h gW :=
    IsPullback.of_hasPullback h gW
  have hcond : pullback.fst h gs ≫ h = (pullback.snd h gs ≫ πs) ≫ gW := by
    rw [Category.assoc, hcomp, pullback.condition]
  have hlift : IsPullback (pullback.lift (pullback.fst h gs) (pullback.snd h gs ≫ πs) hcond)
      (pullback.snd h gs) (pullback.snd h gW) πs := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hW
    rw [pullback.lift_fst, hcomp]
    exact hsq
  haveI : SmoothOfRelativeDimension n (pullback.snd h gs) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback hsq inferInstance
  haveI : SmoothOfRelativeDimension n (pullback.snd h gW) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback hW inferInstance
  haveI : IsProper (pullback.snd h gs) :=
    MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  haveI : Finite κ := hsfin
  haveI : CharP κ p := ringChar.charP κ
  have hfib := sum_finrank_eq_finrank_deRham_charP (pullback.snd h gs) n hsN
    (pullback.snd h gW) (wittTwoToField p κ) (fun _ => rfl) _ hlift m
  have hηs : ∀ {β : Spec (.of R) → ℕ}, UpperSemicontinuous β → β s ≤ β η → β s = β η :=
    fun hβ hle => eq_of_le_of_specializes hβ (hspec s) hle
  have hD : βD η = Module.finrank k
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule f (m : ℤ))) := by
    rw [← hη]
    exact derivedFiberBetti_deRhamDirectImage h k hpb m pt
  have hDs : βD s = Module.finrank κ
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of κ)).inv.hom).obj
        (Scheme.Hom.deRhamCohomologyBaseModule (pullback.snd h gs) (m : ℤ))) :=
    (congrArg βD hs).symm.trans (derivedFiberBetti_deRhamDirectImage h κ hsq m ps)
  have hH : ∀ i, βH i η = Module.finrank k
      (cohomologyOverField k f (Scheme.Hom.relativeDifferentialForms f (i : ℤ)) (m - i)) := by
    intro i
    rw [← hη]
    exact derivedFiberBetti_hodgeDirectImage h k hpb i (m - i) pt
  have hHs : ∀ i, βH i s = Module.finrank κ (cohomologyOverField κ (pullback.snd h gs)
      (Scheme.Hom.relativeDifferentialForms (pullback.snd h gs) (i : ℤ)) (m - i)) := by
    intro i
    exact (congrArg (βH i) hs).symm.trans
      (derivedFiberBetti_hodgeDirectImage h κ hsq i (m - i) ps)
  rw [← hD, ← hηs hβD hsU.1.2, hDs, ← hfib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hH, ← hηs (hβH i) (Set.mem_iInter₂.mp hsU.2 i hi), hHs]

end

end CharZeroCount

/-! ### The first Betti number -/

section BettiOne

/-- An integral quasi-compact scheme locally of finite type over a field has finite topological
Krull dimension. -/
theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- For a smooth projective complex variety `X`, `dim H^1_{dR}(X/ℂ)` equals
`dim H^0(X, Ω^1_X) + dim H^1(X, 𝒪_X)`. -/
theorem finrank_deRham_one (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ))
    [IsProjectiveVariety ℂ sX] (hX : MMP.Mori.IsSmoothScheme sX) :
    Module.finrank ℂ ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of ℂ)).inv.hom).obj
            (sX.deRhamCohomologyBaseModule ((1 : ℕ) : ℤ))) =
          Module.finrank ℂ (cohomologyOverField ℂ sX (Scheme.Hom.relativeDifferentials sX) 0) +
            Module.finrank ℂ (cohomologyOverField ℂ sX (SheafOfModules.unit X.ringCatSheaf) 1) := by
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  haveI := MMP.Intersection.smoothOfRelativeDimension_of_isVariety sX n hn
  have h := sum_finrank_eq_finrank_deRham_charZero ℂ sX n 1
  rw [← h, Finset.sum_range_succ, Finset.sum_range_one, add_comm]
  congr 1
  · exact (AlgebraicGeometry.cohomologyOverFieldIso ℂ sX (Scheme.Hom.deRhamAlgebras sX).exteriorPowerOneIso
      0).toLinearEquiv.finrank_eq
  · exact (AlgebraicGeometry.cohomologyOverFieldIso ℂ sX (Scheme.Hom.relativeDifferentialFormsZeroIso sX)
      1).toLinearEquiv.finrank_eq

end BettiOne

/-! ### Global scalars on hypercohomology -/

section GlobalScalars

open Limits TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)

/-- The homology functors of `D(𝒜)` are `R`-linear. -/
theorem derivedCategory_homologyFunctor_linear
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Linear R C] (i : ℤ) :
    Functor.Linear R (DerivedCategory.homologyFunctor C i) := by
  letI : Functor.Linear R (HomologicalComplex.shortComplexFunctor C (.up ℤ) i) :=
    { map_smul := by intros; ext <;> rfl }
  letI : Functor.Linear R (HomologicalComplex.homologyFunctor C (.up ℤ) i) :=
    Functor.linear_of_iso R (HomologicalComplex.homologyFunctorIso C (.up ℤ) i).symm
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.homologyFunctor C (.up ℤ) i)
      (DerivedCategory.homologyFunctor C i) :=
    ⟨DerivedCategory.homologyFunctorFactors C i⟩
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) R
    (HomologicalComplex.homologyFunctor C (.up ℤ) i)
    (DerivedCategory.homologyFunctor C i)).mp inferInstance

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- Multiplication by a global section of the structure sheaf on a module. -/
noncomputable def smulEnd (r : O.obj.obj (op ⊤)) (M : SheafOfModules.{u} (ringSheaf O)) :
    M ⟶ M :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun m => (show (ringSheaf O).obj.obj U from
              O.obj.map (homOfLE le_top).op r) • m
          map_add' := fun m m' => smul_add _ m m'
          map_smul' := fun a m => by
            rw [RingHom.id_apply, smul_smul, smul_smul]
            congr 1
            exact mul_comm ((O.obj.map (homOfLE le_top).op r : O.obj.obj U)) a }
     naturality := fun {U V} f => by
       ext m
       simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
         ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
       refine Eq.trans ?_ (M.val.map_smul f _ m).symm
       change (show (ringSheaf O).obj.obj V from O.obj.map (homOfLE le_top).op r) •
           (M.val.map f m) = ((ringSheaf O).obj.map f (O.obj.map (homOfLE le_top).op r)) •
             M.val.map f m
       congr 1
       change _ = (O.obj.map (homOfLE le_top).op ≫ O.obj.map f) r
       rw [← Functor.map_comp]
       rfl }⟩

/-- On sections over `U`, `smulEnd O r M` is multiplication by the restriction of `r` to `U`. -/
lemma smulEnd_app (r : O.obj.obj (op ⊤)) (M : SheafOfModules.{u} (ringSheaf O))
    (U : (Opens X)ᵒᵖ) (m : M.val.obj U) :
    (smulEnd O r M).val.app U m =
      (show (ringSheaf O).obj.obj U from O.obj.map (homOfLE le_top).op r) • m := rfl

/-- Multiplication by a global section commutes with morphisms of sheaves of modules. -/
lemma smulEnd_naturality (r : O.obj.obj (op ⊤)) {M N : SheafOfModules.{u} (ringSheaf O)}
    (φ : M ⟶ N) : smulEnd O r M ≫ φ = φ ≫ smulEnd O r N := by
  ext U m
  change φ.val.app U ((show (ringSheaf O).obj.obj U from O.obj.map (homOfLE le_top).op r) • m) =
    (show (ringSheaf O).obj.obj U from O.obj.map (homOfLE le_top).op r) • φ.val.app U m
  exact (φ.val.app U).hom.map_smul _ m

/-- Multiplication by a global section on a complex of modules. -/
noncomputable def smulComplex (r : O.obj.obj (op ⊤))
    (K : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) : K ⟶ K where
  f q := smulEnd O r (K.X q)
  comm' q q' _ := smulEnd_naturality O r (K.d q q')

/-- Multiplication by a global section commutes with morphisms of complexes of sheaves of
modules. -/
lemma smulComplex_naturality (r : O.obj.obj (op ⊤))
    {K L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ} (φ : K ⟶ L) :
    smulComplex O r K ≫ φ = φ ≫ smulComplex O r L := by
  ext q : 1
  exact smulEnd_naturality O r (φ.f q)

/-- On the complex of global sections, multiplication by `r` is the scalar `r` times the
identity. -/
lemma sectionsComplex_smulComplex (r : O.obj.obj (op ⊤))
    (K : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) :
    (Stacks.Cech.Linear.sectionsComplexFunctor X (ringSheaf O) ⊤).map (smulComplex O r K) =
      (show SectionRing (ringSheaf O) ⊤ from r) • 𝟙 _ := by
  ext q x
  change (show (ringSheaf O).obj.obj (op ⊤) from O.obj.map (homOfLE le_top).op r) • x =
    (show SectionRing (ringSheaf O) ⊤ from r) • x
  congr 1
  change (O.obj.map (𝟙 _)) r = r
  rw [CategoryTheory.Functor.map_id]
  rfl

section S1

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

/-- **Multiplication by a global section acts on hypercohomology by scalar multiplication.** -/
theorem hypercohomologyMap_smulComplex
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (r : O.obj.obj (op ⊤)) (n : ℤ) :
    Stacks.Cech.Hypercohomology.hypercohomologyMap O
        (ObjectProperty.homMk (smulComplex O r K.obj)) n =
      (show SectionRing (ringSheaf O) ⊤ from r) • 𝟙 _ := by
  obtain ⟨a, ha⟩ := K.2
  haveI := ha
  obtain ⟨G, f, hf, hinj, hGE⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K.obj a
  let I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)) := ⟨G, a, hGE⟩
  let fP : K ⟶ I := ObjectProperty.homMk f
  let D := Stacks.Cech.Linear.derivedSectionsFunctor X (ringSheaf O) ⊤
  have hQf : IsIso (DerivedCategory.Plus.Q.map fP) := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map fP)) := by
      change IsIso (DerivedCategory.Q.map f)
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact hf
    exact isIso_of_fully_faithful DerivedCategory.Plus.ι _
  have hDf : IsIso (D.map fP) := by
    change IsIso (((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).map (DerivedCategory.Plus.Q.map fP))
    infer_instance
  have hu : IsIso (Stacks.Cech.Linear.sectionsToDerived X (ringSheaf O) ⊤ I) :=
    Stacks.Cech.Linear.isIso_sectionsToDerived_of_rightAcyclic X (ringSheaf O) ⊤ I fun m =>
      haveI := hinj m
      Functor.rightAcyclic_of_injective _ _
  set ρ := (show SectionRing (ringSheaf O) ⊤ from r)
  have h1 : D.map (ObjectProperty.homMk (smulComplex O r G) : I ⟶ I) = ρ • 𝟙 _ := by
    have hn := (Stacks.Cech.Linear.sectionsToDerivedNat X (ringSheaf O) ⊤).naturality
      (ObjectProperty.homMk (smulComplex O r G) : I ⟶ I)
    have hS : (Stacks.Cech.Linear.sectionsDerivedFunctor X (ringSheaf O) ⊤).map
        (ObjectProperty.homMk (smulComplex O r G) : I ⟶ I) = ρ • 𝟙 _ := by
      change DerivedCategory.Q.map ((Stacks.Cech.Linear.sectionsComplexFunctor X (ringSheaf O) ⊤).map
        (smulComplex O r G)) = _
      rw [sectionsComplex_smulComplex, Functor.map_smul, CategoryTheory.Functor.map_id]
      rfl
    rw [hS] at hn
    refine (cancel_epi (Stacks.Cech.Linear.sectionsToDerived X (ringSheaf O) ⊤ I)).1 ?_
    refine hn.symm.trans ?_
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Category.comp_id]
    rfl
  have h2 : D.map (ObjectProperty.homMk (smulComplex O r K.obj) : K ⟶ K) = ρ • 𝟙 _ := by
    have hnat : (ObjectProperty.homMk (smulComplex O r K.obj) : K ⟶ K) ≫ fP =
        fP ≫ (ObjectProperty.homMk (smulComplex O r G) : I ⟶ I) := by
      ext : 1
      exact smulComplex_naturality O r f
    have := congrArg D.map hnat
    rw [Functor.map_comp, Functor.map_comp, h1, Linear.comp_smul, Category.comp_id] at this
    rw [← cancel_mono (D.map fP), this, Linear.smul_comp, Category.id_comp]
  haveI := derivedCategory_homologyFunctor_linear (R := SectionRing (ringSheaf O) ⊤)
    (C := ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) n
  change (DerivedCategory.homologyFunctor _ n).map (D.map _) = _
  rw [h2, Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

end S1

end GlobalScalars

/-! ### Closedness of global one-forms -/

section Closedness

open Limits Stacks.Cech.Hypercohomology
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)
open StacksDraft.StupidTruncation HomologicalComplex
open ZeroObject

section Homotopy

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  (L : CochainComplex C ℤ)

/-- The projection of `σ^{≥1}L` onto `L¹[-1]`, followed by the differential `L¹ ⟶ L²`, is
null-homotopic. -/
noncomputable def truncπ_d_homotopy :
    Homotopy (stupidTruncGEπ L 1 ≫ (single C (ComplexShape.up ℤ) 1).map (L.d 1 2)) 0 := by
  let g21 : (L.stupidTrunc (ComplexShape.embeddingUpIntGE 1)).X 2 ⟶
      ((single C (ComplexShape.up ℤ) 1).obj (L.X 2)).X 1 :=
    (stupidTruncGEXIso L 1 2 (by norm_num)).hom ≫
      (singleObjXSelf (ComplexShape.up ℤ) 1 (L.X 2)).inv
  let hom : ∀ i j, (L.stupidTrunc (ComplexShape.embeddingUpIntGE 1)).X i ⟶
      ((single C (ComplexShape.up ℤ) 1).obj (L.X 2)).X j := fun i j =>
    if h : i = 2 ∧ j = 1 then eqToHom (by rw [h.1]) ≫ g21 ≫ eqToHom (by rw [h.2]) else 0
  have hzero : ∀ i j, ¬(ComplexShape.up ℤ).Rel j i → hom i j = 0 := by
    intro i j hij
    have : ¬(i = 2 ∧ j = 1) := by
      rintro ⟨rfl, rfl⟩
      exact hij rfl
    simp only [hom, dif_neg this]
  refine Homotopy.trans (Homotopy.ofEq ?_) (Homotopy.nullHomotopy hom hzero)
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  by_cases hk : k = 1
  · subst hk
    rw [Homotopy.nullHomotopicMap_f (k₂ := 0) (k₀ := 2) (by simp) (by simp)]
    have h10 : hom 1 0 = 0 := by simp [hom]
    have h21 : hom 2 1 = g21 := by simp [hom]
    rw [h10, h21, zero_comp, add_zero, comp_f, stupidTruncGEπ_f, single_map_f_self]
    have hι := (ιStupidTrunc L (ComplexShape.embeddingUpIntGE 1)).comm 1 2
    rw [ιStupidTruncGE_f L 1 1 le_rfl, ιStupidTruncGE_f L 1 2 (by norm_num)] at hι
    simp only [g21, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← reassoc_of% hι]
  · exact (isZero_single_obj_X _ _ _ _ hk).eq_of_tgt _ _

end Homotopy

section Hyp0

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- Global sections are degree-zero hypercohomology, naturally in the module. -/
noncomputable def hyp0NatIso :
    SheafOfModules.toSheaf (ringSheaf O) ⋙ Stacks.Cohomology.Leray.sectionsFunctor X ⊤ ≅
      Stacks.DerivedIndexing.singlePlusFunctor (SheafOfModules.{u} (ringSheaf O)) 0 ⋙
        DerivedCategory.Plus.Q ⋙
        (SheafOfModules.evaluation (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ ((0 : ℕ) : ℤ) ⋙
        forget₂ (ModuleCat.{u} ((ringSheaf O).obj.obj (op ⊤))) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft _ (Stacks.Cohomology.Leray.sectionsFunctor X ⊤).rightDerivedZeroIsoSelf.symm
    ≪≫ rightDerivedToSheafIso O 0

/-- The identification of global sections with degree-zero hypercohomology. -/
noncomputable def hyp0 (F : SheafOfModules.{u} (ringSheaf O)) :
    F.val.obj (op ⊤) ≃+ hypercohomology O (singlePlus O F 0) 0 :=
  ((hyp0NatIso O).app F).addCommGroupIsoToAddEquiv

/-- The identification `hyp0` of global sections with degree-zero hypercohomology is natural. -/
lemma hyp0_naturality {F G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G)
    (s : F.val.obj (op ⊤)) :
    hyp0 O G (f.val.app (op ⊤) s) =
      hypercohomologyMap O (singlePlusMap O f) 0 (hyp0 O F s) := by
  have h1 : (forget₂ (ModuleCat.{u} ((ringSheaf O).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
      (hypercohomologyMap O (singlePlusMap O f) 0) =
      (Stacks.DerivedIndexing.singlePlusFunctor (SheafOfModules.{u} (ringSheaf O)) 0 ⋙
        DerivedCategory.Plus.Q ⋙
        (SheafOfModules.evaluation (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ ((0 : ℕ) : ℤ) ⋙
        forget₂ (ModuleCat.{u} ((ringSheaf O).obj.obj (op ⊤))) AddCommGrpCat.{u}).map f := rfl
  have h2 := (hyp0NatIso O).hom.naturality f
  rw [← h1] at h2
  have h3 := ConcreteCategory.congr_hom h2 s
  have h4 : ∀ x, ((SheafOfModules.toSheaf (ringSheaf O) ⋙
      Stacks.Cohomology.Leray.sectionsFunctor X ⊤).map f) x = f.val.app (op ⊤) x := fun x => rfl
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, h4] at h3
  exact h3

end Hyp0

section Smul

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- Multiplication by `r` on `F`, placed in degree `a`, is multiplication by `r` on the
complex `F[-a]`. -/
lemma singlePlusMapAt_smulEnd (r : O.obj.obj (op ⊤)) (F : SheafOfModules.{u} (ringSheaf O))
    (a : ℤ) :
    singlePlusMapAt O (smulEnd O r F) a =
      ObjectProperty.homMk (smulComplex O r (singlePlus O F a).obj) := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ fun q => ?_)
  by_cases hq : q = a
  · subst hq
    change ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).map (smulEnd O r F)).f q =
      smulEnd O r _
    have h := smulEnd_naturality O r (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q F).hom
    rw [HomologicalComplex.single_map_f_self, ← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq).eq_of_src _ _

/-- Multiplication by `r` on `F` induces on the hypercohomology of `F[-a]` the scalar `r` times
the identity. -/
lemma hypercohomologyMap_singlePlusMapAt_smulEnd (r : O.obj.obj (op ⊤))
    (F : SheafOfModules.{u} (ringSheaf O)) (a n : ℤ) :
    hypercohomologyMap O (singlePlusMapAt O (smulEnd O r F) a) n =
      (show SectionRing (ringSheaf O) ⊤ from r) • 𝟙 _ := by
  rw [singlePlusMapAt_smulEnd]
  exact hypercohomologyMap_smulComplex O (singlePlus O F a) r n

/-- On global sections, `smulEnd O r F` is multiplication by `r`. -/
lemma smulEnd_app_top (r : O.obj.obj (op ⊤)) (F : SheafOfModules.{u} (ringSheaf O))
    (s : F.val.obj (op ⊤)) :
    (smulEnd O r F).val.app (op ⊤) s = (show (ringSheaf O).obj.obj (op ⊤) from r) • s := by
  rw [smulEnd_app]
  congr 1
  change (O.obj.map (𝟙 _)) r = r
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The identification `hyp0` is linear over global sections of the structure sheaf. -/
lemma hyp0_smul (F : SheafOfModules.{u} (ringSheaf O)) (r : O.obj.obj (op ⊤))
    (s : F.val.obj (op ⊤)) :
    hyp0 O F ((show (ringSheaf O).obj.obj (op ⊤) from r) • s) =
      (show SectionRing (ringSheaf O) ⊤ from r) • hyp0 O F s := by
  rw [← smulEnd_app_top, hyp0_naturality, ← singlePlusMapAt_zero,
    hypercohomologyMap_singlePlusMapAt_smulEnd]
  rfl

/-- The map `cechTransfer` along the identity is linear over global sections of the structure
sheaf. -/
lemma cechTransfer_smul (F : SheafOfModules.{u} (ringSheaf O)) (a₁ a₂ : ℤ)
    (h₁ : CechComputes O (singlePlus O F a₁)) (p : ℕ) (r : O.obj.obj (op ⊤))
    (x : hypercohomology O (singlePlus O F a₁) ((p : ℤ) + a₁)) :
    cechTransfer (O₂ := O) (F₂ := F) (𝟙 _) a₁ a₂ h₁ p ((show SectionRing (ringSheaf O) ⊤ from r) • x) =
      (show SectionRing (ringSheaf O) ⊤ from r) • cechTransfer (O₂ := O) (F₂ := F) (𝟙 _) a₁ a₂ h₁ p x := by
  have h := cechTransfer_hypercohomologyMap (𝟙 _) a₁ a₂ (𝟙 _) (smulEnd O r F) (smulEnd O r F)
    (by rw [Category.comp_id, Category.id_comp]) h₁ h₁ p x
  rw [hypercohomologyMap_singlePlusMapAt_smulEnd, hypercohomologyMap_singlePlusMapAt_smulEnd]
    at h
  exact h

end Smul

section LinearAlgebra

/-- In a sequence `U → V → W` of vector spaces exact at `V`, with `U` and `W` finite-dimensional,
`V` is finite-dimensional and `dim V ≤ dim U + dim W`. -/
lemma finrank_le_add_of_exact {k U V W : Type*} [Field k] [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (hfg : ∀ v, g v = 0 → ∃ u, f u = v) [FiniteDimensional k U] [FiniteDimensional k W] :
    FiniteDimensional k V ∧ Module.finrank k V ≤ Module.finrank k U + Module.finrank k W := by
  have hker : LinearMap.ker g ≤ LinearMap.range f := fun v hv => hfg v hv
  haveI : FiniteDimensional k (LinearMap.ker g) := Submodule.finiteDimensional_of_le hker
  haveI : FiniteDimensional k (V ⧸ LinearMap.ker g) :=
    LinearEquiv.finiteDimensional g.quotKerEquivRange.symm
  haveI : FiniteDimensional k V := Module.Finite.of_submodule_quotient (LinearMap.ker g)
  refine ⟨inferInstance, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker g]
  have h1 := Submodule.finrank_mono hker
  have h2 := LinearMap.finrank_range_le f
  have h3 := Submodule.finrank_le (LinearMap.range g)
  omega

end LinearAlgebra

section Injection

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)

/-- The composite `σ^{≥ 1} L ⟶ L^1[-1] ⟶ L^2[-1]` of the projection with the differential
induces zero on hypercohomology. -/
lemma hypercohomologyMap_truncπ_d (n : ℤ) :
    hypercohomologyMap O ((truncSC O L 1).g ≫ singlePlusMapAt O (L.d 1 2) 1) n = 0 := by
  let Z := singlePlus O (0 : SheafOfModules.{u} (ringSheaf O)) 0
  have hZ : IsZero (hypercohomology O Z n) :=
    isZero_hypercohomology_singlePlus_of_isZero O (isZero_zero _) 0 n
  let a : truncPlus O L 1 ⟶ Z := 0
  let b : Z ⟶ singlePlus O (L.X 2) 1 := 0
  have hQ : DerivedCategory.Plus.Q.map ((truncSC O L 1).g ≫ singlePlusMapAt O (L.d 1 2) 1) =
      DerivedCategory.Plus.Q.map (a ≫ b) :=
    ObjectProperty.hom_ext _ ((DerivedCategory.Q_map_eq_of_homotopy
      (h := truncπ_d_homotopy L)).trans (by
        change DerivedCategory.Q.map 0 = DerivedCategory.Q.map ((0 : _ ⟶ Z.obj) ≫ 0)
        rw [Limits.comp_zero]))
  have : hypercohomologyMap O ((truncSC O L 1).g ≫ singlePlusMapAt O (L.d 1 2) 1) n =
      hypercohomologyMap O (a ≫ b) n := by
    change (DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Plus.ι.map
      ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ((truncSC O L 1).g ≫ singlePlusMapAt O (L.d 1 2) 1)))) =
      (DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Plus.ι.map
      ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map (a ≫ b))))
    exact congrArg (fun g => (DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Plus.ι.map
      ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus.map g))) hQ
  rw [this, hypercohomologyMap_comp, show hypercohomologyMap O a n = 0 from hZ.eq_of_tgt _ _,
    Limits.zero_comp]
  rfl

/-- The projection `σ^{≥ 1} L ⟶ L^1[-1]` is injective on `H^1`. -/
lemma injective_hypercohomologyMap_truncSC_one_g :
    Function.Injective (hypercohomologyMap O (truncSC O L 1).g 1) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := hypercohomology_exact₂ O (truncSC O L 1) (truncSC_shortExact O L 1) 1 x hx
  have hz : IsZero (hypercohomology O (truncSC O L 1).X₁ 1) :=
    Stacks.Cech.Hypercohomology.isZero_hypercohomology O (truncPlus O L (1 + 1)) (1 + 1) 1 (by norm_num)
  rw [show a = 0 from (ModuleCat.isZero_iff_subsingleton.mp hz).elim a 0, map_zero]

variable (h1 : CechComputesSheaf O (L.X 1)) (h2 : CechComputesSheaf O (L.X 2))

/-- The map `H¹(σ^{≥1}L) ⟶ Γ(L¹)`. -/
noncomputable def hypOneToSections (x : hypercohomology O (truncPlus O L 1) 1) :
    (L.X 1).val.obj (op ⊤) :=
  (hyp0 O (L.X 1)).symm
    (cechTransfer (O₂ := O) (F₂ := L.X 1) (𝟙 _) 1 0 ((h1.singlePlus _ 1)) 0 (hypercohomologyMap O (truncSC O L 1).g 1 x))

/-- The map `H¹(σ^{≥1}L) ⟶ Γ(L¹)` is injective. -/
lemma hypOneToSections_injective : Function.Injective (hypOneToSections O L h1) := by
  intro x y hxy
  apply injective_hypercohomologyMap_truncSC_one_g O L
  have h := (hyp0 O (L.X 1)).symm.injective hxy
  exact (cechTransferEquiv (O₂ := O) (F₂ := L.X 1) 1 0 (Iso.refl _) ((h1.singlePlus _ 1)) ((h1.singlePlus _ 0)) 0).injective h

/-- The image of `H¹(σ^{≥1}L) ⟶ Γ(L¹)` lies in the kernel of the differential
`Γ(L¹) ⟶ Γ(L²)`. -/
lemma d_hypOneToSections (h2 : CechComputesSheaf O (L.X 2))
    (x : hypercohomology O (truncPlus O L 1) 1) :
    (L.d 1 2).val.app (op ⊤) (hypOneToSections O L h1 x) = 0 := by
  apply (hyp0 O (L.X 2)).injective
  rw [map_zero, hyp0_naturality, ← singlePlusMapAt_zero]
  unfold hypOneToSections
  rw [AddEquiv.apply_symm_apply]
  have h := cechTransfer_hypercohomologyMap (O₂ := O) (F₂ := L.X 1) (G₂ := L.X 2) (𝟙 _) 1 0
    (𝟙 _) (L.d 1 2) (L.d 1 2)
    (by rw [Category.comp_id, Category.id_comp]) ((h1.singlePlus _ 1)) ((h2.singlePlus _ 1)) 0
    (hypercohomologyMap O (truncSC O L 1).g 1 x)
  refine h.symm.trans ?_
  have h0 := (hypercohomologyMap_comp O _ _ 1).symm.trans (hypercohomologyMap_truncπ_d O L 1)
  change cechTransfer (O₂ := O) (F₂ := L.X 2) (𝟙 _) 1 0 ((h2.singlePlus _ 1)) 0
    ((hypercohomologyMap O (truncSC O L 1).g 1 ≫ hypercohomologyMap O
      (singlePlusMapAt O (L.d 1 2) 1) 1) x) = 0
  erw [h0]
  exact map_zero _

/-- The map `H¹(σ^{≥1}L) ⟶ Γ(L¹)` is linear over global sections of the structure sheaf. -/
lemma hypOneToSections_smul (r : O.obj.obj (op ⊤)) (x : hypercohomology O (truncPlus O L 1) 1) :
    hypOneToSections O L h1 ((show SectionRing (ringSheaf O) ⊤ from r) • x) =
      (show (ringSheaf O).obj.obj (op ⊤) from r) • hypOneToSections O L h1 x := by
  apply (hyp0 O (L.X 1)).injective
  rw [hyp0_smul]
  unfold hypOneToSections
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have := (hypercohomologyMap O (truncSC O L 1).g 1).hom.map_smul
    (show SectionRing (ringSheaf O) ⊤ from r) x
  erw [this]
  exact cechTransfer_smul O (L.X 1) 1 0 ((h1.singlePlus _ 1)) 0 r _

end Injection

section Dimension

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) [hL : L.IsStrictlyGE 0]
  (h1 : CechComputesSheaf O (L.X 1)) (h2 : CechComputesSheaf O (L.X 2))
  (k : Type u) [Field k] (ψ : k →+* SectionRing (ringSheaf O) ⊤)

/-- `hypOneToSections` as a `k`-linear map. -/
noncomputable def hypOneToSectionsₗ :
    (ModuleCat.restrictScalars ψ).obj (hypercohomology O (truncPlus O L 1) 1) →ₗ[k]
      (ModuleCat.restrictScalars ψ).obj ((L.X 1).val.obj (op ⊤)) where
  toFun := hypOneToSections O L h1
  map_add' x y := by
    unfold hypOneToSections
    erw [(hypercohomologyMap O (truncSC O L 1).g 1).hom.map_add x y, map_add, map_add]
    rfl
  map_smul' c x := hypOneToSections_smul O L h1 (ψ c) x

include h1 h2 in
/-- For a complex `L` concentrated in nonnegative degrees, `dim H^1(L)` is at most the dimension
of the kernel of `Γ(L¹) ⟶ Γ(L²)` plus `dim H^1(L^0)`. -/
theorem finrank_hypercohomology_one_le
    [FiniteDimensional k ((ModuleCat.restrictScalars ψ).obj
      (hypercohomology O (singlePlus O (L.X 0) 0) 1))]
    [FiniteDimensional k ((ModuleCat.restrictScalars ψ).obj ((L.X 1).val.obj (op ⊤)))] :
    Module.finrank k ((ModuleCat.restrictScalars ψ).obj (hypercohomology O ⟨L, 0, hL⟩ 1)) ≤
      Module.finrank k (LinearMap.ker
        ((ModuleCat.restrictScalars ψ).map ((L.d 1 2).val.app (op ⊤))).hom) +
      Module.finrank k ((ModuleCat.restrictScalars ψ).obj
        (hypercohomology O (singlePlus O (L.X 0) 0) 1)) := by
  set J := hypOneToSectionsₗ O L h1 k ψ
  have hJ : Function.Injective J := hypOneToSections_injective O L h1
  let D := ((ModuleCat.restrictScalars ψ).map ((L.d 1 2).val.app (op ⊤))).hom
  have hJD : LinearMap.range J ≤ LinearMap.ker D := by
    rintro _ ⟨x, rfl⟩
    exact d_hypOneToSections O L h1 h2 x
  let Jr : _ →ₗ[k] LinearMap.ker D := J.codRestrict (LinearMap.ker D) (fun x => hJD ⟨x, rfl⟩)
  have hJr : Function.Injective Jr := fun x y h => hJ (congrArg Subtype.val h)
  haveI : FiniteDimensional k ((ModuleCat.restrictScalars ψ).obj
      (hypercohomology O (truncSC O L 0).X₁ 1)) := Module.Finite.of_injective J hJ
  let e := truncPlusIso O ⟨L, 0, hL⟩ 0
  let f := ((ModuleCat.restrictScalars ψ).map
    (hypercohomologyMap O (truncSC O L 0).f 1 ≫ hypercohomologyMap O e.hom 1)).hom
  let g := ((ModuleCat.restrictScalars ψ).map
    (hypercohomologyMap O e.inv 1 ≫ hypercohomologyMap O (truncSC O L 0).g 1)).hom
  have hfg : ∀ v, g v = 0 → ∃ u, f u = v := by
    intro v hv
    obtain ⟨a, ha⟩ := hypercohomology_exact₂ O (truncSC O L 0) (truncSC_shortExact O L 0) 1
      (hypercohomologyMap O e.inv 1 v) hv
    refine ⟨a, ?_⟩
    change hypercohomologyMap O e.hom 1 (hypercohomologyMap O (truncSC O L 0).f 1 a) = v
    rw [ha]
    change (hypercohomologyMap O e.inv 1 ≫ hypercohomologyMap O e.hom 1) v = v
    rw [← hypercohomologyMap_comp, e.inv_hom_id, hypercohomologyMap_id]
    rfl
  haveI : FiniteDimensional k ((ModuleCat.restrictScalars ψ).obj
      (hypercohomology O (truncSC O L 0).X₃ 1)) :=
    ‹FiniteDimensional k ((ModuleCat.restrictScalars ψ).obj
      (hypercohomology O (singlePlus O (L.X 0) 0) 1))›
  obtain ⟨-, hle⟩ := finrank_le_add_of_exact f g hfg
  have hW : Module.finrank k ((ModuleCat.restrictScalars ψ).obj
      (hypercohomology O (truncSC O L 0).X₃ 1)) = Module.finrank k
      ((ModuleCat.restrictScalars ψ).obj (hypercohomology O (singlePlus O (L.X 0) 0) 1)) := rfl
  have hU : Module.finrank k ((ModuleCat.restrictScalars ψ).obj
      (hypercohomology O (truncSC O L 0).X₁ 1)) ≤ Module.finrank k (LinearMap.ker D) :=
    LinearMap.finrank_le_finrank_of_injective (f := Jr) hJr
  have hD : Module.finrank k (LinearMap.ker D) = Module.finrank k (LinearMap.ker
      ((ModuleCat.restrictScalars ψ).map ((L.d 1 2).val.app (op ⊤))).hom) := rfl
  omega

end Dimension

section Comparison

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
attribute [local implicit_reducible] TopCat.Sheaf

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The inverse image of the structure sheaf of the base. -/
noncomputable abbrev baseSheaf : Sheaf (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj (Spec (.of k)).sheaf

/-- The structure map from the inverse image of the base. -/
noncomputable abbrev baseHom := SheafOfModules.underlyingRingHom
  (φ := AlgebraicGeometry.inverseImageStructureMap f)

/-- Multiplication by a section `t` of the base sheaf on the restriction of scalars of `F` is,
as a morphism of underlying sheaves, multiplication by the image of `t` on `F`. -/
lemma toSheaf_smulEnd_restrictScalars (t : (baseSheaf f).obj.obj (op ⊤)) (F : X.Modules) :
    (_root_.SheafOfModules.toSheaf (ringSheaf (baseSheaf f))).map
        (smulEnd (baseSheaf f) t ((_root_.SheafOfModules.restrictScalars (baseHom f)).obj F)) =
      (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
        (Stacks.Perfect.FractionClass.smulHom ((baseHom f).hom.app (op ⊤) t) F) := by
  ext U x
  have h := ConcreteCategory.congr_hom ((baseHom f).hom.naturality (homOfLE (le_top : U.unop ≤ ⊤)).op) t
  change (show X.ringCatSheaf.obj.obj U from
      (baseHom f).hom.app U ((baseSheaf f).obj.map (homOfLE le_top).op t)) •
      (show F.val.obj U from x) =
    Stacks.Perfect.FractionClass.resTop ((baseHom f).hom.app (op ⊤) t) U •
      (show F.val.obj U from x)
  congr 1

/-- The scalars of de Rham cohomology over the base field. -/
noncomputable abbrev baseScalars : k →+* SectionRing (ringSheaf (baseSheaf f)) ⊤ :=
  (Scheme.Hom.inverseImageGlobalSections f).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The image in `Γ(X, 𝒪_X)` of a scalar `c : k` is its image under `f` on global sections. -/
lemma baseHom_baseScalars (c : k) :
    (baseHom f).hom.app (op ⊤) (baseScalars f c) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c := by
  have h := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (Scheme.Hom.inverseImageGlobalSections_comp_inverseImageStructureMap_app f)
  refine h.trans ?_
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  erw [X.presheaf.map_id]
  rfl

/-- The hypercohomology of `F`, viewed over the base sheaf and placed in degree zero, is
`k`-linearly isomorphic to the sheaf cohomology `H^n(X, F)` over `k`. -/
theorem nonempty_linearEquiv_hypercohomology_restrictScalars (F : X.Modules) (n : ℕ) :
    Nonempty ((ModuleCat.restrictScalars (baseScalars f)).obj (hypercohomology (baseSheaf f)
      (singlePlus (baseSheaf f) ((_root_.SheafOfModules.restrictScalars (baseHom f)).obj F) 0) n)
        ≃ₗ[k] cohomologyOverField k f F n) := by
  obtain ⟨E, -⟩ := (MMP.Analytic.sheafCohomology_toolkit.{u, 0, 0, 0, 0} X.toTopCat).2.2.1.1
  obtain ⟨e, he⟩ := MMP.Analytic.exists_addEquiv_sheafCohomology_cohomologyOverField f F n
  let I : (forget₂ (ModuleCat.{u} ((ringSheaf (baseSheaf f)).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
      (hypercohomology (baseSheaf f) (singlePlus (baseSheaf f)
        ((_root_.SheafOfModules.restrictScalars (baseHom f)).obj F) 0) n) ≅
      (MMP.Analytic.sheafCohomology X.toTopCat n).obj
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj F) :=
    ((rightDerivedToSheafIso (baseSheaf f) n).app
        ((_root_.SheafOfModules.restrictScalars (baseHom f)).obj F)).symm ≪≫
      ((E X.toTopCat n).app ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj F)).symm
  have key : ∀ g : (_root_.SheafOfModules.restrictScalars (baseHom f)).obj F ⟶
      (_root_.SheafOfModules.restrictScalars (baseHom f)).obj F,
      (forget₂ (ModuleCat.{u} ((ringSheaf (baseSheaf f)).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
        (hypercohomologyMap (baseSheaf f) (singlePlusMap (baseSheaf f) g) n) ≫ I.hom =
        I.hom ≫ (MMP.Analytic.sheafCohomology X.toTopCat n).map
          ((_root_.SheafOfModules.toSheaf (ringSheaf (baseSheaf f))).map g) := by
    intro g
    have n1 : (forget₂ (ModuleCat.{u} ((ringSheaf (baseSheaf f)).obj.obj (op ⊤)))
        AddCommGrpCat.{u}).map (hypercohomologyMap (baseSheaf f) (singlePlusMap (baseSheaf f) g) n) ≫
          (rightDerivedToSheafIso (baseSheaf f) n).inv.app _ =
        (rightDerivedToSheafIso (baseSheaf f) n).inv.app _ ≫
          ((Stacks.Cohomology.Leray.sectionsFunctor X.toTopCat ⊤).rightDerived n).map
            ((_root_.SheafOfModules.toSheaf (ringSheaf (baseSheaf f))).map g) :=
      (rightDerivedToSheafIso (baseSheaf f) n).inv.naturality g
    have n2 := (E X.toTopCat n).inv.naturality
      ((_root_.SheafOfModules.toSheaf (ringSheaf (baseSheaf f))).map g)
    change _ ≫ (rightDerivedToSheafIso (baseSheaf f) n).inv.app _ ≫ (E X.toTopCat n).inv.app _ =
      ((rightDerivedToSheafIso (baseSheaf f) n).inv.app _ ≫ (E X.toTopCat n).inv.app _) ≫ _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (E X.toTopCat n).inv.app _) n1).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) n2).trans (Category.assoc _ _ _).symm)))
  refine ⟨{ I.addCommGroupIsoToAddEquiv.trans e with map_smul' := fun c x => ?_ }⟩
  have hs := ConcreteCategory.congr_hom (hypercohomologyMap_singlePlusMapAt_smulEnd (baseSheaf f)
    (baseScalars f c) ((_root_.SheafOfModules.restrictScalars (baseHom f)).obj F) 0 n) x
  have h2 := ConcreteCategory.congr_hom (key (smulEnd (baseSheaf f) (baseScalars f c)
    ((_root_.SheafOfModules.restrictScalars (baseHom f)).obj F))) x
  have hg : (_root_.SheafOfModules.toSheaf (ringSheaf (baseSheaf f))).map
      (smulEnd (baseSheaf f) (baseScalars f c)
        ((_root_.SheafOfModules.restrictScalars (baseHom f)).obj F)) =
      (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map (Stacks.Perfect.FractionClass.smulHom
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c) F) :=
    (toSheaf_smulEnd_restrictScalars f _ F).trans (by rw [baseHom_baseScalars])
  rw [hg] at h2
  have h3 := he c (I.hom x)
  change e (I.hom _) = c • e (I.hom x)
  refine Eq.trans (congrArg e ?_) h3
  refine Eq.trans (congrArg (ConcreteCategory.hom I.hom) ?_) h2
  change _ = (ConcreteCategory.hom (hypercohomologyMap (baseSheaf f)
    (singlePlusMapAt (baseSheaf f) (smulEnd (baseSheaf f) ((baseScalars f) c)
      ((_root_.SheafOfModules.restrictScalars (baseHom f)).obj F)) 0) n)) x
  rw [hs]
  rfl

end Comparison

section Closed

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
attribute [local implicit_reducible] TopCat.Sheaf

/-- `hyp0` as a linear equivalence over a field of scalars. -/
noncomputable def hyp0ₗ {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    {k : Type u} [Field k] (ψ : k →+* SectionRing (ringSheaf O) ⊤)
    (F : SheafOfModules.{u} (ringSheaf O)) :
    (ModuleCat.restrictScalars ψ).obj (F.val.obj (op ⊤)) ≃ₗ[k]
      (ModuleCat.restrictScalars ψ).obj (hypercohomology O (singlePlus O F 0) 0) :=
  { hyp0 O F with map_smul' := fun c s => hyp0_smul O F (ψ c) s }

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- If `M` is isomorphic to the restriction of scalars of `F`, the global sections of `M` are
`k`-linearly isomorphic to `H^0(X, F)` over `k`. -/
theorem nonempty_linearEquiv_sections_cohomologyOverField
    (M : SheafOfModules.{u} (ringSheaf (baseSheaf f))) (F : X.Modules)
    (φ : M ≅ (_root_.SheafOfModules.restrictScalars (baseHom f)).obj F) :
    Nonempty ((ModuleCat.restrictScalars (baseScalars f)).obj (M.val.obj (op ⊤)) ≃ₗ[k]
      cohomologyOverField k f F 0) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_hypercohomology_restrictScalars f F 0
  exact ⟨(((ModuleCat.restrictScalars (baseScalars f)).mapIso
    ((SheafOfModules.evaluation (ringSheaf (baseSheaf f)) (op ⊤)).mapIso φ)).toLinearEquiv.trans
      (hyp0ₗ (baseSheaf f) (baseScalars f)
        ((_root_.SheafOfModules.restrictScalars (baseHom f)).obj F))).trans e⟩

/-- If `M` is isomorphic to the restriction of scalars of `F`, the hypercohomology of `M` placed
in degree zero is `k`-linearly isomorphic to `H^n(X, F)` over `k`. -/
theorem nonempty_linearEquiv_hypercohomology_cohomologyOverField
    (M : SheafOfModules.{u} (ringSheaf (baseSheaf f))) (F : X.Modules)
    (φ : M ≅ (_root_.SheafOfModules.restrictScalars (baseHom f)).obj F) (n : ℕ) :
    Nonempty ((ModuleCat.restrictScalars (baseScalars f)).obj
      (hypercohomology (baseSheaf f) (singlePlus (baseSheaf f) M 0) n) ≃ₗ[k]
      cohomologyOverField k f F n) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_hypercohomology_restrictScalars f F n
  exact ⟨((ModuleCat.restrictScalars (baseScalars f)).mapIso
    (hypercohomologyMapIso (baseSheaf f) (ObjectProperty.isoMk _
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso φ)) n)).toLinearEquiv.trans e⟩

/-- On a smooth projective complex variety, every global `1`-form is closed. -/
theorem deRhamComplex_d_one_eq_zero (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ))
    [IsProjectiveVariety ℂ sX] (hX : MMP.Mori.IsSmoothScheme sX)
    (ω : ((sX.deRhamComplex).X 1).val.obj (op ⊤)) :
    ((sX.deRhamComplex).d 1 2).val.app (op ⊤) ω = 0 := by
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  haveI := MMP.Intersection.smoothOfRelativeDimension_of_isVariety sX n hn
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X)) := by
    have : IsSeparated (Limits.terminal.from X) := by
      have e : Limits.terminal.from X = sX ≫ Limits.terminal.from (Spec (.of ℂ)) :=
        Subsingleton.elim _ _
      rw [e]; infer_instance
    infer_instance
  let B := Scheme.Hom.deRhamAlgebras sX
  let K := sX.deRhamComplex
  let L := SheafOfModules.deRhamComplexInt B (SheafOfModules.deRhamDifferential B)
  have h1 := Scheme.Hom.cechComputesSheaf_deRhamComplexInt_X sX 1
  have h2 := Scheme.Hom.cechComputesSheaf_deRhamComplexInt_X sX 2
  have eX : ∀ p : ℕ, L.X p ≅ (_root_.SheafOfModules.restrictScalars (baseHom sX)).obj
      (Scheme.Hom.relativeDifferentialForms sX (p : ℤ)) := fun p =>
    K.extendXIso ComplexShape.embeddingUpNat rfl ≪≫ eqToIso (Scheme.Hom.deRhamComplex_X sX p)
  obtain ⟨eW⟩ := nonempty_linearEquiv_hypercohomology_cohomologyOverField sX (L.X 0) _ (eX 0) 1
  obtain ⟨eΓ⟩ := nonempty_linearEquiv_sections_cohomologyOverField sX (L.X 1) _ (eX 1)
  have hcoh : ∀ a : ℕ, (Scheme.Hom.relativeDifferentialForms sX (a : ℤ)).IsCoherent := fun a => by
    haveI := isFiniteLocallyFree_exteriorPower sX n a
    exact Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials sX) a)
  haveI := hcoh 0
  haveI := hcoh 1
  haveI := finiteDimensional_cohomologyOverField_of_isProper ℂ sX
    (Scheme.Hom.relativeDifferentialForms sX ((0 : ℕ) : ℤ)) 1
  haveI := finiteDimensional_cohomologyOverField_of_isProper ℂ sX
    (Scheme.Hom.relativeDifferentialForms sX ((1 : ℕ) : ℤ)) 0
  haveI : FiniteDimensional ℂ ((ModuleCat.restrictScalars (baseScalars sX)).obj
      (hypercohomology (baseSheaf sX) (singlePlus (baseSheaf sX) (L.X 0) 0) 1)) :=
    LinearEquiv.finiteDimensional eW.symm
  haveI : FiniteDimensional ℂ ((ModuleCat.restrictScalars (baseScalars sX)).obj
      ((L.X 1).val.obj (op ⊤))) := LinearEquiv.finiteDimensional eΓ.symm
  haveI hL : L.IsStrictlyGE 0 := SheafOfModules.isStrictlyGE_deRhamComplexInt B _
  have hineq := finrank_hypercohomology_one_le (baseSheaf sX) L (hL := hL) h1 h2 ℂ (baseScalars sX)
  have hV : Module.finrank ℂ ((ModuleCat.restrictScalars (baseScalars sX)).obj
      (hypercohomology (baseSheaf sX) ⟨L, 0, hL⟩ 1)) =
      Module.finrank ℂ ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of ℂ)).inv.hom).obj
        (sX.deRhamCohomologyBaseModule ((1 : ℕ) : ℤ))) :=
    ((ModuleCat.restrictScalars (baseScalars sX)).mapIso
      (SheafOfModules.hypercohomologyIsoDeRhamCohomology B
        (SheafOfModules.deRhamDifferential B) 1)).toLinearEquiv.finrank_eq
  have h10 := finrank_deRham_one X sX hX
  have hW := eW.finrank_eq
  have hW' := (AlgebraicGeometry.cohomologyOverFieldIso ℂ sX (Scheme.Hom.relativeDifferentialFormsZeroIso sX)
    1).toLinearEquiv.finrank_eq
  have hΓ := eΓ.finrank_eq
  have hΓ' := (AlgebraicGeometry.cohomologyOverFieldIso ℂ sX (Scheme.Hom.deRhamAlgebras sX).exteriorPowerOneIso
    0).toLinearEquiv.finrank_eq
  have hW1 : Module.finrank ℂ ((ModuleCat.restrictScalars (baseScalars sX)).obj
      (hypercohomology (baseSheaf sX) (singlePlus (baseSheaf sX) (L.X 0) 0) 1)) =
    Module.finrank ℂ ((ModuleCat.restrictScalars (baseScalars sX)).obj
      (hypercohomology (baseSheaf sX) (singlePlus (baseSheaf sX) (L.X 0) 0) ((1 : ℕ) : ℤ))) := rfl
  have hb : Module.finrank ℂ (cohomologyOverField ℂ sX
      (Scheme.Hom.relativeDifferentialForms sX ((0 : ℕ) : ℤ)) 1) =
      Module.finrank ℂ (cohomologyOverField ℂ sX (Scheme.Hom.relativeDifferentialForms sX 0) 1) :=
    rfl
  have he : Module.finrank ℂ (cohomologyOverField ℂ sX
      (Scheme.Hom.relativeDifferentialForms sX ((1 : ℕ) : ℤ)) 0) =
      Module.finrank ℂ (cohomologyOverField ℂ sX
        ((Scheme.Hom.deRhamAlgebras sX).exteriorPower 1) 0) := rfl
  have hle := Submodule.finrank_le (LinearMap.ker
    ((ModuleCat.restrictScalars (baseScalars sX)).map ((L.d 1 2).val.app (op ⊤))).hom)
  have hker : LinearMap.ker
      ((ModuleCat.restrictScalars (baseScalars sX)).map ((L.d 1 2).val.app (op ⊤))).hom = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  let e1 := K.extendXIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f 1 = 1)
  let e2 := K.extendXIso ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f 2 = 2)
  have hd : L.d 1 2 = e1.hom ≫ K.d 1 2 ≫ e2.inv := HomologicalComplex.extend_d_eq _ _ rfl rfl
  have h0 : (L.d 1 2).val.app (op ⊤) (e1.inv.val.app (op ⊤) ω) = 0 := by
    have hm : (show ((ModuleCat.restrictScalars (baseScalars sX)).obj ((L.X 1).val.obj (op ⊤)))
        from e1.inv.val.app (op ⊤) ω) ∈ LinearMap.ker
        ((ModuleCat.restrictScalars (baseScalars sX)).map ((L.d 1 2).val.app (op ⊤))).hom := by
      rw [hker]; exact Submodule.mem_top
    exact hm
  have hK : K.d 1 2 = e1.inv ≫ L.d 1 2 ≫ e2.hom := by
    have : K.d 1 2 = e1.inv ≫ (e1.hom ≫ K.d 1 2 ≫ e2.inv) ≫ e2.hom := by simp
    exact this.trans (congrArg (fun g => e1.inv ≫ g ≫ e2.hom) hd.symm)
  have key : (K.d 1 2).val.app (op ⊤) ω =
      e2.hom.val.app (op ⊤) ((L.d 1 2).val.app (op ⊤) (e1.inv.val.app (op ⊤) ω)) := by
    rw [hK]; rfl
  exact key.trans ((congrArg (e2.hom.val.app (op ⊤)) h0).trans (map_zero _))

end Closed

end Closedness

/-! ### The holomorphic Poincaré lemma -/

section HolomorphicPoincare

open Set Filter ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology

/-- Removing entry `i.succ` from `Fin.cons x v` gives `Fin.cons x` of `v` with entry `i`
removed. -/
theorem removeNth_succ_cons {α : Type*} {n : ℕ} (x : α) (v : Fin (n+1) → α)
    (i : Fin (n+1)) :
    Fin.removeNth i.succ (Fin.cons x v : Fin (n+2) → α) = Fin.cons x (Fin.removeNth i v) := by
  ext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp [Fin.removeNth, Fin.succ_succAbove_zero]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

/-- Contracting `alternatizeUncurryFin L` with `x` in the first slot, plus the alternatization of
`L` contracted with `x` in the first slot of each value, gives `L x`. -/
theorem curryLeft_alternatizeUncurryFin_add {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ}
    (L : E →L[𝕜] E [⋀^Fin (k + 1)]→L[𝕜] F) (x : E) :
    (alternatizeUncurryFin L).curryLeft x +
      alternatizeUncurryFin
        (((curryLeftLI (𝕜 := 𝕜) (E := E) (F := F) (n := k)).toContinuousLinearMap.comp L).flip x) =
      L x := by
  ext v
  rw [ContinuousAlternatingMap.add_apply, curryLeft_apply_apply,
    alternatizeUncurryFin_apply, alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  have h : ∀ i : Fin (k + 1), Fin.removeNth i.succ (Matrix.vecCons x v) =
      Matrix.vecCons x (Fin.removeNth i v) := fun i ↦ removeNth_succ_cons x v i
  simp only [h, Fin.removeNth_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero,
    pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul]
  simp [Matrix.tail_cons, curryLeft_apply_apply]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The radial homotopy operator on holomorphic forms. -/
@[expose] public noncomputable def radialHomotopy (k : ℕ) (β : E → E [⋀^Fin (k + 1)]→L[ℂ] F)
    (x : E) :
    E [⋀^Fin k]→L[ℂ] F :=
  ∫ t in (0 : ℝ)..1, ((t : ℂ) ^ k) • (β ((t : ℂ) • x)).curryLeft x

/-- The Fréchet derivative at `x` of `y ↦ t ^ k • (β (t • y)).curryLeft y`, for `β`
differentiable at `t • x`. -/
theorem hasFDerivAt_radialIntegrand {k : ℕ} {β : E → E [⋀^Fin (k + 1)]→L[ℂ] F}
    (x : E) (t : ℂ) (hβ : DifferentiableAt ℂ β (t • x)) :
    HasFDerivAt (fun y ↦ t ^ k • (β (t • y)).curryLeft y)
      (t ^ k • ((β (t • x)).curryLeft + t •
        ((curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).toContinuousLinearMap.comp
          (fderiv ℂ β (t • x))).flip x)) x := by
  have hc : HasFDerivAt (fun y ↦
      (curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).toContinuousLinearMap (β (t • y)))
      ((curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).toContinuousLinearMap.comp
        ((fderiv ℂ β (t • x)).comp (t • ContinuousLinearMap.id ℂ E))) x := by
    refine (curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).toContinuousLinearMap.hasFDerivAt.comp
        x ?_
    exact hβ.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
  have h := (hc.clm_apply (hasFDerivAt_id x)).const_smul (t ^ k)
  have h' : HasFDerivAt (fun y ↦ t ^ k • (β (t • y)).curryLeft y) _ x := h
  refine h'.congr_fderiv ?_
  congr 1
  ext w v
  simp [curryLeft_apply_apply, add_comm]

/-- The derivative of the radial integrand. -/
@[expose] public noncomputable def radialDeriv (k : ℕ) (β : E → E [⋀^Fin (k + 1)]→L[ℂ] F) (x : E)
    (t : ℝ) :
    E →L[ℂ] E [⋀^Fin k]→L[ℂ] F :=
  ((t : ℂ) ^ k) • ((β ((t : ℂ) • x)).curryLeft + (t : ℂ) •
    ((curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).toContinuousLinearMap.comp
      (fderiv ℂ β ((t : ℂ) • x))).flip x)

/-- For `t ∈ [0, 1]`, the closed ball about `0` of radius `R` is stable under scaling by `t`. -/
lemma norm_smul_mem_closedBall {x : E} {R : ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ closedBall (0 : E) R) : (t : ℂ) • x ∈ closedBall (0 : E) R := by
  rw [mem_closedBall_zero_iff] at hx ⊢
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc t * ‖x‖ ≤ 1 * ‖x‖ := by gcongr; exact ht.2
    _ = ‖x‖ := one_mul _
    _ ≤ R := hx

/-- For `β` of class `C¹` on the ball of radius `r > R`, the radial derivative is jointly
continuous on `closedBall 0 R × [0, 1]`. -/
theorem continuousOn_radialDeriv [FiniteDimensional ℂ E] {k : ℕ}
    {β : E → E [⋀^Fin (k + 1)]→L[ℂ] F} {r R : ℝ} (hRr : R < r)
    (hcd : ContDiffOn ℂ 1 β (ball 0 r)) :
    ContinuousOn (fun p : E × ℝ ↦ radialDeriv k β p.1 p.2)
      (closedBall (0 : E) R ×ˢ Icc (0 : ℝ) 1) := by
  have hβc : ContinuousOn β (closedBall 0 R) :=
    hcd.continuousOn.mono (closedBall_subset_ball hRr)
  have hβ'c : ContinuousOn (fderiv ℂ β) (closedBall 0 R) :=
    (hcd.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono (closedBall_subset_ball hRr)
  have hm : MapsTo (fun p : E × ℝ ↦ (p.2 : ℂ) • p.1) (closedBall (0 : E) R ×ˢ Icc (0 : ℝ) 1)
      (closedBall 0 R) := fun p hp ↦ norm_smul_mem_closedBall hp.2 hp.1
  have hsm : Continuous (fun p : E × ℝ ↦ (p.2 : ℂ) • p.1) :=
    (Complex.continuous_ofReal.comp continuous_snd).smul continuous_fst
  have h1 : ContinuousOn (fun p : E × ℝ ↦ β ((p.2 : ℂ) • p.1))
      (closedBall (0 : E) R ×ˢ Icc (0 : ℝ) 1) := hβc.comp hsm.continuousOn hm
  have h2 : ContinuousOn (fun p : E × ℝ ↦ fderiv ℂ β ((p.2 : ℂ) • p.1))
      (closedBall (0 : E) R ×ˢ Icc (0 : ℝ) 1) := hβ'c.comp hsm.continuousOn hm
  have hpow : Continuous (fun p : E × ℝ ↦ ((p.2 : ℂ) ^ k)) :=
    (Complex.continuous_ofReal.comp continuous_snd).pow k
  have hsc : Continuous (fun p : E × ℝ ↦ (p.2 : ℂ)) := Complex.continuous_ofReal.comp continuous_snd
  refine hpow.continuousOn.smul (ContinuousOn.add ?_ (hsc.continuousOn.smul ?_))
  · exact (curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).continuous.comp_continuousOn h1
  · have h3 : ContinuousOn (fun p : E × ℝ ↦
        ((curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).toContinuousLinearMap.comp
          (fderiv ℂ β ((p.2 : ℂ) • p.1))).flip) (closedBall (0 : E) R ×ˢ Icc (0 : ℝ) 1) :=
      (ContinuousLinearMap.flipₗᵢ ℂ E E (E [⋀^Fin k]→L[ℂ] F)).continuous.comp_continuousOn
        ((((ContinuousLinearMap.compL ℂ E _ _)
          (curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).toContinuousLinearMap)).continuous.comp_continuousOn h2)
    exact h3.clm_apply continuous_fst.continuousOn

/-- For `β` continuous on `closedBall 0 R` and `x` in that ball, the radial integrand
`t ↦ t ^ k • (β (t • x)).curryLeft x` is continuous on `[0, 1]`. -/
theorem continuousOn_radialIntegrand {k : ℕ}
    {β : E → E [⋀^Fin (k + 1)]→L[ℂ] F} {R : ℝ} (hβc : ContinuousOn β (closedBall 0 R))
    {x : E} (hx : x ∈ closedBall (0 : E) R) :
    ContinuousOn (fun t : ℝ ↦ ((t : ℂ) ^ k) • (β ((t : ℂ) • x)).curryLeft x) (Icc 0 1) := by
  have hm : MapsTo (fun t : ℝ ↦ (t : ℂ) • x) (Icc (0 : ℝ) 1) (closedBall 0 R) :=
    fun t ht ↦ norm_smul_mem_closedBall ht hx
  have h1 : ContinuousOn (fun t : ℝ ↦ β ((t : ℂ) • x)) (Icc 0 1) :=
    hβc.comp ((Complex.continuous_ofReal.smul continuous_const).continuousOn) hm
  refine ((Complex.continuous_ofReal.pow k).continuousOn).smul ?_
  exact ((ContinuousLinearMap.apply ℂ _ x).continuous.comp
    (curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).continuous).comp_continuousOn h1

/-- The derivative of the radial homotopy operator. -/
public theorem hasFDerivAt_radialHomotopy [FiniteDimensional ℂ E] {k : ℕ}
    {β : E → E [⋀^Fin (k + 1)]→L[ℂ] F} {r : ℝ} (hcd : ContDiffOn ℂ 1 β (ball 0 r))
    {x : E} (hx : x ∈ ball (0 : E) r) :
    HasFDerivAt (radialHomotopy k β) (∫ t in (0 : ℝ)..1, radialDeriv k β x t) x := by
  obtain ⟨R, hxR, hRr⟩ := exists_between (mem_ball_zero_iff.mp hx)
  set δ := R - ‖x‖ with hδ
  have hδpos : 0 < δ := sub_pos.mpr hxR
  have hsub : closedBall x δ ⊆ closedBall (0 : E) R := by
    intro y hy
    rw [mem_closedBall_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hy
    calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ δ + ‖x‖ := by gcongr
      _ = R := by rw [hδ]; ring
  have hβc : ContinuousOn β (closedBall 0 R) :=
    hcd.continuousOn.mono (closedBall_subset_ball hRr)
  have hK : IsCompact (closedBall (0 : E) R ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuousOn_radialDeriv hRr hcd)
  have hIoc : Set.uIoc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (s := closedBall x δ) (bound := fun _ ↦ C) (closedBall_mem_nhds x hδpos) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [closedBall_mem_nhds x hδpos] with y hy
    exact ((continuousOn_radialIntegrand hβc (hsub hy)).mono hIoc).aestronglyMeasurable
      measurableSet_uIoc
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_radialIntegrand hβc (hsub (mem_closedBall_self hδpos.le))
  · have h := (continuousOn_radialDeriv (k := k) hRr hcd).comp
      (Continuous.prodMk_right x).continuousOn (fun t ht ↦ ⟨hsub (mem_closedBall_self hδpos.le), ht⟩)
    exact (h.mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · refine Filter.Eventually.of_forall fun t ht y hy ↦ hC (y, t) ⟨hsub hy, hIoc ht⟩
  · refine Filter.Eventually.of_forall fun t ht y hy ↦ ?_
    have hty : (t : ℂ) • y ∈ ball (0 : E) r :=
      closedBall_subset_ball hRr (norm_smul_mem_closedBall (hIoc ht) (hsub hy))
    exact hasFDerivAt_radialIntegrand y (t : ℂ)
      ((hcd.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hty))

/-- The radial homotopy formula `d K β + K (d β) = β` on a ball centred at `0`. -/
public theorem extDeriv_radialHomotopy_add [FiniteDimensional ℂ E] {k : ℕ}
    {β : E → E [⋀^Fin (k + 1)]→L[ℂ] F} {r : ℝ} (hcd : ContDiffOn ℂ 1 β (ball 0 r))
    {x : E} (hx : x ∈ ball (0 : E) r) :
    extDeriv (radialHomotopy k β) x + radialHomotopy (k + 1) (extDeriv β) x = β x := by
  set cL := (curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k)).toContinuousLinearMap with hcL
  obtain ⟨R, hxR, hRr⟩ := exists_between (mem_ball_zero_iff.mp hx)
  have hxc : x ∈ closedBall (0 : E) R := mem_closedBall_zero_iff.mpr hxR.le
  have hβc : ContinuousOn β (closedBall 0 R) :=
    hcd.continuousOn.mono (closedBall_subset_ball hRr)
  have hβ'c : ContinuousOn (fderiv ℂ β) (closedBall 0 R) :=
    (hcd.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono (closedBall_subset_ball hRr)
  have hm : MapsTo (fun t : ℝ ↦ (t : ℂ) • x) (Icc (0 : ℝ) 1) (closedBall 0 R) :=
    fun t ht ↦ norm_smul_mem_closedBall ht hxc
  have hdiff : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ β ((t : ℂ) • x) := fun t ht ↦
    (hcd.differentiableOn one_ne_zero).differentiableAt
      (isOpen_ball.mem_nhds (closedBall_subset_ball hRr (hm ht)))
  have hD := hasFDerivAt_radialHomotopy (k := k) hcd hx
  have hDc : ContinuousOn (fun t ↦ radialDeriv k β x t) (Icc 0 1) :=
    (continuousOn_radialDeriv (k := k) hRr hcd).comp (Continuous.prodMk_right x).continuousOn
      (fun t ht ↦ ⟨hxc, ht⟩)
  have hDi : IntervalIntegrable (fun t ↦ radialDeriv k β x t) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]; exact hDc
  have h1 : extDeriv (radialHomotopy k β) x =
      ∫ t in (0 : ℝ)..1, alternatizeUncurryFin (radialDeriv k β x t) := by
    rw [extDeriv, hD.fderiv, ← alternatizeUncurryFinCLM_apply,
      ← (alternatizeUncurryFinCLM ℂ E F).intervalIntegral_comp_comm hDi]
    simp [alternatizeUncurryFinCLM_apply]
  have h2 : radialHomotopy (k + 1) (extDeriv β) x = ∫ t in (0 : ℝ)..1,
      ((t : ℂ) ^ (k + 1)) • (alternatizeUncurryFin (fderiv ℂ β ((t : ℂ) • x))).curryLeft x := rfl
  have hpt : ∀ t : ℝ, alternatizeUncurryFin (radialDeriv k β x t) +
      ((t : ℂ) ^ (k + 1)) • (alternatizeUncurryFin (fderiv ℂ β ((t : ℂ) • x))).curryLeft x =
      (((k + 1 : ℂ)) * (t : ℂ) ^ k) • β ((t : ℂ) • x) +
        ((t : ℂ) ^ (k + 1)) • fderiv ℂ β ((t : ℂ) • x) x := by
    intro t
    rw [← curryLeft_alternatizeUncurryFin_add (fderiv ℂ β ((t : ℂ) • x)) x]
    simp only [radialDeriv, alternatizeUncurryFin_smul, alternatizeUncurryFin_add,
      alternatizeUncurryFin_curryLeft]
    rw [← hcL, ← Nat.cast_smul_eq_nsmul ℂ]
    push_cast
    first | done | module
  have hint1 : IntervalIntegrable (fun t ↦ alternatizeUncurryFin (radialDeriv k β x t))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (alternatizeUncurryFinCLM ℂ E F).continuous.comp_continuousOn hDc
  have hc2 : ContinuousOn (fun t : ℝ ↦
      ((t : ℂ) ^ (k + 1)) • (alternatizeUncurryFin (fderiv ℂ β ((t : ℂ) • x))).curryLeft x)
      (Icc 0 1) := by
    refine ((Complex.continuous_ofReal.pow (k + 1)).continuousOn).smul ?_
    exact ((ContinuousLinearMap.apply ℂ _ x).continuous.comp
      ((curryLeftLI (𝕜 := ℂ) (E := E) (F := F) (n := k + 1)).continuous.comp
        (alternatizeUncurryFinCLM ℂ E F).continuous)).comp_continuousOn
      (hβ'c.comp (Complex.continuous_ofReal.smul continuous_const).continuousOn hm)
  have hint2 : IntervalIntegrable (fun t : ℝ ↦
      ((t : ℂ) ^ (k + 1)) • (alternatizeUncurryFin (fderiv ℂ β ((t : ℂ) • x))).curryLeft x)
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]; exact hc2
  rw [h1, h2, ← intervalIntegral.integral_add hint1 hint2]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ ↦
    (((k + 1 : ℂ)) * (t : ℂ) ^ k) • β ((t : ℂ) • x) +
      ((t : ℂ) ^ (k + 1)) • fderiv ℂ β ((t : ℂ) • x) x) (fun t _ ↦ hpt t)]
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ ((s : ℂ) ^ (k + 1)) • β ((s : ℂ) • x))
      ((((k + 1 : ℂ)) * (t : ℂ) ^ k) • β ((t : ℂ) • x) +
        ((t : ℂ) ^ (k + 1)) • fderiv ℂ β ((t : ℂ) • x) x) t := by
    intro t ht
    have hp : HasDerivAt (fun s : ℝ ↦ (s : ℂ) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k) t := by
      have := (hasDerivAt_pow (k + 1) (t : ℂ)).comp_ofReal
      simpa using this
    have hl : HasDerivAt (fun s : ℝ ↦ (s : ℂ) • x) x t := by
      have := ((hasDerivAt_id t).ofReal_comp).smul_const x
      simpa using this
    have hb := ((hdiff t (Ioo_subset_Icc_self ht)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hl
    have h3 := hp.smul hb
    refine h3.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_restrictScalars']
    push_cast
    exact add_comm _ _
  have hcont : ContinuousOn (fun s : ℝ ↦ ((s : ℂ) ^ (k + 1)) • β ((s : ℂ) • x)) (Icc 0 1) :=
    ((Complex.continuous_ofReal.pow (k + 1)).continuousOn).smul
      (hβc.comp (Complex.continuous_ofReal.smul continuous_const).continuousOn hm)
  have hint3 : IntervalIntegrable (fun t : ℝ ↦
      (((k + 1 : ℂ)) * (t : ℂ) ^ k) • β ((t : ℂ) • x) +
        ((t : ℂ) ^ (k + 1)) • fderiv ℂ β ((t : ℂ) • x) x) volume 0 1 := by
    have he : (fun t : ℝ ↦ (((k + 1 : ℂ)) * (t : ℂ) ^ k) • β ((t : ℂ) • x) +
        ((t : ℂ) ^ (k + 1)) • fderiv ℂ β ((t : ℂ) • x) x) = fun t ↦
        alternatizeUncurryFin (radialDeriv k β x t) +
        ((t : ℂ) ^ (k + 1)) • (alternatizeUncurryFin (fderiv ℂ β ((t : ℂ) • x))).curryLeft x :=
      funext fun t ↦ (hpt t).symm
    rw [he]
    exact hint1.add hint2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint3]
  simp

/-- **Poincaré lemma** on a ball: a closed `C¹` form of degree `k + 1` on `ball 0 r` is the
exterior derivative of a differentiable `k`-form there. -/
theorem exists_primitive_ball_zero [FiniteDimensional ℂ E] {k : ℕ}
    {β : E → E [⋀^Fin (k + 1)]→L[ℂ] F} {r : ℝ} (hcd : ContDiffOn ℂ 1 β (ball 0 r))
    (hd : ∀ y ∈ ball (0 : E) r, extDeriv β y = 0) :
    ∃ η : E → E [⋀^Fin k]→L[ℂ] F, DifferentiableOn ℂ η (ball 0 r) ∧
      ∀ y ∈ ball (0 : E) r, extDeriv η y = β y := by
  refine ⟨radialHomotopy k β, fun y hy ↦ (hasFDerivAt_radialHomotopy hcd hy).differentiableAt
    |>.differentiableWithinAt, fun y hy ↦ ?_⟩
  have h := extDeriv_radialHomotopy_add hcd hy
  have h0 : radialHomotopy (k + 1) (extDeriv β) y = 0 := by
    unfold radialHomotopy
    rw [intervalIntegral.integral_congr (g := fun _ ↦ 0)]
    · simp
    · intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hts : (t : ℂ) • y ∈ ball (0 : E) r := by
        rw [mem_ball_zero_iff] at hy ⊢
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc t * ‖y‖ ≤ 1 * ‖y‖ := by gcongr; exact ht.2
          _ < r := by rwa [one_mul]
      show (t : ℂ) ^ (k + 1) • (extDeriv β ((t : ℂ) • y)).curryLeft y = 0
      rw [hd _ hts]
      simp
  rwa [h0, add_zero] at h

/-- Precomposing an alternating map with the identity gives the same map. -/
lemma compCLM_id {m : ℕ} (ω : E [⋀^Fin m]→L[ℂ] F) :
    ω.compContinuousLinearMap (ContinuousLinearMap.id ℂ E) = ω := by
  ext v; simp

/-- **Holomorphic Poincaré lemma** on a ball. -/
public theorem exists_primitive_ball [FiniteDimensional ℂ E] {k : ℕ}
    {β : E → E [⋀^Fin (k + 1)]→L[ℂ] F} {c : E} {r : ℝ} (hcd : ContDiffOn ℂ 1 β (ball c r))
    (hd : ∀ y ∈ ball c r, extDeriv β y = 0) :
    ∃ η : E → E [⋀^Fin k]→L[ℂ] F, DifferentiableOn ℂ η (ball c r) ∧
      ∀ y ∈ ball c r, extDeriv η y = β y := by
  set β' : E → E [⋀^Fin (k + 1)]→L[ℂ] F := fun y ↦ β (y + c) with hβ'
  have hmap : ∀ y, y ∈ ball (0 : E) r ↔ y + c ∈ ball c r := fun y ↦ by
    simp [mem_ball, dist_eq_norm]
  have htr : ∀ y, ContDiffAt ℂ 2 (fun z : E ↦ z + c) y := fun y ↦
    (contDiff_id.add contDiff_const).contDiffAt
  have hfd : ∀ y, fderiv ℂ (fun z : E ↦ z + c) y = ContinuousLinearMap.id ℂ E := fun y ↦ by
    rw [fderiv_add_const, fderiv_id']
  have hcd' : ContDiffOn ℂ 1 β' (ball 0 r) := by
    refine hcd.comp (contDiff_id.add contDiff_const).contDiffOn ?_
    intro y hy; exact (hmap y).1 hy
  have hpull : ∀ {m : ℕ} (ω : E → E [⋀^Fin m]→L[ℂ] F) (y : E),
      DifferentiableAt ℂ ω (y + c) →
      extDeriv (fun z ↦ ω (z + c)) y = extDeriv ω (y + c) := by
    intro m ω y hω
    have h := extDeriv_pullback (x := y) (f := fun z : E ↦ z + c) hω (htr y)
      (by simp [minSmoothness])
    simp only [hfd, compCLM_id] at h
    exact h
  have hd' : ∀ y ∈ ball (0 : E) r, extDeriv β' y = 0 := by
    intro y hy
    rw [hpull β y ((hcd.differentiableOn one_ne_zero).differentiableAt
      (isOpen_ball.mem_nhds ((hmap y).1 hy)))]
    exact hd _ ((hmap y).1 hy)
  obtain ⟨η, hη, hdη⟩ := exists_primitive_ball_zero hcd' hd'
  refine ⟨fun z ↦ η (z - c), ?_, fun y hy ↦ ?_⟩
  · refine hη.comp (differentiableOn_id.sub_const c) ?_
    intro y hy
    rw [hmap]; simpa using hy
  · have hy' : y - c ∈ ball (0 : E) r := by rw [hmap]; simpa using hy
    have hda : DifferentiableAt ℂ η (y - c) := hη.differentiableAt (isOpen_ball.mem_nhds hy')
    have h2 := extDeriv_pullback (x := y) (f := fun z : E ↦ z - c) (ω := η) (r := 2) hda
      ((contDiff_id.sub contDiff_const).contDiffAt) (by simp [minSmoothness])
    have hfd' : ∀ z, fderiv ℂ (fun z : E ↦ z - c) z = ContinuousLinearMap.id ℂ E := fun z ↦ by
      rw [fderiv_sub_const, fderiv_id']
    simp only [hfd', compCLM_id] at h2
    rw [h2, hdη _ hy']
    simp [β']

/-- **Osgood's lemma**, vector-valued: a complex differentiable map from an open subset of `ℂⁿ`
to a finite-dimensional space is analytic. -/
theorem analyticOnNhd_of_differentiableOn_vec {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] {S : Set (EuclideanSpace ℂ (Fin n))}
    (hS : IsOpen S) {G : EuclideanSpace ℂ (Fin n) → W} (hG : DifferentiableOn ℂ G S) :
    AnalyticOnNhd ℂ G S := by
  set b := Module.finBasis ℂ W
  let c : Fin (Module.finrank ℂ W) → W →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hG' : G = fun x => ∑ i, c i (G x) • b i := by
    funext x
    exact (b.sum_repr (G x)).symm
  intro x hx
  rw [hG']
  have hc : ∀ i, AnalyticAt ℂ (fun x => c i (G x)) x := fun i => by
    have hd : DifferentiableOn ℂ (fun x => c i (G x)) S :=
      (c i).differentiable.comp_differentiableOn hG
    exact MMP.Analytic.analyticOnNhd_of_differentiableOn hS hd x hx
  convert Finset.analyticAt_sum Finset.univ (fun i _ =>
    (hc i).smul (analyticAt_const : AnalyticAt ℂ (fun _ => b i) x)) using 1
  funext y
  simp [Finset.sum_apply]

/-- A complex differentiable map from an open subset of `ℂⁿ` to a finite-dimensional space is
smooth. -/
public theorem contDiffOn_of_differentiableOn_vec {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] {S : Set (EuclideanSpace ℂ (Fin n))}
    (hS : IsOpen S) {G : EuclideanSpace ℂ (Fin n) → W} (hG : DifferentiableOn ℂ G S)
    {N : WithTop ℕ∞} : ContDiffOn ℂ N G S :=
  (analyticOnNhd_of_differentiableOn_vec hS hG).contDiffOn_of_completeSpace

end HolomorphicPoincare

/-! ### Determinant forms on `ℂⁿ` -/

section DetForms

open ContinuousAlternatingMap

variable {n : ℕ}

/-- The determinant forms `v ↦ det (v a (ι b))` on `ℂⁿ`. -/
@[expose] public noncomputable def detForm : ∀ {p : ℕ}, (Fin p → Fin n) →
    EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ
  | 0, _ => constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) 1
  | _ + 1, ι => alternatizeUncurryFin
      ((EuclideanSpace.proj (ι 0) : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).smulRight
        (detForm (Fin.tail ι)))

/-- `detForm ι v` is the determinant of the matrix `(v a (ι b))`. -/
public theorem detForm_apply : ∀ {p : ℕ} (ι : Fin p → Fin n) (v : Fin p → EuclideanSpace ℂ (Fin n)),
    detForm ι v = (Matrix.of fun a b => v a (ι b)).det
  | 0, ι, v => by simp [detForm]
  | p + 1, ι, v => by
    rw [detForm, alternatizeUncurryFin_apply, Matrix.det_succ_column_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply, detForm_apply]
    simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [mul_assoc]
    congr 2

/-- The sorted enumeration of a `p`-subset. -/
@[expose] public noncomputable def sortedIdx {p : ℕ} (I : Set.powersetCard (Fin n) p) :
    Fin p → Fin n :=
  fun j => Set.powersetCard.ofFinEmbEquiv.symm I j

/-- The determinant form of the sorted enumeration of a `p`-subset `I` is the coordinate
functional at `I` of the standard basis of the `p`-th exterior power. -/
theorem toAlternatingMap_detForm_sorted {p : ℕ} (I : Set.powersetCard (Fin n) p) :
    (detForm (sortedIdx I)).toAlternatingMap =
      exteriorPower.alternatingMapLinearEquiv.symm
        (((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.exteriorPower p).coord I) := by
  ext v
  rw [ContinuousAlternatingMap.coe_toAlternatingMap, detForm_apply,
    exteriorPower.alternatingMapLinearEquiv_symm_apply]
  rw [exteriorPower.basis_coord, LinearMap.compAlternatingMap_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

/-- The determinant forms of the `p`-subsets are linearly independent. -/
public theorem linearIndependent_detForm (p : ℕ) :
    LinearIndependent ℂ (fun I : Set.powersetCard (Fin n) p => detForm (sortedIdx I)) := by
  set B := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.exteriorPower p
  apply LinearIndependent.of_comp (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℂ))
  have h : (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℂ)) ∘
      (fun I : Set.powersetCard (Fin n) p => detForm (sortedIdx I)) =
      exteriorPower.alternatingMapLinearEquiv.symm ∘ B.dualBasis := by
    funext I
    simp only [Function.comp_apply, Module.Basis.coe_dualBasis]
    exact toAlternatingMap_detForm_sorted I
  rw [h]
  exact B.dualBasis.linearIndependent.map' _ (LinearEquiv.ker _)

/-- The determinant forms of the `p`-subsets span the alternating `p`-forms on `ℂⁿ`. -/
public theorem span_detForm (p : ℕ) :
    ⊤ ≤ Submodule.span ℂ
      (Set.range fun I : Set.powersetCard (Fin n) p => detForm (sortedIdx I)) := by
  set B := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.exteriorPower p
  intro ω _
  set f := exteriorPower.alternatingMapLinearEquiv ω.toAlternatingMap
  have hf := B.dualBasis.sum_repr f
  have key : ω = ∑ I, B.dualBasis.repr f I • detForm (sortedIdx I) := by
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    change ContinuousAlternatingMap.toAlternatingMapLinear (R := ℂ) ω =
      ContinuousAlternatingMap.toAlternatingMapLinear (R := ℂ)
        (∑ I, B.dualBasis.repr f I • detForm (sortedIdx I))
    have h1 : ContinuousAlternatingMap.toAlternatingMapLinear (R := ℂ) ω =
        exteriorPower.alternatingMapLinearEquiv.symm f := by
      simp [f, ContinuousAlternatingMap.toAlternatingMapLinear]
    rw [h1]
    conv_lhs => rw [← hf]
    rw [_root_.map_sum, _root_.map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, map_smul, Module.Basis.coe_dualBasis]
    exact congrArg _ (toAlternatingMap_detForm_sorted I).symm
  rw [key]
  exact Submodule.sum_mem _ fun I _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨I, rfl⟩)

/-- The determinant forms of the `p`-subsets form a basis of the alternating forms on `ℂⁿ`. -/
@[expose] public noncomputable def detBasis (p : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) p) ℂ (EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ) :=
  Module.Basis.mk (linearIndependent_detForm p) (span_detForm p)

/-- The basis vector of `detBasis` at `I` is the determinant form of its sorted enumeration. -/
public theorem detBasis_apply {p : ℕ} (I : Set.powersetCard (Fin n) p) :
    detBasis p I = detForm (sortedIdx I) :=
  Module.Basis.mk_apply _ _ _

/-- The derivative of `w ↦ (w_i + c) • D` is `dw_i ⊗ D`. -/
theorem hasFDerivAt_affine_smul {p : ℕ} (i : Fin n) (c : ℂ)
    (D : EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    HasFDerivAt (fun w : EuclideanSpace ℂ (Fin n) => (EuclideanSpace.proj i w + c) • D)
      ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).smulRight D) v := by
  have h := (((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasFDerivAt
    (x := v)).add_const c).smul_const D
  exact h

/-- The exterior derivative of `w ↦ (w_i + c) • D` is `dw_i ∧ D`. -/
theorem extDeriv_affine_smul {p : ℕ} (i : Fin n) (c : ℂ)
    (D : EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    extDeriv (fun w : EuclideanSpace ℂ (Fin n) => (EuclideanSpace.proj i w + c) • D) v =
      alternatizeUncurryFin
        ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).smulRight D) := by
  rw [extDeriv, (hasFDerivAt_affine_smul i c D v).fderiv]

/-- The exterior derivative of `w ↦ (w_i + c) • detForm ι` is `detForm (Fin.cons i ι)`. -/
theorem extDeriv_affine_smul_detForm {p : ℕ} (i : Fin n) (c : ℂ) (ι : Fin p → Fin n)
    (v : EuclideanSpace ℂ (Fin n)) :
    extDeriv (fun w : EuclideanSpace ℂ (Fin n) => (EuclideanSpace.proj i w + c) • detForm ι) v =
      detForm (Fin.cons i ι : Fin (p + 1) → Fin n) := by
  rw [extDeriv_affine_smul, detForm]
  simp only [Fin.cons_zero, Fin.tail_cons]

end DetForms

/-! ### Analytic differential forms in GAGA charts -/

section AnalyticForms

open CategoryTheory.Limits TopologicalSpace
open MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- The patch `φ⁻¹(O)` of a chart. -/
@[expose] public def patch {n : ℕ}
    (φ : OpenPartialHomeomorph (ComplexPoints sX) (EuclideanSpace ℂ (Fin n)))
    (O : Opens (EuclideanSpace ℂ (Fin n))) : Opens (space sX) :=
  ⟨φ.source ∩ φ ⁻¹' O, φ.isOpen_inter_preimage O.2⟩

/-- The analytic differential forms. -/
public noncomputable abbrev Ωan (p : ℕ) : SheafOfModules.{0} (ringCatSheaf sX) :=
  (analytifyModule sX).obj (sX.relativeDifferentialForms (p : ℤ))

/-- The analytification of an algebraic form, restricted to an open. -/
@[expose] public noncomputable def an (p : ℕ) (V : X.Opens) (U : Opens (space sX))
    (h : U ≤ (Opens.map (toSchemeHom sX)).obj V)
    (s : Γ(sX.relativeDifferentialForms (p : ℤ), V)) : (Ωan sX p).val.obj (op U) :=
  (Ωan sX p).val.presheaf.map (homOfLE h).op
    ((analytifyModuleUnit sX (sX.relativeDifferentialForms (p : ℤ))).val.app (op V) s)

/-- The chart data at a point supplied by GAGA. -/
public structure ChartData (n : ℕ) [ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
    (Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]) (y : ComplexPoints sX) where
  /-- An affine open of `X`. -/
  W : X.Opens
  hW : IsAffineOpen W
  /-- Regular functions on `W` serving as coordinates. -/
  z : Fin n → Γ(X, W)
  /-- A chart of the complex manifold around `y`. -/
  φ : OpenPartialHomeomorph (ComplexPoints sX) (EuclideanSpace ℂ (Fin n))
  mem : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)
  hφ : φ.source ⊆ chart W
  hy : y ∈ φ.source
  coord : ∀ y' (hy' : y' ∈ φ.source) (i : Fin n),
    φ y' i = evalHom W ⟨y', hφ hy'⟩ (z i) - evalHom W ⟨y, hφ hy⟩ (z i)
  /-- The coordinate expression of an analytic `p`-form on the patch of `φ` over `O`. -/
  Ψ : ∀ (p : ℕ) (O : Opens (EuclideanSpace ℂ (Fin n))),
    (Ωan sX p).val.obj (op (patch sX φ O)) →+
      (patch sX φ O → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ)
  /-- The coordinate expression `Ψ` is injective. -/
  inj : ∀ p O, Function.Injective (Ψ p O)
  range : ∀ p O (η : patch sX φ O → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ),
    η ∈ Set.range (Ψ p O) ↔
      ∃ ξ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ,
        DifferentiableOn ℂ ξ (φ.target ∩ O) ∧ ∀ y' : patch sX φ O, ξ (φ y') = η y'
  restr : ∀ p O₁ O₂ (h : patch sX φ O₁ ≤ patch sX φ O₂)
    (s : (Ωan sX p).val.obj (op (patch sX φ O₂))) (y' : patch sX φ O₁),
    Ψ p O₁ ((Ωan sX p).val.presheaf.map (homOfLE h).op s) y' = Ψ p O₂ s ⟨y'.1, h y'.2⟩
  smul : ∀ p O (a : (ringCatSheaf sX).obj.obj (op (patch sX φ O)))
    (s : (Ωan sX p).val.obj (op (patch sX φ O))) (y' : patch sX φ O),
    Ψ p O (a • s) y' = Θ.hom.hom.app (op (patch sX φ O)) a y' • Ψ p O s y'
  deg0 : ∀ (V : X.Opens) (hV : IsAffineOpen V) O
    (h : patch sX φ O ≤ (Opens.map (toSchemeHom sX)).obj V) (g : Γ(X, V)) (y' : patch sX φ O),
    letI := MMP.Mori.sectionAlgebra sX V
    Ψ 0 O (an sX 0 V (patch sX φ O) h ((MMP.DeRham.formsAlgEquiv sX 0 ⟨V, hV⟩).symm
        ((exteriorPower.zeroEquiv Γ(X, V) Ω[Γ(X, V)⁄ℂ]).symm g))) y' =
      ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0)
        (evalHom V ⟨y'.1, mem_chart_iff.2 (h y'.2)⟩ g)
  dcompat : ∀ (p : ℕ) (V : X.Opens) (hV : IsAffineOpen V) O
    (h : patch sX φ O ≤ (Opens.map (toSchemeHom sX)).obj V),
    letI := MMP.Mori.sectionAlgebra sX V
    ∀ (η : ⋀[Γ(X, V)]^p Ω[Γ(X, V)⁄ℂ])
      (ξ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ),
      DifferentiableOn ℂ ξ (φ.target ∩ O) →
      (∀ y' : patch sX φ O, ξ (φ y') =
        Ψ p O (an sX p V (patch sX φ O) h ((MMP.DeRham.formsAlgEquiv sX p ⟨V, hV⟩).symm η)) y') →
      ∀ y' : patch sX φ O, Ψ (p + 1) O (an sX (p + 1) V (patch sX φ O) h
          ((MMP.DeRham.formsAlgEquiv sX (p + 1) ⟨V, hV⟩).symm
            (KaehlerDifferential.deRhamDifferential (A := ℂ) p η))) y' =
        extDeriv ξ (φ y')

/-- A complex point of `X` is a closed point of the scheme `X`. -/
public theorem isClosed_singleton_toScheme' (x : ComplexPoints sX) :
    IsClosed ({x.toScheme} : Set X) := by
  have : IsClosedImmersion x.hom := isClosedImmersion_of_comp_eq_id sX x.hom x.2
  convert x.hom.isClosedEmbedding.isClosed_range using 1
  ext y
  constructor
  · rintro rfl; exact ⟨default, rfl⟩
  · rintro ⟨q, rfl⟩; rw [Subsingleton.elim q default]; rfl

set_option maxRecDepth 10000 in
/-- A smooth projective complex variety `X` admits an `n`-dimensional complex manifold structure
on its complex points and an isomorphism `Θ` of its analytic structure sheaf with the sheaf of
holomorphic functions, compatible with evaluation of regular functions, such that every point
has chart data `ChartData sX n Θ y`. -/
theorem exists_chartData [IsProjectiveVariety ℂ sX] (hX : MMP.Mori.IsSmoothScheme sX) :
    ∃ (n : ℕ) (cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)),
      (letI := cs; IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)) ∧
      ∃ Θ : (letI := cs; structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]),
        (∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
          Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
            evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g) ∧
        ∀ y : ComplexPoints sX, Nonempty (letI := cs; ChartData sX n Θ y) := by
  have hP : IsProjective sX := (isProjectiveVariety_iff_isProjective ℂ sX).mp inferInstance
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  haveI : IsProper sX := hP.isProper
  haveI := MMP.Analytic.smoothOfRelativeDimension_of_isSmoothScheme sX inferInstance hX hn
  obtain ⟨cs, hmfd, -, -, -, Θ, hΘ, hloc⟩ :=
    MMP.Analytic.analytification_smooth_differentials_of_smoothOfRelativeDimension sX (n := n)
      (0 : MMP.Mori.Divisor X)
      (MMP.Mori.DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sX hX)
  refine ⟨n, cs, hmfd, Θ, hΘ, fun y => ?_⟩
  obtain ⟨W, hW, hxW, k, hk, z, -, -, -, hy⟩ :=
    hloc y.toScheme (isClosed_singleton_toScheme' sX y)
  obtain ⟨φ, hφm, hφ, hyφ, hcoord, Ψ, i1, i2, i3, i4, i5, i6, -⟩ := hy y (mem_chart_iff.2 hxW)
  exact ⟨⟨W, hW, z, φ, hφm, hφ, hyφ, hcoord, Ψ, i1, i2, i3, i4, i5, i6⟩⟩

/-- The analytification of a regular function, restricted to an open. -/
@[expose] public noncomputable def an₀ (V : X.Opens) (U : Opens (space sX))
    (h : U ≤ (Opens.map (toSchemeHom sX)).obj V) (g : Γ(X, V)) :
    (ringCatSheaf sX).obj.obj (op U) :=
  (ringCatSheaf sX).obj.map (homOfLE h).op ((ringCatSheafHom sX).hom.app (op V) g)

/-- Analytification of forms is linear over regular functions. -/
public lemma an_smul (p : ℕ) (V : X.Opens) (U : Opens (space sX))
    (h : U ≤ (Opens.map (toSchemeHom sX)).obj V) (g : Γ(X, V))
    (s : Γ(sX.relativeDifferentialForms (p : ℤ), V)) :
    an sX p V U h (g • s) = an₀ sX V U h g • an sX p V U h s := by
  unfold an an₀
  have h1 := ((analytifyModuleUnit sX (sX.relativeDifferentialForms (p : ℤ))).val.app (op V)).hom.map_smul g s
  erw [h1]
  exact (Ωan sX p).val.map_smul (homOfLE h).op _ _

/-- Under `Θ`, the analytification `an₀ sX V U h g` of a regular function `g` is the function
`y' ↦ g(y')` given by evaluation. -/
lemma Θ_an₀ {n : ℕ} [ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
    (Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX])
    (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (V : X.Opens) (U : Opens (space sX)) (h : U ≤ (Opens.map (toSchemeHom sX)).obj V)
    (g : Γ(X, V)) (y' : U) :
    Θ.hom.hom.app (op U) (an₀ sX V U h g) y' = evalHom V ⟨y'.1, mem_chart_iff.2 (h y'.2)⟩ g := by
  have hn := ConcreteCategory.congr_hom (Θ.hom.hom.naturality (homOfLE h).op)
    ((analytificationHom sX).hom.c.app (op V) g)
  have h2 := congrArg (fun f => f y') hn
  refine h2.trans ?_
  exact hΘ V g ⟨y'.1, h y'.2⟩

section Charts

variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]

/-- For charts `e, e'` in the maximal atlas and `s` contained in both sources, the transition
map `e' ∘ e.symm` is smooth on `e '' s`. -/
theorem transition_contDiffOn
    {e e' : OpenPartialHomeomorph (ComplexPoints sX) (EuclideanSpace ℂ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX))
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX))
    {s : Set (ComplexPoints sX)} (hs : s ⊆ e.source) (hs' : s ⊆ e'.source) :
    ContDiffOn ℂ ∞ (e' ∘ e.symm) (e '' s) := by
  have h := (contMDiffOn_iff_of_mem_maximalAtlas' he he' hs (fun x hx => hs' hx)).1
    (contMDiff_id.contMDiffOn (s := s))
  simp only [OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, Function.comp_id,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.image_id] at h
  exact h

/-- The image under `φ` of the patch `patch sX φ O` is `φ.target ∩ O`. -/
theorem patch_image {φ : OpenPartialHomeomorph (ComplexPoints sX) (EuclideanSpace ℂ (Fin n))}
    (O : Opens (EuclideanSpace ℂ (Fin n))) :
    φ '' (patch sX φ O : Set (ComplexPoints sX)) = φ.target ∩ O := by
  ext v
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨φ.map_source hy1, hy2⟩
  · rintro ⟨hv1, hv2⟩
    refine ⟨φ.symm v, ⟨φ.map_target hv1, ?_⟩, φ.right_inv hv1⟩
    show φ (φ.symm v) ∈ O
    rw [φ.right_inv hv1]; exact hv2

end Charts

section Gen

variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}

/-- The algebraic generators `β_ι = d(z_{ι 0} β_{tail ι})` attached to the coordinates of a
chart. -/
noncomputable def gen {y₁ : ComplexPoints sX} (C : ChartData sX n Θ y₁) :
    ∀ {p : ℕ}, (Fin p → Fin n) →
      (letI := MMP.Mori.sectionAlgebra sX C.W; ⋀[Γ(X, C.W)]^p Ω[Γ(X, C.W)⁄ℂ])
  | 0, _ => letI := MMP.Mori.sectionAlgebra sX C.W
      (exteriorPower.zeroEquiv Γ(X, C.W) Ω[Γ(X, C.W)⁄ℂ]).symm 1
  | p + 1, ι => letI := MMP.Mori.sectionAlgebra sX C.W
      KaehlerDifferential.deRhamDifferential (A := ℂ) p (C.z (ι 0) • gen C (Fin.tail ι))

/-- The degree-zero generator `gen sX C ι` is the unit `1` in `⋀^0 Ω`. -/
lemma gen_zero {y₁ : ComplexPoints sX} (C : ChartData sX n Θ y₁) (ι : Fin 0 → Fin n) :
    gen sX C ι = (letI := MMP.Mori.sectionAlgebra sX C.W
      (exteriorPower.zeroEquiv Γ(X, C.W) Ω[Γ(X, C.W)⁄ℂ]).symm 1) := rfl

/-- The generator in degree `p + 1` is `gen sX C ι = d(z_{ι 0} • gen sX C (Fin.tail ι))`. -/
lemma gen_succ {y₁ : ComplexPoints sX} (C : ChartData sX n Θ y₁) {p : ℕ}
    (ι : Fin (p + 1) → Fin n) :
    gen sX C ι = (letI := MMP.Mori.sectionAlgebra sX C.W
      KaehlerDifferential.deRhamDifferential (A := ℂ) p (C.z (ι 0) • gen sX C (Fin.tail ι))) :=
  rfl

end Gen

section Gen2

variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)

/-- The set `φ.target ∩ O` is open. -/
lemma isOpen_target_inter {φ : OpenPartialHomeomorph (ComplexPoints sX) (EuclideanSpace ℂ (Fin n))}
    (O : Opens (EuclideanSpace ℂ (Fin n))) : IsOpen (φ.target ∩ O) :=
  φ.open_target.inter O.2

/-- Pulling back an alternating map along `L` commutes with scalar multiplication:
`(a • D) ∘ L = a • (D ∘ L)`. -/
lemma compCLM_smul' {p : ℕ} (a : ℂ) (D : EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    (a • D).compContinuousLinearMap L = a • D.compContinuousLinearMap L := by
  ext v; simp

set_option maxRecDepth 10000 in
include hΘ in
/-- In the chart of `C`, the analytification of the generator `gen sX C' ι` of the chart `C'` is
the pullback of `detForm ι` along the derivative of the transition map `C'.φ ∘ C.φ.symm`. -/
theorem Ψ_an_gen {y y₁ : ComplexPoints sX} (C : ChartData sX n Θ y) (C' : ChartData sX n Θ y₁)
    (O : Opens (EuclideanSpace ℂ (Fin n)))
    (hW : patch sX C.φ O ≤ (Opens.map (toSchemeHom sX)).obj C'.W)
    (hsrc : (patch sX C.φ O : Set (ComplexPoints sX)) ⊆ C'.φ.source) :
    ∀ {p : ℕ} (ι : Fin p → Fin n) (y' : patch sX C.φ O),
      C.Ψ p O (an sX p C'.W (patch sX C.φ O) hW
          ((MMP.DeRham.formsAlgEquiv sX p ⟨C'.W, C'.hW⟩).symm (gen sX C' ι))) y' =
        (detForm ι).compContinuousLinearMap (fderiv ℂ (C'.φ ∘ C.φ.symm) (C.φ y')) := by
  have hκ : ContDiffOn ℂ ∞ (C'.φ ∘ C.φ.symm) (C.φ.target ∩ O) := by
    rw [← patch_image sX O]
    exact transition_contDiffOn sX C.mem C'.mem (fun x hx => hx.1) hsrc
  intro p
  induction p with
  | zero =>
    intro ι y'
    have h0 := C.deg0 C'.W C'.hW O hW 1 y'
    rw [gen_zero]
    erw [h0]
    rw [map_one]
    ext v
    simp [detForm]
  | succ p ih =>
    intro ι y'
    set κ := C'.φ ∘ C.φ.symm with hκdef
    set c := evalHom C'.W ⟨y₁, C'.hφ C'.hy⟩ (C'.z (ι 0)) with hc
    let F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ :=
      fun w => (EuclideanSpace.proj (ι 0) w + c) • detForm (Fin.tail ι)
    let ξ := fun v => (F (κ v)).compContinuousLinearMap (fderiv ℂ κ v)
    have hFd : ∀ w, DifferentiableAt ℂ F w := fun w =>
      (hasFDerivAt_affine_smul (ι 0) c (detForm (Fin.tail ι)) w).differentiableAt
    have hκat : ∀ v ∈ C.φ.target ∩ O, ContDiffAt ℂ ∞ κ v := fun v hv =>
      hκ.contDiffAt ((isOpen_target_inter sX O).mem_nhds hv)
    have hξ : DifferentiableOn ℂ ξ (C.φ.target ∩ O) := by
      intro v hv
      have h1 : DifferentiableAt ℂ κ v := (hκat v hv).differentiableAt (by simp)
      have h2 : DifferentiableAt ℂ (fderiv ℂ κ) v :=
        ((hκat v hv).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
      exact (((hFd (κ v)).comp v h1).continuousAlternatingMapCompContinuousLinearMap
        h2).differentiableWithinAt
    have hcoord : ∀ y'' : patch sX C.φ O,
        evalHom C'.W ⟨y''.1, C'.hφ (hsrc y''.2)⟩ (C'.z (ι 0)) =
          EuclideanSpace.proj (ι 0) (κ (C.φ y'')) + c := by
      intro y''
      have h := C'.coord y''.1 (hsrc y''.2) (ι 0)
      have hk : κ (C.φ y'') = C'.φ y''.1 := by
        simp only [hκdef, Function.comp_apply, C.φ.left_inv y''.2.1]
      rw [hk]
      change _ = C'.φ y''.1 (ι 0) + c
      rw [h]; ring
    have hξval : ∀ y'' : patch sX C.φ O, ξ (C.φ y'') =
        C.Ψ p O (an sX p C'.W (patch sX C.φ O) hW
          ((MMP.DeRham.formsAlgEquiv sX p ⟨C'.W, C'.hW⟩).symm
            (C'.z (ι 0) • gen sX C' (Fin.tail ι)))) y'' := by
      intro y''
      rw [LinearEquiv.map_smul, an_smul, C.smul, Θ_an₀ sX Θ hΘ, ih]
      simp only [ξ, F, compCLM_smul']
      congr 1
      exact (hcoord y'').symm
    have hd := C.dcompat p C'.W C'.hW O hW (C'.z (ι 0) • gen sX C' (Fin.tail ι)) ξ hξ hξval y'
    rw [gen_succ]
    refine hd.trans ?_
    have hv : C.φ y' ∈ C.φ.target ∩ O := ⟨C.φ.map_source y'.2.1, y'.2.2⟩
    rw [extDeriv_pullback (r := ∞) (hFd _) (hκat _ hv) (by simp), extDeriv_affine_smul_detForm,
      Fin.cons_self_tail]

end Gen2

section Generation

attribute [local implicit_reducible] TopCat.Sheaf

variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)

/-- A chart patch lies over the affine open `W` of its chart data. -/
public lemma patch_le_W {y : ComplexPoints sX} (C : ChartData sX n Θ y)
    (O : Opens (EuclideanSpace ℂ (Fin n))) :
    patch sX C.φ O ≤ (Opens.map (toSchemeHom sX)).obj C.W := fun y' hy' =>
  mem_chart_iff.1 (C.hφ hy'.1)

/-- At a point `v` of `φ.target`, the derivative of `φ ∘ φ.symm` is the identity. -/
lemma fderiv_comp_symm_self {φ : OpenPartialHomeomorph (ComplexPoints sX) (EuclideanSpace ℂ (Fin n))}
    {v : EuclideanSpace ℂ (Fin n)} (hv : v ∈ φ.target) :
    fderiv ℂ (φ ∘ φ.symm) v = ContinuousLinearMap.id ℂ _ := by
  have h : (φ ∘ φ.symm) =ᶠ[nhds v] id :=
    Filter.eventually_of_mem (φ.open_target.mem_nhds hv) fun w hw => φ.right_inv hw
  rw [h.fderiv_eq, fderiv_id]

/-- `Θ.hom (Θ.inv b) = b` for a section `b` of the sheaf of holomorphic functions. -/
lemma Θ_inv_apply (N : Opens (space sX))
    (b : (𝒪[n, ComplexPoints sX]).presheaf.obj (op N)) :
    Θ.hom.hom.app (op N) (Θ.inv.hom.app (op N) b) = b := by
  have h' : Θ.inv.hom ≫ Θ.hom.hom = 𝟙 _ := congrArg (fun φ => φ.hom) Θ.inv_hom_id
  exact congrArg (fun g => (ConcreteCategory.hom (NatTrans.app g (op N))) b) h'

set_option maxRecDepth 10000 in
include hΘ in
/-- Every holomorphic `p`-form on a chart patch is a linear combination, with holomorphic
coefficients, of the analytified generators `gen sX C (sortedIdx I)` for `I` a `p`-subset of
`Fin n`. -/
theorem exists_eq_sum_gen {y : ComplexPoints sX} (C : ChartData sX n Θ y) {p : ℕ}
    (O : Opens (EuclideanSpace ℂ (Fin n))) (t : (Ωan sX p).val.obj (op (patch sX C.φ O))) :
    ∃ a : Set.powersetCard (Fin n) p → (ringCatSheaf sX).obj.obj (op (patch sX C.φ O)),
      t = ∑ I, a I • an sX p C.W (patch sX C.φ O) (patch_le_W sX C O)
        ((MMP.DeRham.formsAlgEquiv sX p ⟨C.W, C.hW⟩).symm (gen sX C (sortedIdx I))) := by
  haveI : FiniteDimensional ℂ (EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ) :=
    (detBasis (n := n) p).finiteDimensional_of_finite
  obtain ⟨ξ, hξd, hξ⟩ := (C.range p O (C.Ψ p O t)).1 ⟨t, rfl⟩
  have hSo : IsOpen (C.φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n)))) :=
    C.φ.open_target.inter O.2
  let crd : Set.powersetCard (Fin n) p → (EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ) →L[ℂ] ℂ :=
    fun I => LinearMap.toContinuousLinearMap ((detBasis p).coord I)
  let gI : Set.powersetCard (Fin n) p → EuclideanSpace ℂ (Fin n) → ℂ := fun I v => crd I (ξ v)
  have hgd : ∀ I, DifferentiableOn ℂ (gI I) (C.φ.target ∩ O) := fun I =>
    (crd I).differentiable.comp_differentiableOn hξd
  have hsm : ∀ I, ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞
      (fun y' : patch sX C.φ O => gI I (C.φ y'.1)) := by
    intro I y'
    refine (contMDiffAt_subtype_iff (f := fun y => gI I (C.φ y))).2 ?_
    have hmem : C.φ y'.1 ∈ C.φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n))) :=
      ⟨C.φ.map_source y'.2.1, y'.2.2⟩
    have h1 : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (gI I) (C.φ y'.1) :=
      ((MMP.Analytic.analyticOnNhd_of_differentiableOn hSo (hgd I)) _
        hmem).contDiffAt.contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞
        C.φ y'.1 :=
      (contMDiffOn_of_mem_maximalAtlas C.mem).contMDiffAt (C.φ.open_source.mem_nhds y'.2.1)
    exact h1.comp y'.1 h2
  let b : Set.powersetCard (Fin n) p → (𝒪[n, ComplexPoints sX]).presheaf.obj
      (op (patch sX C.φ O)) := fun I => ⟨fun y' => gI I (C.φ y'.1), hsm I⟩
  refine ⟨fun I => Θ.inv.hom.app (op (patch sX C.φ O)) (b I), C.inj p O ?_⟩
  funext y'
  rw [map_sum, Finset.sum_apply, ← hξ y']
  have hrepr := (detBasis p).sum_repr (ξ (C.φ y'))
  conv_lhs => rw [← hrepr]
  refine Finset.sum_congr rfl fun I _ => ?_
  erw [C.smul, Θ_inv_apply, Ψ_an_gen sX hΘ C C O (patch_le_W sX C O) (fun x hx => hx.1),
    fderiv_comp_symm_self sX (C.φ.map_source y'.2.1), compCLM_id, detBasis_apply]
  rfl

end Generation

section Transform

attribute [local implicit_reducible] TopCat.Sheaf

variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)

/-- Pulling back alternating maps along `L` commutes with finite sums. -/
lemma compCLM_sum {p : ℕ} {ι : Type*} (s : Finset ι)
    (D : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    (∑ i ∈ s, D i).compContinuousLinearMap L = ∑ i ∈ s, (D i).compContinuousLinearMap L := by
  ext v; simp

/-- Restricting the analytification of an algebraic form is analytifying it on the smaller open. -/
public lemma an_res (p : ℕ) (V : X.Opens) {U U' : Opens (space sX)} (hUU' : U ≤ U')
    (h' : U' ≤ (Opens.map (toSchemeHom sX)).obj V)
    (s : Γ(sX.relativeDifferentialForms (p : ℤ), V)) :
    (Ωan sX p).val.presheaf.map (homOfLE hUU').op (an sX p V U' h' s) =
      an sX p V U (hUU'.trans h') s := by
  unfold an
  have := ConcreteCategory.congr_hom ((Ωan sX p).val.presheaf.map_comp (homOfLE h').op
    (homOfLE hUU').op) ((analytifyModuleUnit sX (sX.relativeDifferentialForms (p : ℤ))).val.app (op V) s)
  exact this.symm

/-- `Θ` commutes with restriction: the function `Θ(a|_U)` is the restriction of `Θ(a)` to `U`. -/
lemma Θ_res (U U' : Opens (space sX)) (hUU' : U ≤ U')
    (a : (ringCatSheaf sX).obj.obj (op U')) (y' : U) :
    Θ.hom.hom.app (op U) ((ringCatSheaf sX).obj.map (homOfLE hUU').op a) y' =
      Θ.hom.hom.app (op U') a ⟨y'.1, hUU' y'.2⟩ := by
  have hn := ConcreteCategory.congr_hom (Θ.hom.hom.naturality (homOfLE hUU').op) a
  exact congrArg (fun f => f y') hn

set_option maxRecDepth 10000 in
include hΘ in
/-- For chart patches `patch sX C₁.φ O₁ ≤ patch sX C₂.φ O₂`, the coordinate expression in `C₁`
of the restriction of a holomorphic form `t` is the pullback of its coordinate expression in `C₂`
along the derivative of the transition map `C₂.φ ∘ C₁.φ.symm`. -/
theorem Ψ_res_transform {y₁ y₂ : ComplexPoints sX} (C₁ : ChartData sX n Θ y₁)
    (C₂ : ChartData sX n Θ y₂) {p : ℕ} (O₁ O₂ : Opens (EuclideanSpace ℂ (Fin n)))
    (h : patch sX C₁.φ O₁ ≤ patch sX C₂.φ O₂) (t : (Ωan sX p).val.obj (op (patch sX C₂.φ O₂)))
    (y' : patch sX C₁.φ O₁) :
    C₁.Ψ p O₁ ((Ωan sX p).val.presheaf.map (homOfLE h).op t) y' =
      (C₂.Ψ p O₂ t ⟨y'.1, h y'.2⟩).compContinuousLinearMap
        (fderiv ℂ (C₂.φ ∘ C₁.φ.symm) (C₁.φ y')) := by
  obtain ⟨a, rfl⟩ := exists_eq_sum_gen sX hΘ C₂ O₂ t
  have hW : patch sX C₁.φ O₁ ≤ (Opens.map (toSchemeHom sX)).obj C₂.W :=
    h.trans (patch_le_W sX C₂ O₂)
  have hsrc : (patch sX C₁.φ O₁ : Set (ComplexPoints sX)) ⊆ C₂.φ.source :=
    fun x hx => (h hx).1
  erw [map_sum, map_sum, Finset.sum_apply, map_sum, Finset.sum_apply]
  rw [compCLM_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  erw [(Ωan sX p).val.map_smul (homOfLE h).op (a I), an_res, C₁.smul, C₂.smul, Θ_res,
    Ψ_an_gen sX hΘ C₁ C₂ O₁ hW hsrc, Ψ_an_gen sX hΘ C₂ C₂ O₂ (patch_le_W sX C₂ O₂)
      (fun x hx => hx.1), fderiv_comp_symm_self sX (C₂.φ.map_source (h y'.2).1), compCLM_id,
    compCLM_smul']

end Transform

end AnalyticForms

/-! ### The holomorphic de Rham differential -/

section HolomorphicDifferential

open CategoryTheory.Limits TopologicalSpace
open MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

attribute [local implicit_reducible] TopCat.Sheaf

variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}

/-- The alternating forms on `ℂⁿ` form a finite-dimensional space. -/
public lemma finiteDimensional_alt (p : ℕ) :
    FiniteDimensional ℂ (EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ) :=
  (detBasis (n := n) p).finiteDimensional_of_finite

/-- The exterior derivative of a holomorphic form on an open set is holomorphic. -/
public theorem differentiableOn_extDeriv {p : ℕ}
    {ξ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ}
    {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsOpen S) (hξ : DifferentiableOn ℂ ξ S) :
    DifferentiableOn ℂ (extDeriv ξ) S := by
  haveI := finiteDimensional_alt (n := n) p
  have h1 : ContDiffOn ℂ ∞ ξ S := contDiffOn_of_differentiableOn_vec hS hξ
  have h2 : ContDiffOn ℂ ∞ (fun y => fderiv ℂ ξ y) S := h1.fderiv_of_isOpen hS (by simp)
  have h3 : extDeriv ξ = fun y => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ _ _ (fderiv ℂ ξ y) := by
    funext y; rfl
  rw [h3]
  exact ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ _ _).contDiff.comp_contDiffOn h2).differentiableOn (by simp)

/-- A chosen holomorphic extension of the chart expression of a section. -/
@[expose] public noncomputable def holExt {y : ComplexPoints sX} (C : ChartData sX n Θ y) {p : ℕ}
    (O : Opens (EuclideanSpace ℂ (Fin n))) (t : (Ωan sX p).val.obj (op (patch sX C.φ O))) :
    EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ :=
  Classical.choose ((C.range p O (C.Ψ p O t)).1 ⟨t, rfl⟩)

/-- `holExt` is holomorphic on the chart patch and restricts to the chart expression. -/
public lemma holExt_spec {y : ComplexPoints sX} (C : ChartData sX n Θ y) {p : ℕ}
    (O : Opens (EuclideanSpace ℂ (Fin n))) (t : (Ωan sX p).val.obj (op (patch sX C.φ O))) :
    DifferentiableOn ℂ (holExt sX C O t) (C.φ.target ∩ O) ∧
      ∀ y' : patch sX C.φ O, holExt sX C O t (C.φ y') = C.Ψ p O t y' :=
  Classical.choose_spec ((C.range p O (C.Ψ p O t)).1 ⟨t, rfl⟩)

/-- The holomorphic exterior derivative on a chart patch. -/
@[expose] public noncomputable def δP {y : ComplexPoints sX} (C : ChartData sX n Θ y) {p : ℕ}
    (O : Opens (EuclideanSpace ℂ (Fin n))) (t : (Ωan sX p).val.obj (op (patch sX C.φ O))) :
    (Ωan sX (p + 1)).val.obj (op (patch sX C.φ O)) :=
  Classical.choose ((C.range (p + 1) O (fun y' => extDeriv (holExt sX C O t) (C.φ y'))).2
    ⟨extDeriv (holExt sX C O t), differentiableOn_extDeriv (C.φ.open_target.inter O.2)
      (holExt_spec sX C O t).1, fun _ => rfl⟩)

/-- The chart expression of `δP t` is the exterior derivative of the chosen extension. -/
public lemma Ψ_δP {y : ComplexPoints sX} (C : ChartData sX n Θ y) {p : ℕ}
    (O : Opens (EuclideanSpace ℂ (Fin n))) (t : (Ωan sX p).val.obj (op (patch sX C.φ O)))
    (y' : patch sX C.φ O) :
    C.Ψ (p + 1) O (δP sX C O t) y' = extDeriv (holExt sX C O t) (C.φ y') :=
  congrFun (Classical.choose_spec ((C.range (p + 1) O
    (fun y' => extDeriv (holExt sX C O t) (C.φ y'))).2
    ⟨extDeriv (holExt sX C O t), differentiableOn_extDeriv (C.φ.open_target.inter O.2)
      (holExt_spec sX C O t).1, fun _ => rfl⟩)) y'

/-- Any holomorphic extension computes `δP`. -/
public lemma Ψ_δP_of_ext {y : ComplexPoints sX} (C : ChartData sX n Θ y) {p : ℕ}
    (O : Opens (EuclideanSpace ℂ (Fin n))) (t : (Ωan sX p).val.obj (op (patch sX C.φ O)))
    (ξ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ)
    (hξ : ∀ y' : patch sX C.φ O, ξ (C.φ y') = C.Ψ p O t y') (y' : patch sX C.φ O) :
    C.Ψ (p + 1) O (δP sX C O t) y' = extDeriv ξ (C.φ y') := by
  rw [Ψ_δP]
  refine Filter.EventuallyEq.extDeriv_eq ?_
  have hS : IsOpen (C.φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n)))) :=
    C.φ.open_target.inter O.2
  have hv : C.φ y' ∈ C.φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n))) :=
    ⟨C.φ.map_source y'.2.1, y'.2.2⟩
  filter_upwards [hS.mem_nhds hv] with v hv'
  have hmem : C.φ.symm v ∈ patch sX C.φ O :=
    ⟨C.φ.map_target hv'.1, by show C.φ (C.φ.symm v) ∈ O; rw [C.φ.right_inv hv'.1]; exact hv'.2⟩
  have e1 := (holExt_spec sX C O t).2 ⟨_, hmem⟩
  have e2 := hξ ⟨_, hmem⟩
  simp only [C.φ.right_inv hv'.1] at e1 e2
  exact e1.trans e2.symm

variable (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)

set_option maxRecDepth 10000 in
include hΘ in
/-- The exterior derivative on chart patches commutes with restriction between patches. -/
theorem δP_res {y₁ y₂ : ComplexPoints sX} (C₁ : ChartData sX n Θ y₁)
    (C₂ : ChartData sX n Θ y₂) {p : ℕ} (O₁ O₂ : Opens (EuclideanSpace ℂ (Fin n)))
    (h : patch sX C₁.φ O₁ ≤ patch sX C₂.φ O₂) (t : (Ωan sX p).val.obj (op (patch sX C₂.φ O₂))) :
    δP sX C₁ O₁ ((Ωan sX p).val.presheaf.map (homOfLE h).op t) =
      (Ωan sX (p + 1)).val.presheaf.map (homOfLE h).op (δP sX C₂ O₂ t) := by
  set κ := C₂.φ ∘ C₁.φ.symm with hκdef
  set ξ₂ := holExt sX C₂ O₂ t
  have hκ : ContDiffOn ℂ ∞ κ (C₁.φ.target ∩ O₁) := by
    rw [← patch_image sX O₁]
    exact transition_contDiffOn sX C₁.mem C₂.mem (fun x hx => hx.1) (fun x hx => (h hx).1)
  have hκv : ∀ y'' : patch sX C₁.φ O₁, κ (C₁.φ y'') = C₂.φ y''.1 := fun y'' => by
    simp only [hκdef, Function.comp_apply, C₁.φ.left_inv y''.2.1]
  apply C₁.inj (p + 1) O₁
  funext y'
  rw [Ψ_res_transform sX hΘ C₁ C₂ O₁ O₂ h, Ψ_δP]
  have hξ₁ : ∀ y'' : patch sX C₁.φ O₁,
      (ξ₂ (κ (C₁.φ y''))).compContinuousLinearMap (fderiv ℂ κ (C₁.φ y'')) =
        C₁.Ψ p O₁ ((Ωan sX p).val.presheaf.map (homOfLE h).op t) y'' := fun y'' => by
    rw [Ψ_res_transform sX hΘ C₁ C₂ O₁ O₂ h]
    simp only [hκv]
    congr 1
    exact (holExt_spec sX C₂ O₂ t).2 ⟨y''.1, h y''.2⟩
  refine (Ψ_δP_of_ext sX C₁ O₁ _
    (fun v => (ξ₂ (κ v)).compContinuousLinearMap (fderiv ℂ κ v)) hξ₁ y').trans ?_
  have hv₁ : C₁.φ y' ∈ C₁.φ.target ∩ O₁ := ⟨C₁.φ.map_source y'.2.1, y'.2.2⟩
  have hv₂ : C₂.φ y'.1 ∈ C₂.φ.target ∩ O₂ :=
    ⟨C₂.φ.map_source (h y'.2).1, (h y'.2).2⟩
  have hξd : DifferentiableAt ℂ ξ₂ (κ (C₁.φ y')) := by
    rw [hκv]
    exact ((holExt_spec sX C₂ O₂ t).1.differentiableAt
      ((C₂.φ.open_target.inter O₂.2).mem_nhds hv₂))
  rw [extDeriv_pullback (r := ∞) hξd
    (hκ.contDiffAt ((C₁.φ.open_target.inter O₁.2).mem_nhds hv₁)) (by simp), hκv]

/-- The exterior derivative on a chart patch is additive. -/
lemma δP_add {y : ComplexPoints sX} (C : ChartData sX n Θ y) {p : ℕ}
    (O : Opens (EuclideanSpace ℂ (Fin n))) (t t' : (Ωan sX p).val.obj (op (patch sX C.φ O))) :
    δP sX C O (t + t') = δP sX C O t + δP sX C O t' := by
  apply C.inj (p + 1) O
  funext y'
  have hξ : ∀ y'' : patch sX C.φ O, (holExt sX C O t + holExt sX C O t') (C.φ y'') =
      C.Ψ p O (t + t') y'' := fun y'' => by
    rw [map_add, Pi.add_apply, Pi.add_apply, (holExt_spec sX C O t).2, (holExt_spec sX C O t').2]
  rw [Ψ_δP_of_ext sX C O (t + t') _ hξ y', map_add, Pi.add_apply, Ψ_δP, Ψ_δP]
  have hv : C.φ y' ∈ C.φ.target ∩ O := ⟨C.φ.map_source y'.2.1, y'.2.2⟩
  have hS := (C.φ.open_target.inter O.2).mem_nhds hv
  exact extDeriv_add ((holExt_spec sX C O t).1.differentiableAt hS)
    ((holExt_spec sX C O t').1.differentiableAt hS)

/-- `δP` as an additive map. -/
noncomputable def δPHom {y : ComplexPoints sX} (C : ChartData sX n Θ y) (p : ℕ)
    (O : Opens (EuclideanSpace ℂ (Fin n))) :
    (Ωan sX p).val.obj (op (patch sX C.φ O)) →+ (Ωan sX (p + 1)).val.obj (op (patch sX C.φ O)) :=
  AddMonoidHom.mk' (δP sX C O) (δP_add sX C O)

/-- The index type of the basis of chart patches. -/
public abbrev PatchIdx (n : ℕ) := Σ _ : ComplexPoints sX, Opens (EuclideanSpace ℂ (Fin n))

/-- The basis of chart patches. -/
@[expose] public def patchB (C : ∀ y, ChartData sX n Θ y) (i : PatchIdx sX n) : Opens (space sX) :=
  patch sX (C i.1).φ i.2

/-- The chart patches form a basis of the topology of `X^an`. -/
public theorem isBasis_patchB (C : ∀ y, ChartData sX n Θ y) :
    Opens.IsBasis (Set.range (patchB sX C)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  let O : Opens (EuclideanSpace ℂ (Fin n)) :=
    ⟨(C x).φ.target ∩ (C x).φ.symm ⁻¹' U, (C x).φ.isOpen_inter_preimage_symm U.2⟩
  refine ⟨patchB sX C ⟨x, O⟩, ⟨⟨x, O⟩, rfl⟩, ⟨(C x).hy, (C x).φ.map_source (C x).hy, ?_⟩, ?_⟩
  · show (C x).φ.symm ((C x).φ x) ∈ U
    rw [(C x).φ.left_inv (C x).hy]; exact hx
  · rintro y' ⟨hy's, -, hy'U⟩
    have : (C x).φ.symm ((C x).φ y') ∈ U := hy'U
    rwa [(C x).φ.left_inv hy's] at this

include hΘ in
/-- The holomorphic exterior derivative on the basis of chart patches. -/
public noncomputable def δBasis (C : ∀ y, ChartData sX n Θ y) (p : ℕ) :
    (inducedFunctor (patchB sX C)).op ⋙ ((SheafOfModules.toSheaf _).obj (Ωan sX p)).obj ⟶
      (inducedFunctor (patchB sX C)).op ⋙
        ((SheafOfModules.toSheaf _).obj (Ωan sX (p + 1))).obj where
  app i := AddCommGrpCat.ofHom (δPHom sX (C i.unop.1) p i.unop.2)
  naturality i j f := by
    ext t
    exact δP_res sX hΘ (C j.unop.1) (C i.unop.1) j.unop.2 i.unop.2 (leOfHom f.unop.hom) t

include hΘ in
/-- **The holomorphic de Rham differential** `d : Ω^p_an ⟶ Ω^{p+1}_an`. -/
@[expose] public noncomputable def δan (C : ∀ y, ChartData sX n Θ y) (p : ℕ) :
    (SheafOfModules.toSheaf _).obj (Ωan sX p) ⟶ (SheafOfModules.toSheaf _).obj (Ωan sX (p + 1)) :=
  ObjectProperty.homMk (TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C)
    (δBasis sX hΘ C p))

/-- On a chart patch, `δan` is `δP`. -/
public lemma δan_app_patch (C : ∀ y, ChartData sX n Θ y) (p : ℕ) (i : PatchIdx sX n)
    (t : (Ωan sX p).val.obj (op (patchB sX C i))) :
    (δan sX hΘ C p).hom.app (op (patchB sX C i)) t = δP sX (C i.1) i.2 t := by
  have h := TopCat.Sheaf.extend_hom_app _ _ (isBasis_patchB sX C) (δBasis sX hΘ C p) i
  exact ConcreteCategory.congr_hom h t

/-- The exterior derivative on a chart patch squares to zero. -/
lemma δP_δP {y : ComplexPoints sX} (C : ChartData sX n Θ y) {p : ℕ}
    (O : Opens (EuclideanSpace ℂ (Fin n))) (t : (Ωan sX p).val.obj (op (patch sX C.φ O))) :
    δP sX C O (δP sX C O t) = 0 := by
  apply C.inj (p + 2) O
  funext y'
  rw [map_zero, Pi.zero_apply]
  have hS : IsOpen (C.φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n)))) :=
    C.φ.open_target.inter O.2
  rw [Ψ_δP_of_ext sX C O (δP sX C O t) (extDeriv (holExt sX C O t)) (fun y'' => (Ψ_δP sX C O t y'').symm) y']
  haveI := finiteDimensional_alt (n := n) p
  have hv : C.φ y' ∈ C.φ.target ∩ O := ⟨C.φ.map_source y'.2.1, y'.2.2⟩
  have hc : ContDiffOn ℂ ∞ (holExt sX C O t) (C.φ.target ∩ O) :=
    contDiffOn_of_differentiableOn_vec hS (holExt_spec sX C O t).1
  exact extDeriv_extDeriv_apply (hc.contDiffAt (hS.mem_nhds hv)) (by simp)

/-- The holomorphic de Rham differential squares to zero. -/
public theorem δan_comp_δan (C : ∀ y, ChartData sX n Θ y) (p : ℕ) :
    δan sX hΘ C p ≫ δan sX hΘ C (p + 1) = 0 := by
  refine ObjectProperty.hom_ext _ (TopCat.Sheaf.hom_ext _ _ (isBasis_patchB sX C) fun i => ?_)
  ext t
  change (δan sX hΘ C (p + 1)).hom.app _ ((δan sX hΘ C p).hom.app _ t) = 0
  erw [δan_app_patch, δan_app_patch]
  exact δP_δP sX (C i.1) i.2 t

set_option maxRecDepth 10000 in
/-- The holomorphic exterior derivative of an algebraic form is the analytification of its
algebraic exterior derivative. -/
theorem δP_an {y : ComplexPoints sX} (C : ChartData sX n Θ y) (k : ℕ)
    (O : Opens (EuclideanSpace ℂ (Fin n))) (V : X.Opens) (hV : IsAffineOpen V)
    (h : patch sX C.φ O ≤ (Opens.map (toSchemeHom sX)).obj V)
    (s : Γ(sX.relativeDifferentialForms (k : ℤ), V)) :
    δP sX C O (an sX k V (patch sX C.φ O) h s) =
      an sX (k + 1) V (patch sX C.φ O) h (((sX.deRhamComplex).d k (k + 1)).val.app (op V) s) := by
  apply C.inj (k + 1) O
  funext y'
  rw [Ψ_δP]
  letI := MMP.Mori.sectionAlgebra sX V
  have hs : s = (MMP.DeRham.formsAlgEquiv sX k ⟨V, hV⟩).symm
      (MMP.DeRham.formsAlgEquiv sX k ⟨V, hV⟩ s) := (LinearEquiv.symm_apply_apply _ s).symm
  have hds : ((sX.deRhamComplex).d k (k + 1)).val.app (op V) s =
      (MMP.DeRham.formsAlgEquiv sX (k + 1) ⟨V, hV⟩).symm
        (KaehlerDifferential.deRhamDifferential (A := ℂ) k
          (MMP.DeRham.formsAlgEquiv sX k ⟨V, hV⟩ s)) :=
    ((MMP.DeRham.formsAlgEquiv sX (k + 1) ⟨V, hV⟩).symm_apply_apply _).symm.trans
      (congrArg _ (MMP.DeRham.formsAlgEquiv_d sX k ⟨V, hV⟩ s))
  rw [hds]
  refine (C.dcompat k V hV O h (MMP.DeRham.formsAlgEquiv sX k ⟨V, hV⟩ s)
    (holExt sX C O (an sX k V (patch sX C.φ O) h s))
    (holExt_spec sX C O _).1 (fun y'' => ?_) y').symm
  rw [(holExt_spec sX C O _).2 y'', ← hs]

set_option maxRecDepth 10000 in
/-- The holomorphic exterior derivative commutes with analytification of algebraic forms. -/
public theorem δan_unit (C : ∀ y, ChartData sX n Θ y) (k : ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (s : Γ(sX.relativeDifferentialForms (k : ℤ), V)) :
    (δan sX hΘ C k).hom.app (op ((Opens.map (toSchemeHom sX)).obj V))
        ((analytifyModuleUnit sX (sX.relativeDifferentialForms (k : ℤ))).val.app (op V) s) =
      (analytifyModuleUnit sX (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ))).val.app (op V)
        (((sX.deRhamComplex).d k (k + 1)).val.app (op V) s) := by
  refine TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf _).obj (Ωan sX (k + 1))) _ _ _
    fun x hx => ?_
  obtain ⟨_, ⟨i, rfl⟩, hxB, hBV⟩ := (Opens.isBasis_iff_nbhd.mp (isBasis_patchB sX C)) hx
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hBV) x hxB]
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hBV) x hxB]
  congr 1
  have hn := ConcreteCategory.congr_hom ((δan sX hΘ C k).hom.naturality (homOfLE hBV).op)
    ((analytifyModuleUnit sX (sX.relativeDifferentialForms (k : ℤ))).val.app (op V) s)
  refine hn.symm.trans ?_
  erw [δan_app_patch]
  exact δP_an sX (C i.1) k i.2 V hV hBV s

end HolomorphicDifferential

/-! ### The holomorphic Poincaré lemma for sheaves -/

section HolomorphicPoincareSheaf

open CategoryTheory.Limits TopologicalSpace
open MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

attribute [local implicit_reducible] TopCat.Sheaf

variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)

/-- A chart ball around a point inside an open set. -/
public lemma exists_ball_patch {y : ComplexPoints sX} (D : ChartData sX n Θ y)
    (W : Opens (space sX))
    (hyW : y ∈ W) : ∃ r > 0, Metric.ball (D.φ y) r ⊆ D.φ.target ∧
      (patch sX D.φ ⟨Metric.ball (D.φ y) r, Metric.isOpen_ball⟩ : Set (ComplexPoints sX)) ⊆
        (W : Set (ComplexPoints sX)) := by
  have hopen : IsOpen (D.φ.target ∩ D.φ.symm ⁻¹' (W : Set (ComplexPoints sX))) :=
    D.φ.isOpen_inter_preimage_symm W.2
  have hmem : D.φ y ∈ D.φ.target ∩ D.φ.symm ⁻¹' (W : Set (ComplexPoints sX)) :=
    ⟨D.φ.map_source D.hy, by simp [D.φ.left_inv D.hy, hyW]⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen _ hmem
  refine ⟨r, hr, fun v hv => (hball hv).1, ?_⟩
  rintro y' ⟨hy's, hy'b⟩
  have h := (hball hy'b).2
  simp only [Set.mem_preimage, D.φ.left_inv hy's] at h
  exact h

include hΘ in
set_option maxRecDepth 10000 in
/-- **Holomorphic Poincaré lemma**: a closed holomorphic `(k + 1)`-form on `W` is, near each
point of `W`, the exterior derivative of a holomorphic `k`-form. -/
theorem exists_δan_preimage (C : ∀ y, ChartData sX n Θ y) (k : ℕ) (x : space sX)
    (W : Opens (space sX)) (hxW : x ∈ W) (t : (Ωan sX (k + 1)).val.obj (op W))
    (ht : (δan sX hΘ C (k + 1)).hom.app (op W) t = 0) :
    ∃ (B : Opens (space sX)) (_ : x ∈ B) (hBW : B ≤ W) (u : (Ωan sX k).val.obj (op B)),
      (δan sX hΘ C k).hom.app (op B) u = (Ωan sX (k + 1)).val.presheaf.map (homOfLE hBW).op t := by
  obtain ⟨r, hr, hbt, hpW⟩ := exists_ball_patch sX (C x) W hxW
  set O : Opens (EuclideanSpace ℂ (Fin n)) := ⟨Metric.ball ((C x).φ x) r, Metric.isOpen_ball⟩
  have hBW : patchB sX C ⟨x, O⟩ ≤ W := hpW
  set tB := (Ωan sX (k + 1)).val.presheaf.map (homOfLE hBW).op t with htB
  have hδ0 : δP sX (C x) O tB = 0 := by
    have hn := ConcreteCategory.congr_hom ((δan sX hΘ C (k + 1)).hom.naturality (homOfLE hBW).op) t
    erw [δan_app_patch] at hn
    refine hn.trans ?_
    erw [ConcreteCategory.comp_apply, ht]
    exact map_zero _
  set D := C x with hD
  haveI := finiteDimensional_alt (n := n) (k + 1)
  set ξ := holExt sX D O tB
  have hsub : Metric.ball (D.φ x) r ⊆ D.φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n))) :=
    fun v hv => ⟨hbt hv, hv⟩
  have hξc : ContDiffOn ℂ 1 ξ (Metric.ball (D.φ x) r) :=
    contDiffOn_of_differentiableOn_vec Metric.isOpen_ball ((holExt_spec sX D O tB).1.mono hsub)
  have hmemB : ∀ v ∈ Metric.ball (D.φ x) r, D.φ.symm v ∈ patch sX D.φ O := fun v hv =>
    ⟨D.φ.map_target (hbt hv), by
      show D.φ (D.φ.symm v) ∈ Metric.ball (D.φ x) r
      rw [D.φ.right_inv (hbt hv)]; exact hv⟩
  have hd : ∀ v ∈ Metric.ball (D.φ x) r, extDeriv ξ v = 0 := by
    intro v hv
    have h1 := Ψ_δP sX D O tB ⟨_, hmemB v hv⟩
    rw [hδ0, map_zero, Pi.zero_apply] at h1
    simp only [D.φ.right_inv (hbt hv)] at h1
    exact h1.symm
  obtain ⟨η, hηd, hη⟩ := exists_primitive_ball hξc hd
  obtain ⟨u, hu⟩ := (D.range k O (fun y' => η (D.φ y'))).2
    ⟨η, hηd.mono (fun v hv => hv.2), fun _ => rfl⟩
  have hδu : δP sX D O u = tB := by
    apply D.inj (k + 1) O
    funext y'
    rw [Ψ_δP_of_ext sX D O u η (fun y'' => (congrFun hu y'').symm) y', hη _ y'.2.2]
    exact (holExt_spec sX D O tB).2 y'
  refine ⟨patchB sX C ⟨x, O⟩, ⟨D.hy, Metric.mem_ball_self hr⟩, hBW, u, ?_⟩
  erw [δan_app_patch]
  exact hδu

include hΘ in
/-- The holomorphic de Rham complex `Ω^k_an ⟶ Ω^{k+1}_an ⟶ Ω^{k+2}_an` is exact as a sequence
of sheaves. -/
theorem exact_δan (C : ∀ y, ChartData sX n Θ y) (k : ℕ) :
    (ShortComplex.mk (δan sX hΘ C k) (δan sX hΘ C (k + 1)) (δan_comp_δan sX hΘ C k)).Exact := by
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{0})
    (X := space sX) _).2 fun x => ?_
  rw [ShortComplex.ab_exact_iff]
  intro e he
  obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ e
  have he' := (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    (δan sX hΘ C (k + 1)).hom t).symm.trans he
  let P : TopCat.Presheaf AddCommGrpCat.{0} (space sX) :=
    ((SheafOfModules.toSheaf (ringCatSheaf sX)).obj (Ωan sX (k + 1 + 1))).obj
  have he2 : P.germ U x hxU ((δan sX hΘ C (k + 1)).hom.app (op U) t) =
      P.germ U x hxU 0 := he'.trans (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq P x hxU hxU _ _ he2
  have hWU : W ≤ U := leOfHom iU
  set tW := (Ωan sX (k + 1)).val.presheaf.map (homOfLE hWU).op t
  have htW : (δan sX hΘ C (k + 1)).hom.app (op W) tW = 0 := by
    have hiU : iU = homOfLE hWU := Subsingleton.elim _ _
    have hiV : iV = homOfLE hWU := Subsingleton.elim _ _
    rw [hiU, hiV, map_zero] at hW
    exact (ConcreteCategory.congr_hom
      ((δan sX hΘ C (k + 1)).hom.naturality (homOfLE hWU).op) t).trans hW
  obtain ⟨B, hxB, hBW, u, hu⟩ := exists_δan_preimage sX hΘ C k x W hxW tW htW
  let P0 : TopCat.Presheaf AddCommGrpCat.{0} (space sX) :=
    ((SheafOfModules.toSheaf (ringCatSheaf sX)).obj (Ωan sX k)).obj
  refine ⟨P0.germ B x hxB u, ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply B x hxB (δan sX hΘ C k).hom u).trans ?_
  erw [hu, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  rfl

/-- The constant `0`-form `c` on a chart patch. -/
@[expose] public noncomputable def εP {y : ComplexPoints sX} (D : ChartData sX n Θ y)
    (O : Opens (EuclideanSpace ℂ (Fin n))) (c : ℂ) :
    (Ωan sX 0).val.obj (op (patch sX D.φ O)) :=
  Classical.choose ((D.range 0 O (fun _ =>
    ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) c)).2
    ⟨fun _ => ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) c,
      differentiableOn_const _, fun _ => rfl⟩)

/-- The chart expression of `εP c` is the constant `0`-form `c`. -/
public lemma Ψ_εP {y : ComplexPoints sX} (D : ChartData sX n Θ y)
    (O : Opens (EuclideanSpace ℂ (Fin n))) (c : ℂ) :
    D.Ψ 0 O (εP sX D O c) =
      fun _ => ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) c :=
  Classical.choose_spec ((D.range 0 O (fun _ =>
    ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) c)).2
    ⟨fun _ => ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) c,
      differentiableOn_const _, fun _ => rfl⟩)

/-- The constant `0`-form on a chart patch is additive in the constant. -/
lemma εP_add {y : ComplexPoints sX} (D : ChartData sX n Θ y)
    (O : Opens (EuclideanSpace ℂ (Fin n))) (c c' : ℂ) :
    εP sX D O (c + c') = εP sX D O c + εP sX D O c' := by
  apply D.inj 0 O
  rw [map_add, Ψ_εP, Ψ_εP, Ψ_εP]
  funext y'
  ext v
  simp

include hΘ in
/-- The restriction of the constant `0`-form `c` to a smaller patch is the constant form `c`. -/
lemma εP_res {y₁ y₂ : ComplexPoints sX} (C₁ : ChartData sX n Θ y₁) (C₂ : ChartData sX n Θ y₂)
    (O₁ O₂ : Opens (EuclideanSpace ℂ (Fin n))) (h : patch sX C₁.φ O₁ ≤ patch sX C₂.φ O₂) (c : ℂ) :
    (Ωan sX 0).val.presheaf.map (homOfLE h).op (εP sX C₂ O₂ c) = εP sX C₁ O₁ c := by
  apply C₁.inj 0 O₁
  funext y'
  rw [Ψ_res_transform sX hΘ C₁ C₂ O₁ O₂ h, Ψ_εP, Ψ_εP]
  ext v
  simp

/-- The constant presheaf `ℂ` on `X^an`. -/
public noncomputable abbrev constPre : TopCat.Presheaf AddCommGrpCat.{0} (space sX) :=
  (Functor.const (Opens (space sX))ᵒᵖ).obj (AddCommGrpCat.of ℂ)

include hΘ in
/-- The constant forms on the basis of chart patches. -/
public noncomputable def εBasis (C : ∀ y, ChartData sX n Θ y) :
    (inducedFunctor (patchB sX C)).op ⋙ constPre sX ⟶
      (inducedFunctor (patchB sX C)).op ⋙ ((SheafOfModules.toSheaf _).obj (Ωan sX 0)).obj where
  app i := AddCommGrpCat.ofHom (AddMonoidHom.mk' (εP sX (C i.unop.1) i.unop.2)
    (εP_add sX (C i.unop.1) i.unop.2))
  naturality i j f := by
    ext c
    exact (εP_res sX hΘ (C j.unop.1) (C i.unop.1) j.unop.2 i.unop.2 (leOfHom f.unop.hom) c).symm

include hΘ in
/-- **The inclusion of the constants** `ℂ_{X^an} ⟶ Ω⁰_an`. -/
@[expose] public noncomputable def εan (C : ∀ y, ChartData sX n Θ y) :
    (constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of ℂ) ⟶ (SheafOfModules.toSheaf _).obj (Ωan sX 0) :=
  ⟨sheafifyLift (Opens.grothendieckTopology (space sX))
    (TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C))
    ((SheafOfModules.toSheaf _).obj (Ωan sX 0)).property⟩

/-- Precomposed with sheafification of the constant presheaf, `εan` is the morphism determined
by the constant forms on the basis of chart patches. -/
lemma toSheafify_εan (C : ∀ y, ChartData sX n Θ y) :
    toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX) ≫ (εan sX hΘ C).hom =
      TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C) :=
  toSheafify_sheafifyLift _ _ _

/-- On a chart patch the presheaf map of constants is `εP`. -/
public lemma εPre_app_patch (C : ∀ y, ChartData sX n Θ y) (i : PatchIdx sX n) (c : ℂ) :
    (TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)).app
      (op (patchB sX C i)) c = εP sX (C i.1) i.2 c :=
  ConcreteCategory.congr_hom (TopCat.Sheaf.extend_hom_app _ _ (isBasis_patchB sX C)
    (εBasis sX hΘ C) i) c

/-- The exterior derivative of a constant form is zero. -/
lemma extDeriv_const_zero {p : ℕ} (a : EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ)
    (v : EuclideanSpace ℂ (Fin n)) : extDeriv (fun _ => a) v = 0 := by
  have h : fderiv ℂ (fun _ : EuclideanSpace ℂ (Fin n) => a) v = 0 := fderiv_const_apply a
  rw [extDeriv, h, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero]

/-- The exterior derivative of a constant `0`-form on a chart patch is zero. -/
lemma δP_εP {y : ComplexPoints sX} (D : ChartData sX n Θ y)
    (O : Opens (EuclideanSpace ℂ (Fin n))) (c : ℂ) : δP sX D O (εP sX D O c) = 0 := by
  apply D.inj 1 O
  funext y'
  rw [Ψ_δP_of_ext sX D O _ (fun _ =>
    ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) c)
    (fun y'' => by rw [Ψ_εP]) y', extDeriv_const_zero, map_zero, Pi.zero_apply]

/-- The constants are killed by the holomorphic exterior derivative. -/
public theorem εan_comp_δan (C : ∀ y, ChartData sX n Θ y) : εan sX hΘ C ≫ δan sX hΘ C 0 = 0 := by
  refine ObjectProperty.hom_ext _ ?_
  change (εan sX hΘ C).hom ≫ (δan sX hΘ C 0).hom = 0
  refine sheafify_hom_ext _ _ _ ((SheafOfModules.toSheaf _).obj (Ωan sX 1)).property ?_
  erw [reassoc_of% (toSheafify_εan sX hΘ C), Limits.comp_zero]
  refine TopCat.Sheaf.hom_ext _ _ (isBasis_patchB sX C) fun i => ?_
  ext c
  change (δan sX hΘ C 0).hom.app _ (_ ) = 0
  erw [εPre_app_patch, δan_app_patch]
  exact δP_εP sX (C i.1) i.2 c

/-- On stalks, `εan` composed with sheafification of the constants is the basis map. -/
public lemma stalk_εan (C : ∀ y, ChartData sX n Θ y) (x : space sX) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX)) ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map (εan sX hΘ C).hom =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      (TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)) :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map_comp _ _).symm.trans
    (congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map (toSheafify_εan sX hΘ C))

/-- The constant `0`-form `c` over `U` restricts to the constant `0`-form `c` over `W ≤ U`. -/
lemma εPre_res (C : ∀ y, ChartData sX n Θ y) {U W : Opens (space sX)} (h : W ≤ U) (c : ℂ) :
    ((SheafOfModules.toSheaf _).obj (Ωan sX 0)).obj.map (homOfLE h).op
      ((TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)).app
        (op U) c) =
    (TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)).app
      (op W) c :=
  (ConcreteCategory.congr_hom ((TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C)
    (εBasis sX hΘ C)).naturality (homOfLE h).op) c).symm

/-- The inclusion of the constants `ℂ_{X^an} ⟶ Ω⁰_an` is a monomorphism. -/
theorem mono_εan (C : ∀ y, ChartData sX n Θ y) : Mono (εan sX hΘ C) := by
  have hm : ∀ x : space sX, Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      (εan sX hΘ C).hom) := by
    intro x
    rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro w hw
    haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{0}
      (constPre sX)
    have hsurj := ((ConcreteCategory.isIso_iff_bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX)))).1 inferInstance).2
    obtain ⟨w', rfl⟩ := hsurj w
    obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (constPre sX) w'
    let P : TopCat.Presheaf AddCommGrpCat.{0} (space sX) :=
      ((SheafOfModules.toSheaf _).obj (Ωan sX 0)).obj
    let εPre := TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)
    have h1 := ConcreteCategory.congr_hom (stalk_εan sX hΘ C x) ((constPre sX).germ U x hxU a)
    have h2 : P.germ U x hxU (εPre.app (op U) a) = P.germ U x hxU 0 :=
      ((TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU εPre a).symm.trans
        (h1.symm.trans ((ConcreteCategory.comp_apply _ _ _).trans hw))).trans
          (_root_.map_zero _).symm
    obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq P x hxU hxU _ _ h2
    obtain ⟨_, ⟨i, rfl⟩, hxB, hBW⟩ := (Opens.isBasis_iff_nbhd.mp (isBasis_patchB sX C)) hxW
    have hBU : patchB sX C i ≤ U := hBW.trans (leOfHom iU)
    have hiU : iU = homOfLE (leOfHom iU) := Subsingleton.elim _ _
    have h3 : εPre.app (op (patchB sX C i)) a = 0 := by
      rw [← εPre_res sX hΘ C hBU]
      have e : homOfLE hBU = homOfLE hBW ≫ iU := Subsingleton.elim _ _
      rw [e, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hW, map_zero, map_zero]
    erw [εPre_app_patch] at h3
    have h4 : (C i.1).Ψ 0 i.2 (εP sX (C i.1) i.2 a) = 0 := by
      erw [h3]; exact map_zero _
    have h5 := congrFun ((Ψ_εP sX (C i.1) i.2 a).symm.trans h4) ⟨x, hxB⟩
    have ha : (show ℂ from a) = 0 := by
      have := congrArg (fun f => f Fin.elim0) h5
      simpa using this
    have : (constPre sX).germ U x hxU a = 0 := by
      rw [show a = 0 from ha]; exact _root_.map_zero _
    rw [this]; exact _root_.map_zero _
  exact TopCat.Presheaf.mono_of_stalk_mono (C := AddCommGrpCat.{0}) (X := space sX)
    (εan sX hΘ C)

/-- A `0`-form with vanishing exterior derivative has vanishing derivative. -/
public lemma fderiv_eq_zero_of_extDeriv_eq_zero
    {ξ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin 0]→L[ℂ] ℂ}
    {v : EuclideanSpace ℂ (Fin n)} (h : extDeriv ξ v = 0) : fderiv ℂ ξ v = 0 := by
  ext w u
  have h1 := congrArg (fun f => f ![w]) h
  simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_one,
    Fin.val_zero, pow_zero, one_smul] at h1
  have hu : u = Fin.removeNth 0 ![w] := Subsingleton.elim _ _
  rw [hu]
  simpa using h1

include hΘ in
set_option maxRecDepth 10000 in
/-- A holomorphic function on `W` with zero differential is constant on a chart patch around each
point of `W`. -/
theorem exists_εP_eq (C : ∀ y, ChartData sX n Θ y) (x : space sX)
    (W : Opens (space sX)) (hxW : x ∈ W) (t : (Ωan sX 0).val.obj (op W))
    (ht : (δan sX hΘ C 0).hom.app (op W) t = 0) :
    ∃ (i : PatchIdx sX n) (_ : x ∈ patchB sX C i) (hBW : patchB sX C i ≤ W) (c : ℂ),
      (Ωan sX 0).val.presheaf.map (homOfLE hBW).op t = εP sX (C i.1) i.2 c := by
  obtain ⟨r, hr, hbt, hpW⟩ := exists_ball_patch sX (C x) W hxW
  set O : Opens (EuclideanSpace ℂ (Fin n)) := ⟨Metric.ball ((C x).φ x) r, Metric.isOpen_ball⟩
  have hBW : patchB sX C ⟨x, O⟩ ≤ W := hpW
  set tB := (Ωan sX 0).val.presheaf.map (homOfLE hBW).op t with htB
  have hδ0 : δP sX (C x) O tB = 0 := by
    have hn := ConcreteCategory.congr_hom ((δan sX hΘ C 0).hom.naturality (homOfLE hBW).op) t
    erw [δan_app_patch] at hn
    refine hn.trans ?_
    erw [ConcreteCategory.comp_apply, ht]
    exact map_zero _
  set D := C x with hD
  set ξ := holExt sX D O tB
  have hsub : Metric.ball (D.φ x) r ⊆ D.φ.target ∩ (O : Set (EuclideanSpace ℂ (Fin n))) :=
    fun v hv => ⟨hbt hv, hv⟩
  have hξd : DifferentiableOn ℂ ξ (Metric.ball (D.φ x) r) :=
    (holExt_spec sX D O tB).1.mono hsub
  have hmemB : ∀ v ∈ Metric.ball (D.φ x) r, D.φ.symm v ∈ patch sX D.φ O := fun v hv =>
    ⟨D.φ.map_target (hbt hv), by
      show D.φ (D.φ.symm v) ∈ Metric.ball (D.φ x) r
      rw [D.φ.right_inv (hbt hv)]; exact hv⟩
  have hd : ∀ v ∈ Metric.ball (D.φ x) r, fderiv ℂ ξ v = 0 := by
    intro v hv
    have h1 := Ψ_δP sX D O tB ⟨_, hmemB v hv⟩
    rw [hδ0, map_zero, Pi.zero_apply] at h1
    simp only [D.φ.right_inv (hbt hv)] at h1
    exact fderiv_eq_zero_of_extDeriv_eq_zero h1.symm
  have hconst : ∀ v ∈ Metric.ball (D.φ x) r, ξ v = ξ (D.φ x) := by
    intro v hv
    refine (convex_ball _ _).is_const_of_fderivWithin_eq_zero hξd (fun z hz => ?_) hv
      (Metric.mem_ball_self hr)
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hz]
    exact hd z hz
  refine ⟨⟨x, O⟩, ⟨D.hy, Metric.mem_ball_self hr⟩, hBW, ξ (D.φ x) Fin.elim0, ?_⟩
  apply D.inj 0 O
  rw [Ψ_εP]
  funext y'
  refine ((holExt_spec sX D O tB).2 y').symm.trans ((hconst _ y'.2.2).trans ?_)
  ext u
  simp [Subsingleton.elim u Fin.elim0]

include hΘ in
/-- The sequence `ℂ_{X^an} ⟶ Ω⁰_an ⟶ Ω¹_an` is exact as a sequence of sheaves. -/
theorem exact_εan (C : ∀ y, ChartData sX n Θ y) :
    (ShortComplex.mk (εan sX hΘ C) (δan sX hΘ C 0) (εan_comp_δan sX hΘ C)).Exact := by
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{0})
    (X := space sX) _).2 fun x => ?_
  rw [ShortComplex.ab_exact_iff]
  intro e he
  obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ e
  have he' := (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    (δan sX hΘ C 0).hom t).symm.trans he
  let P : TopCat.Presheaf AddCommGrpCat.{0} (space sX) :=
    ((SheafOfModules.toSheaf (ringCatSheaf sX)).obj (Ωan sX (0 + 1))).obj
  have he2 : P.germ U x hxU ((δan sX hΘ C 0).hom.app (op U) t) =
      P.germ U x hxU 0 := he'.trans (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq P x hxU hxU _ _ he2
  have hWU : W ≤ U := leOfHom iU
  set tW := (Ωan sX 0).val.presheaf.map (homOfLE hWU).op t
  have htW : (δan sX hΘ C 0).hom.app (op W) tW = 0 := by
    have hiU : iU = homOfLE hWU := Subsingleton.elim _ _
    have hiV : iV = homOfLE hWU := Subsingleton.elim _ _
    rw [hiU, hiV, map_zero] at hW
    exact (ConcreteCategory.congr_hom
      ((δan sX hΘ C 0).hom.naturality (homOfLE hWU).op) t).trans hW
  obtain ⟨i, hxB, hBW, c, hc⟩ := exists_εP_eq sX hΘ C x W hxW tW htW
  let εPre := TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)
  refine ⟨(TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
    (toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX))
      ((constPre sX).germ (patchB sX C i) x hxB c), ?_⟩
  have h1 := ConcreteCategory.congr_hom (stalk_εan sX hΘ C x)
    ((constPre sX).germ (patchB sX C i) x hxB c)
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans (h1.trans ?_)
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hxB εPre c).trans ?_
  erw [εPre_app_patch, ← hc, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  rfl

end HolomorphicPoincareSheaf

section DeRhamComparison

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MMP.Analytic

namespace GodPull

section CompLift

open MMP.Analytic.CokernelCoresolution

universe v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
  {D : Type u} [Category.{v} D] [Preadditive D] [HasCokernels D]
  {E : Type u} [Category.{v} E] [Preadditive E] [HasCokernels E]
  {G₁ : C ⥤ C} {η₁ : 𝟭 C ⟶ G₁} {G₂ : D ⥤ D} {η₂ : 𝟭 D ⟶ G₂} {G₃ : E ⥤ E} {η₃ : 𝟭 E ⟶ G₃}
  {P₁ : D ⥤ C} {P₂ : E ⥤ D} [P₁.PreservesZeroMorphisms] [P₂.PreservesZeroMorphisms]
  (Λ₁ : Lift G₁ η₁ G₂ η₂ P₁) (Λ₂ : Lift G₂ η₂ G₃ η₃ P₂) (Λ₁₂ : Lift G₁ η₁ G₃ η₃ (P₂ ⋙ P₁))
  (hcomp : ∀ {A : C} {B : D} {B' : E} (φ : A ⟶ P₁.obj B) (ψ : B ⟶ P₂.obj B'),
    Λ₁.lift φ ≫ P₁.map (Λ₂.lift ψ) = Λ₁₂.lift (φ ≫ P₁.map ψ))

include hcomp in
/-- If the lifts `Λ₁`, `Λ₂` compose to `Λ₁₂`, then so do the induced maps on each stage of the
cokernel coresolutions. -/
theorem homX_comp_lift {A : C} {B : D} {B' : E} (φ : A ⟶ P₁.obj B) (ψ : B ⟶ P₂.obj B') (n : ℕ) :
    homX Λ₁ φ n ≫ P₁.map (homX Λ₂ ψ n) = homX Λ₁₂ (φ ≫ P₁.map ψ) n := by
  suffices H : ∀ n, (stageHom Λ₁ φ n).1 ≫ P₁.map (stageHom Λ₂ ψ n).1 =
      (stageHom Λ₁₂ (φ ≫ P₁.map ψ) n).1 ∧
      homX Λ₁ φ n ≫ P₁.map (homX Λ₂ ψ n) = homX Λ₁₂ (φ ≫ P₁.map ψ) n from (H n).2
  intro n
  induction n with
  | zero => exact ⟨rfl, hcomp φ ψ⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    change Λ₁.lift (cokerDesc (stageHom Λ₁ φ n)) ≫ P₁.map (Λ₂.lift (cokerDesc (stageHom Λ₂ ψ n))) =
      Λ₁₂.lift (cokerDesc (stageHom Λ₁₂ (φ ≫ P₁.map ψ) n))
    rw [hcomp]
    congr 1
    refine coequalizer.hom_ext ?_
    change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
    rw [π_cokerDesc_assoc, ← P₁.map_comp, π_cokerDesc, π_cokerDesc]
    change homX Λ₁ φ n ≫ P₁.map (homX Λ₂ ψ n ≫ P₂.map (cokernel.π _)) =
      homX Λ₁₂ (φ ≫ P₁.map ψ) n ≫ (P₂ ⋙ P₁).map (cokernel.π _)
    rw [P₁.map_comp, ← Category.assoc, ih.2]
    rfl

end CompLift

section GodComp

open TopCat TopCat.Presheaf

attribute [local implicit_reducible] TopCat.Sheaf

variable {T T' T'' : TopCat.{u}} (f : T' ⟶ T) (f' : T'' ⟶ T')

/-- The Godement lifts along `f` and `f'` compose to the Godement lift along `f' ≫ f`. -/
theorem godementLiftHom_comp {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'} {B' : TopCat.Sheaf AddCommGrpCat.{u} T''}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B)
    (ψ : B ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f').obj B') :
    godementLiftHom f φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map (godementLiftHom f' ψ) =
      (godementLiftHom (f' ≫ f) (φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map ψ) :) := by
  refine sheafHom_ext fun U s => funext fun z => ?_
  change B'.presheaf.stalkPushforward AddCommGrpCat f' z
      ((stalkFunctor AddCommGrpCat (f' z)).map ψ.hom
        (B.presheaf.stalkPushforward AddCommGrpCat f (f' z)
          ((stalkFunctor AddCommGrpCat (f (f' z))).map φ.hom (s ⟨f (f' z), z.2⟩)))) =
    B'.presheaf.stalkPushforward AddCommGrpCat (f' ≫ f) z
      ((stalkFunctor AddCommGrpCat ((f' ≫ f) z)).map
        (φ.hom ≫ (Presheaf.pushforward AddCommGrpCat f).map ψ.hom) (s ⟨(f' ≫ f) z, z.2⟩))
  rw [TopCat.Presheaf.stalkPushforward.comp]
  erw [CategoryTheory.Functor.map_comp]
  simp only [ConcreteCategory.comp_apply]
  exact congrArg (B'.presheaf.stalkPushforward AddCommGrpCat f' z)
    (stalkFunctor_map_pushforward_comp_stalkPushforward_apply f ψ.hom (f' z) _).symm

/-- The Godement lifts along a composite, read through the composite of pushforwards. -/
noncomputable def compLift : CokernelCoresolution.Lift (godementFunctor T) (godementUnit T) (godementFunctor T'')
    (godementUnit T'') (TopCat.Sheaf.pushforward AddCommGrpCat f' ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat f) where
  lift φ := godementLiftHom (f' ≫ f) φ
  app_comp_lift φ := (godementPullbackLift (f' ≫ f)).app_comp_lift φ
  lift_precomp a φ := (godementPullbackLift (f' ≫ f)).lift_precomp a φ
  lift_postcomp φ b := (godementPullbackLift (f' ≫ f)).lift_postcomp φ b

/-- The maps of Godement resolutions induced along `f` and `f'` compose to the map induced along
`f' ≫ f`, in each degree. -/
theorem complexHom_comp {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'} {B' : TopCat.Sheaf AddCommGrpCat.{u} T''}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B)
    (ψ : B ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f').obj B') (n : ℕ) :
    CokernelCoresolution.homX (godementPullbackLift f) φ n ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f).map
          (CokernelCoresolution.homX (godementPullbackLift f') ψ n) =
      CokernelCoresolution.homX (godementPullbackLift (f' ≫ f))
        (φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map ψ) n :=
  homX_comp_lift (godementPullbackLift f) (godementPullbackLift f') (compLift f f')
    (fun φ ψ => godementLiftHom_comp f f' φ ψ) φ ψ n

end GodComp

section HypComp

open TopCat TopCat.Presheaf

variable {T T' T'' : TopCat.{u}} (f : T' ⟶ T) (f' : T'' ⟶ T')

/-- The map of Godement section complexes induced by `ψ : A ⟶ f_* B`. -/
noncomputable def secHom {A : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B) :
    (godementSections T).obj A ⟶ (godementSections T').obj B :=
  (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).map
    (((globalSections T).mapHomologicalComplex _).map
      (CokernelCoresolution.complexHom (godementPullbackLift f) ψ))

/-- The maps of Godement section complexes induced along `f` and `f'` compose to the map
induced along `f' ≫ f`. -/
theorem secHom_comp {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'} {B' : TopCat.Sheaf AddCommGrpCat.{u} T''}
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B)
    (χ : B ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f').obj B') :
    secHom f ψ ≫ secHom f' χ =
      secHom (f' ≫ f) (ψ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map χ) := by
  unfold secHom
  refine (Functor.map_comp _ _ _).symm.trans (congrArg _ ?_)
  ext n : 1
  exact (Functor.map_comp (globalSections T) _ _).symm.trans
    (congrArg (globalSections T).map (complexHom_comp f f' ψ χ n))

/-- The pullback map on Godement sections followed by the map induced by `b : f⁻¹ F ⟶ L` is the
map of section complexes induced by the adjoint `F ⟶ f_* L` of `b`. -/
theorem godementSectionsPullback_comp_map (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    {L : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (b : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F ⟶ L) :
    godementSectionsPullback f F ≫ (godementSections T').map b =
      secHom f ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f).map b) := by
  unfold godementSectionsPullback secHom
  refine (Functor.map_comp _ _ _).symm.trans (congrArg _ ?_)
  have h := CokernelCoresolution.complexFunctor_map_comp_complexHom (godementPullbackLift f)
    (𝟙 F) b ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat f).map b) (by rw [Category.id_comp])
  rw [CategoryTheory.Functor.map_id] at h
  have h' := (Category.id_comp _).symm.trans h
  ext n : 1
  exact (Functor.map_comp (globalSections T) _ _).symm.trans
    (congrArg (globalSections T).map (congrArg (fun φ => φ.f n) h'.symm))

/-- The map on Godement hypercohomology induced by `φ` is the map on homology of the total
complexes of the Godement sections bicomplexes. -/
lemma hyp_map_eq {S : TopCat.{u}} {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} S) ℤ}
    (φ : K ⟶ L) (n : ℤ) :
    (hypercohomology S n).map φ = (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (((godementSections S).mapHomologicalComplex _).map φ) (ComplexShape.up ℤ)) n :) :=
  eq_of_heq HEq.rfl

/-- The pullback map on Godement hypercohomology is the map on homology of the total complexes
induced by `godementSectionsDoubleComplexPullback`. -/
lemma hpb_eq (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) (n : ℤ) :
    hypercohomologyPullback f K n = (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (godementSectionsDoubleComplexPullback f K) (ComplexShape.up ℤ)) n :) :=
  eq_of_heq HEq.rfl

end HypComp

section BridgeP

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] globalSections_additive

variable (T : TopCat.{u})

/-- The derived-functor unit `Γ(T, M) ⟶ RΓ(T, M)`. -/
noncomputable abbrev Uc (M : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) :=
  (Functor.mapCochainComplexPlusDerivedUnit (globalSections T)).app M

/-- On a bounded below complex of flasque sheaves, the derived-functor unit
`Γ(T, M) ⟶ RΓ(T, M)` is an isomorphism. -/
theorem isIso_Uc (M : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T))
    (hM : ∀ n, (M.obj.X n).IsFlasque) : IsIso (Uc T M) := by
  have hu : IsIso ((globalSections T).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient _).obj M)) :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun n =>
      rightAcyclic_of_isFlasque T _ (hM n)
  have h1 : IsIso ((DerivedCategory.Plus.quotientCompQhIso AddCommGrpCat.{u}).inv.app
      ((globalSections T).mapCochainComplexPlus.obj M)) := inferInstance
  have h3 : IsIso ((globalSections T).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso _).hom.app M)) := inferInstance
  rw [Uc, Functor.mapCochainComplexPlusDerivedUnit_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (@IsIso.comp_isIso _ _ _ _ _ _ _ hu h3)

/-- The isomorphism between derived hypercohomology `H^m(RΓ(T, L))` and the cohomology of the
total complex of Godement sections of `L`. -/
public noncomputable def hypercohomologyIsoGodementTotal
    (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).obj
      ((globalSections T).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L)) ≅
    ((godementSectionsDoubleComplex T L.obj).total (ComplexShape.up ℤ)).homology m :=
  haveI := isIso_Uc T ((godTotPlus T).obj L) fun n => by
    obtain ⟨a, ha⟩ := L.2
    exact isFlasque_total_godDC T L.obj a n
  ((globalSections T).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).mapIso
    (asIso (DerivedCategory.Plus.Q.map ((compNatPlus T).app L))) ≪≫
  (asIso ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
    (Uc T ((godTotPlus T).obj L)))).symm ≪≫
  (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} m).app
    ((globalSections T).mapCochainComplexPlus.obj ((godTotPlus T).obj L)).obj ≪≫
  (HomologicalComplex.homologyFunctor _ _ m).mapIso (gammaTotIso T L)

/-- The isomorphism `hypercohomologyIsoGodementTotal` is the composite of `RΓ` applied to the
comparison `L ⟶ Tot G(L)`, the inverse of the derived-functor unit on `Tot G(L)`, and
`gammaTotIso`. -/
theorem hypercohomologyIsoGodementTotal_hom_eq
    (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)) (m : ℤ)
    [IsIso ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
      (Uc T ((godTotPlus T).obj L)))] :
    (hypercohomologyIsoGodementTotal T L m).hom =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
          ((globalSections T).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map ((compNatPlus T).app L))) ≫
        CategoryTheory.inv ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
          (Uc T ((godTotPlus T).obj L))) ≫
        (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} m).hom.app
          ((globalSections T).mapCochainComplexPlus.obj ((godTotPlus T).obj L)).obj ≫
        HomologicalComplex.homologyMap (gammaTotIso T L).hom m :=
  rfl

/-- `hypercohomologyIsoGodementTotal` is natural in the complex. -/
public theorem hypercohomologyIsoGodementTotal_hom_naturality
    {L L' : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)} (φ : L ⟶ L') (m : ℤ) :
    ((globalSections T).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
          (DerivedCategory.Plus.Q.map φ) ≫ (hypercohomologyIsoGodementTotal T L' m).hom =
      (hypercohomologyIsoGodementTotal T L m).hom ≫
        HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (((godementSections T).mapHomologicalComplex _).map φ.hom) (ComplexShape.up ℤ)) m := by
  haveI := isIso_Uc T ((godTotPlus T).obj L) fun n => by
    obtain ⟨a, ha⟩ := L.2
    exact isFlasque_total_godDC T L.obj a n
  haveI := isIso_Uc T ((godTotPlus T).obj L') fun n => by
    obtain ⟨a, ha⟩ := L'.2
    exact isFlasque_total_godDC T L'.obj a n
  set F := (globalSections T).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m
  set H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m
  have hc := (compNatPlus T).naturality φ
  have hU := (Functor.mapCochainComplexPlusDerivedUnit (globalSections T)).naturality
    ((godTotPlus T).map φ)
  have hU' : H.map ((globalSections T).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map ((godTotPlus T).map φ))) ≫
      CategoryTheory.inv (H.map (Uc T ((godTotPlus T).obj L'))) =
      CategoryTheory.inv (H.map (Uc T ((godTotPlus T).obj L))) ≫
        H.map (DerivedCategory.Plus.Q.map ((globalSections T).mapCochainComplexPlus.map
          ((godTotPlus T).map φ))) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← H.map_comp, IsIso.comp_inv_eq, ← H.map_comp]
    exact congrArg H.map hU.symm
  have hρ := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} m).hom.naturality
    ((globalSections T).mapCochainComplexPlus.map ((godTotPlus T).map φ)).hom
  have hG := congrArg (fun χ => HomologicalComplex.homologyMap χ m) (gammaTotIso_naturality T φ)
  simp only [HomologicalComplex.homologyMap_comp] at hG
  have hc' : F.map (DerivedCategory.Plus.Q.map φ) ≫
      F.map (DerivedCategory.Plus.Q.map ((compNatPlus T).app L')) =
      F.map (DerivedCategory.Plus.Q.map ((compNatPlus T).app L)) ≫
        H.map ((globalSections T).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map ((godTotPlus T).map φ))) := by
    rw [← F.map_comp, ← Functor.map_comp]
    exact (congrArg (fun χ => F.map (DerivedCategory.Plus.Q.map χ)) hc).trans
      (by rw [Functor.map_comp, F.map_comp]; rfl)
  simp only [hypercohomologyIsoGodementTotal, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% hc', reassoc_of% hU']
  congr 2
  exact (reassoc_of% hρ) _ |>.trans (congrArg (_ ≫ ·) hG)

end BridgeP

section Chi

attribute [local implicit_reducible] MMP.Analytic.godementResolution
  MMP.Analytic.CokernelCoresolution.complexFunctor

variable {T T' : TopCat.{u}} (f : T' ⟶ T)

/-- The isomorphism `mapHomologicalComplexExtendIso` is natural in the complex. -/
theorem mapHCExtendIso_hom_naturality {C D : Type*} [Category* C] [Category* D] [HasZeroObject C]
    [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] {K K' : CochainComplex C ℕ} (φ : K ⟶ K') :
    (HomologicalComplex.mapHomologicalComplexExtendIso F K ComplexShape.embeddingUpNat).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) =
      HomologicalComplex.extendMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
          ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso F K'
          ComplexShape.embeddingUpNat).hom := by
  rw [← cancel_mono (HomologicalComplex.mapHomologicalComplexExtendIso F K'
      ComplexShape.embeddingUpNat).inv, Category.assoc,
    HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality, Iso.hom_inv_id_assoc,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The comparison of Godement resolutions `G(f_* A) ⟶ f_* G(A)`, extended to `ℤ`. -/
noncomputable def colχ (A : TopCat.Sheaf AddCommGrpCat.{u} T') :
    ((godementResolution T).obj ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj A)).extend ComplexShape.embeddingUpNat ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((godementResolution T').obj A).extend ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap (CokernelCoresolution.complexHom (godementPullbackLift f)
      (𝟙 ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj A))) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
      ((godementResolution T').obj A) ComplexShape.embeddingUpNat).hom

/-- The comparison `G(f_* A) ⟶ f_* G(A)` is natural in `A`. -/
theorem colχ_naturality {A A' : TopCat.Sheaf AddCommGrpCat.{u} T'} (a : A ⟶ A') :
    HomologicalComplex.extendMap ((godementResolution T).map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map a))
        ComplexShape.embeddingUpNat ≫ colχ f A' =
      colχ f A ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap ((godementResolution T').map a)
          ComplexShape.embeddingUpNat) := by
  unfold colχ
  rw [Category.assoc, mapHCExtendIso_hom_naturality, ← Category.assoc, ← Category.assoc,
    ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  congr 2
  exact CokernelCoresolution.complexFunctor_map_comp_complexHom (godementPullbackLift f)
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map a) a (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])

/-- The comparison of Godement double complexes `G(f_* K) ⟶ f_* G(K)`. -/
noncomputable def δχ (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ) :
    godDC T (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) ⟶
    HomologicalComplex₂.TotalMap.mapBicomplex (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
      (godDC T' K) where
  f p := colχ f (K.X p)
  comm' p p' _ := (colχ_naturality f (K.d p p')).symm

/-- The comparison of Godement total complexes `Tot G(f_* L) ⟶ f_* Tot G(L)`. -/
noncomputable def χ (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T')) :
    (godTotPlus T).obj ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapCochainComplexPlus.obj L) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapCochainComplexPlus.obj
        ((godTotPlus T').obj L) :=
  ObjectProperty.homMk (HomologicalComplex₂.total.map (δχ f L.obj) (ComplexShape.up ℤ) ≫
    HomologicalComplex₂.TotalMap.totalMap (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
      (godDC T' L.obj))

/-- In degree `p`, the row augmentation is the Godement unit of `K^p`. -/
lemma rowAug_f_eq {S : TopCat.{u}} (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} S) ℤ)
    (p : ℤ) : (rowAug S K).f p = (godementUnit S).app (K.X p) ≫
      (((godementResolution S).obj (K.X p)).extendXIso ComplexShape.embeddingUpNat
        embeddingUpNat_f_zero).inv := by
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X p)).inv ≫
    (colAugS S (K.X p)).f 0 = _
  rw [colAugS_f_zero, Iso.inv_hom_id_assoc]

/-- In degree `0`, the comparison `G(f_* A) ⟶ f_* G(A)` is the Godement lift of the identity. -/
lemma colχ_f_zero (A : TopCat.Sheaf AddCommGrpCat.{u} T') :
    (colχ f A).f 0 = (((godementResolution T).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj A)).extendXIso
          ComplexShape.embeddingUpNat embeddingUpNat_f_zero).hom ≫
      godementLiftHom f (𝟙 _) ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
        ((((godementResolution T').obj A).extendXIso ComplexShape.embeddingUpNat
          embeddingUpNat_f_zero).inv) := by
  unfold colχ
  rw [HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ _ embeddingUpNat_f_zero,
    HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ embeddingUpNat_f_zero]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  rfl

/-- The row augmentation of `f_* L` followed by the comparison `G(f_* L^n) ⟶ f_* G(L^n)` in
degree `0` is the pushforward of the row augmentation of `L`. -/
lemma rowAug_colχ (L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ) (n : ℤ) :
    (rowAug T (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)).f n ≫ (colχ f (L.X n)).f 0 =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map ((rowAug T' L).f n) := by
  rw [rowAug_f_eq, rowAug_f_eq, colχ_f_zero]
  erw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    (godementPullbackLift f).app_comp_lift (𝟙 _), Category.id_comp, Functor.map_comp]
  rfl

/-- On the summand of bidegree `(p, q)`, the comparison of total complexes
`Tot G(f_* L) ⟶ f_* Tot G(L)` is the comparison `G(f_* L^p) ⟶ f_* G(L^p)` in degree `q`. -/
theorem ιTotal_δχ (L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ) (p q n : ℤ)
    (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex₂.ιTotal _ (ComplexShape.up ℤ) p q n hpq ≫
        (HomologicalComplex₂.total.map (δχ f L) (ComplexShape.up ℤ)).f n ≫
        HomologicalComplex₂.TotalMap.totalMapf (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
          (godDC T' L) n =
      (colχ f (L.X p)).f q ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
        (HomologicalComplex₂.ιTotal (godDC T' L) (ComplexShape.up ℤ) p q n hpq) := by
  have hmap := HomologicalComplex₂.TotalMap.ι_totalMapf
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) (godDC T' L) (c₁₂ := ComplexShape.up ℤ)
    n p q hpq
  have hι := HomologicalComplex₂.ιTotal_map _ _ (δχ f L) (ComplexShape.up ℤ) p q n hpq
  rw [reassoc_of% hι]
  erw [hmap]
  rfl

/-- The comparison `f_* L ⟶ Tot G(f_* L)` followed by `χ` is the pushforward of the comparison
`L ⟶ Tot G(L)`. -/
theorem compNat_χ (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T')) :
    ((compNatPlus T).app ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapCochainComplexPlus.obj L)).hom ≫
        (χ f L).hom =
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((compNatPlus T').app L).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h0 : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n :=
    add_zero n
  have hmap := HomologicalComplex₂.TotalMap.ι_totalMapf
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) (godDC T' L.obj) (c₁₂ := ComplexShape.up ℤ)
    n n 0 h0
  have hι := HomologicalComplex₂.ιTotal_map _ _ (δχ f L.obj) (ComplexShape.up ℤ) n 0 n h0
  have hr := rowAug_colχ f L.obj n
  have e1 : ((compNatPlus T').app L).hom.f n = (rowAug T' L.obj).f n ≫
      HomologicalComplex₂.ιTotal (godDC T' L.obj) (ComplexShape.up ℤ) n 0 n h0 := rfl
  have e2 : ((compNatPlus T).app ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapCochainComplexPlus.obj L)).hom.f n =
      (rowAug T (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L.obj)).f n ≫
      HomologicalComplex₂.ιTotal (godDC T (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L.obj)) (ComplexShape.up ℤ) n 0 n h0 := by
    unfold compNatPlus compNat
    exact comparisonMapP_f _ _ _ (hypotheses_rowAug_plus T _) n
  have e3 : (χ f L).hom.f n = (HomologicalComplex₂.total.map (δχ f L.obj) (ComplexShape.up ℤ)).f n ≫
      HomologicalComplex₂.TotalMap.totalMapf (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
        (godDC T' L.obj) n := rfl
  rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, e1, e2, e3]
  erw [Functor.map_comp, ← hmap, Category.assoc, reassoc_of% hι, ← reassoc_of% hr]
  rfl

end Chi

section SecChi

attribute [local instance] globalSections_additive

attribute [local implicit_reducible] MMP.Analytic.godementResolution
  MMP.Analytic.CokernelCoresolution.complexFunctor TopCat.Sheaf

variable {T T' : TopCat.{u}} (f : T' ⟶ T)

/-- Cancellation of two isomorphisms and their inverses in a composite. -/
theorem aux_cancel5 {C : Type*} [Category* C] {P Q R S U V : C} (x : P ⟶ Q) (y : R ≅ Q)
    (m : Q ⟶ S) (z : U ≅ S) (w : S ⟶ V) :
    x ≫ y.inv ≫ (y.hom ≫ m ≫ z.inv) ≫ z.hom ≫ w = x ≫ m ≫ w := by
  simp

/-- The components of the inverse of `mapHomologicalComplexExtendIso`. -/
theorem mapHCExtendIso_inv_f {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {C D : Type*} [Category* C] [Category* D] [HasZeroObject C]
    [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (K : HomologicalComplex C c) (e : c.Embedding c') {i : ι} {i' : ι'}
    (h : e.f i = i') :
    (HomologicalComplex.mapHomologicalComplexExtendIso F K e).inv.f i' =
      F.map (K.extendXIso e h).hom ≫ (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv := by
  rw [← cancel_epi ((HomologicalComplex.mapHomologicalComplexExtendIso F K e).hom.f i'),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ h]
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp,
    Iso.hom_inv_id]

/-- The map of Godement section complexes induced by the identity of `f_* A` is the global
sections of the comparison `G(f_* A) ⟶ f_* G(A)`. -/
theorem secHom_colχ (A : TopCat.Sheaf AddCommGrpCat.{u} T') :
    (HomologicalComplex.mapHomologicalComplexExtendIso (globalSections T)
        ((godementResolution T).obj ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj A))
        ComplexShape.embeddingUpNat).inv ≫ secHom f (𝟙 _) ≫
      (HomologicalComplex.mapHomologicalComplexExtendIso (globalSections T')
        ((godementResolution T').obj A) ComplexShape.embeddingUpNat).hom =
    ((globalSections T).mapHomologicalComplex (ComplexShape.up ℤ)).map (colχ f A) := by
  refine HomologicalComplex.hom_ext _ _ fun i' => ?_
  cases hi : ComplexShape.embeddingUpNat.r i' with
  | none =>
    exact (Functor.map_isZero (globalSections T) (HomologicalComplex.isZero_extend_X'
      ((godementResolution T).obj ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj A))
      ComplexShape.embeddingUpNat i' hi)).eq_of_src _ _
  | some a =>
    have h : ComplexShape.embeddingUpNat.f a = i' := ComplexShape.embeddingUpNat.f_eq_of_r_eq_some hi
    erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    rw [mapHCExtendIso_inv_f _ _ _ h,
      HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ h,
      Functor.mapHomologicalComplex_map_f]
    unfold colχ
    erw [HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
      (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) (h := h)]
    unfold secHom
    erw [HomologicalComplex.extendMap_f _ _ h]
    simp only [Category.assoc, Functor.map_comp]
    exact (aux_cancel5 _ _ _ _ _).trans rfl

/-- The map of Godement section complexes induced by `ψ : A ⟶ f_* B` is natural in `A` and
`B`. -/
theorem secHom_naturality {A A' : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B B' : TopCat.Sheaf AddCommGrpCat.{u} T'} (a : A ⟶ A') (b : B ⟶ B')
    (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B)
    (ψ' : A' ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B')
    (h : a ≫ ψ' = ψ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map b) :
    (godementSections T).map a ≫ secHom f ψ' = secHom f ψ ≫ (godementSections T').map b := by
  have h' := CokernelCoresolution.complexFunctor_map_comp_complexHom (godementPullbackLift f)
    a b ψ ψ' h
  have := congrArg (fun g => (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).map
    (((globalSections T).mapHomologicalComplex _).map g)) h'
  simp only [Functor.map_comp] at this
  exact this

/-- The map of Godement section double complexes induced by `φ : K ⟶ f_* L`. -/
noncomputable def secDC {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (φ : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L) :
    godementSectionsDoubleComplex T K ⟶ godementSectionsDoubleComplex T' L where
  f p := secHom f (φ.f p)
  comm' p p' _ := (secHom_naturality f (K.d p p') (L.d p p') (φ.f p) (φ.f p') (φ.comm p p').symm).symm

end SecChi

section SecChi2

attribute [local instance] globalSections_additive
attribute [local implicit_reducible] MMP.Analytic.godementResolution
  MMP.Analytic.CokernelCoresolution.complexFunctor

variable {T T' : TopCat.{u}} (f : T' ⟶ T)

/-- On the summand of bidegree `(p, q)`, the comparison `Tot Γ(G(K)) ⟶ Γ(Tot G(K))` is the
global sections of the inclusion of that summand. -/
theorem ι_totalMapf_Γ {S : TopCat.{u}} (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} S) ℤ)
    (n p q : ℤ)
    (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (HomologicalComplex₂.TotalMap.mapBicomplex (globalSections S) (godDC S K)).ιTotal
        (ComplexShape.up ℤ) p q n hpq ≫
      HomologicalComplex₂.TotalMap.totalMapf (globalSections S) (godDC S K) n =
    (globalSections S).map ((godDC S K).ιTotal (ComplexShape.up ℤ) p q n hpq) :=
  HomologicalComplex₂.TotalMap.ι_totalMapf (globalSections S) (godDC S K)
      (c₁₂ := ComplexShape.up ℤ) n p q hpq

/-- Pasting of commutative squares and triangles into one commutative diagram. -/
theorem paste_tot {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {P₁ P₂ P₃ P₄ Q₁ Q₂ : D} {S₀ S₁ S₂ S₃ : C}
    (ι : G.obj S₀ ⟶ P₁) (A : P₁ ⟶ P₂) (B : P₂ ⟶ P₃) (Cc : P₃ ⟶ P₄) (E : P₄ ⟶ G.obj S₃)
    (a : G.obj S₀ ⟶ Q₁) (ι₂ : Q₁ ⟶ P₂) (b : Q₁ ⟶ Q₂) (ι₃ : Q₂ ⟶ P₃) (c : Q₂ ⟶ G.obj S₂)
    (ι₄ : G.obj S₂ ⟶ P₄) (E' : P₁ ⟶ G.obj S₁) (ιD : S₀ ⟶ S₁) (X : S₁ ⟶ S₃) (y : S₀ ⟶ S₂)
    (z : S₂ ⟶ S₃)
    (h1 : ι ≫ A = a ≫ ι₂) (h2 : ι₂ ≫ B = b ≫ ι₃) (h3 : ι₃ ≫ Cc = c ≫ ι₄) (h4 : ι₄ ≫ E = G.map z)
    (h5 : ι ≫ E' = G.map ιD) (h6 : ιD ≫ X = y ≫ z) (h8 : a ≫ b ≫ c = G.map y) :
    ι ≫ A ≫ B ≫ Cc ≫ E = ι ≫ E' ≫ G.map X := by
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, h4, reassoc_of% h5, ← G.map_comp, h6,
    G.map_comp, ← h8]
  simp only [Category.assoc]

/-- A commutative square with isomorphisms on its sides, rewritten with their inverses. -/
theorem paste_iso {C : Type*} [Category* C] {P Q R S U V : C} (e : P ≅ Q) (e' : R ≅ S)
    (g : Q ⟶ S) (s : P ≅ U) (d : U ⟶ V) (s' : R ≅ V)
    (key : s.hom ≫ d ≫ s'.inv ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv ≫ s'.hom = e.inv ≫ s.hom ≫ d := by
  rw [← cancel_epi e.hom, Iso.hom_inv_id_assoc, ← reassoc_of% key]
  simp

/-- The degree-`q` component of `secHom_colχ`. -/
theorem secHom_colχ_f (A : TopCat.Sheaf AddCommGrpCat.{u} T') (q : ℤ) :
    (HomologicalComplex.mapHomologicalComplexExtendIso (globalSections T)
        ((godementResolution T).obj ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj A))
        ComplexShape.embeddingUpNat).inv.f q ≫ (secHom f (𝟙 _)).f q ≫
      (HomologicalComplex.mapHomologicalComplexExtendIso (globalSections T')
        ((godementResolution T').obj A) ComplexShape.embeddingUpNat).hom.f q =
    (globalSections T).map ((colχ f A).f q) := by
  have h8 := congrArg (fun g => HomologicalComplex.Hom.f g q) (secHom_colχ f A)
  erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h8
  exact h8

/-- The summand-wise form of `gammaTot_χ_key`, on the summand of bidegree `(p, q)`. -/
theorem gammaTot_χ_comp (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T')) (n p q : ℤ)
    (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex₂.ιTotal _ (ComplexShape.up ℤ) p q n hpq ≫
      (HomologicalComplex₂.total.map (secIso T (((TopCat.Sheaf.pushforward
        AddCommGrpCat.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)).hom
        (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.total.map (secDC f
          (𝟙 (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L.obj)))
          (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.total.map (secIso T' L.obj).inv (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.TotalMap.totalMap (globalSections T') (godDC T' L.obj)).f n =
    HomologicalComplex₂.ιTotal _ (ComplexShape.up ℤ) p q n hpq ≫
      (HomologicalComplex₂.TotalMap.totalMap (globalSections T) (godDC T (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.obj)) ≫
      ((globalSections T).mapHomologicalComplex _).map (χ f L).hom).f n := by
  have h1 := HomologicalComplex₂.ιTotal_map _ _ (secIso T (((TopCat.Sheaf.pushforward
      AddCommGrpCat.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)).hom
    (ComplexShape.up ℤ) p q n hpq
  have h2 := HomologicalComplex₂.ιTotal_map _ _ (secDC f
        (𝟙 (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L.obj)))
    (ComplexShape.up ℤ) p q n hpq
  have h3 := HomologicalComplex₂.ιTotal_map _ _ (secIso T' L.obj).inv (ComplexShape.up ℤ) p q n hpq
  have h4 := HomologicalComplex₂.TotalMap.ι_totalMapf (globalSections T') (godDC T' L.obj)
    (c₁₂ := ComplexShape.up ℤ) n p q hpq
  have h6 := ιTotal_δχ f L.obj p q n hpq
  have h8 := secHom_colχ_f f (L.obj.X p) q
  have h5 := ι_totalMapf_Γ (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L.obj) n p q hpq
  simp only [HomologicalComplex.comp_f]
  refine paste_tot (globalSections T)
    (S₂ := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (((godDC T' L.obj).X p).X q))
    (z := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
      ((godDC T' L.obj).ιTotal (ComplexShape.up ℤ) p q n hpq))
    (y := (colχ f (L.obj.X p)).f q)
    (ιD := HomologicalComplex₂.ιTotal _ (ComplexShape.up ℤ) p q n hpq)
    (X := (χ f L).hom.f n) _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h8

/-- The map of total complexes of Godement sections induced by the identity of `f_* L`, followed
by `Tot Γ(G(L)) ⟶ Γ(Tot G(L))`, is `Tot Γ(G(f_* L)) ⟶ Γ(Tot G(f_* L))` followed by `Γ(χ)`. -/
theorem gammaTot_χ_key (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T')) :
    HomologicalComplex₂.total.map (secIso T (((TopCat.Sheaf.pushforward
        AddCommGrpCat.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)).hom
        (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.total.map (secDC f
          (𝟙 (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L.obj)))
          (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.total.map (secIso T' L.obj).inv (ComplexShape.up ℤ) ≫
      HomologicalComplex₂.TotalMap.totalMap (globalSections T') (godDC T' L.obj) =
    HomologicalComplex₂.TotalMap.totalMap (globalSections T) (godDC T (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.obj)) ≫
      ((globalSections T).mapHomologicalComplex _).map (χ f L).hom :=
  HomologicalComplex.hom_ext _ _ fun n =>
    HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) fun p q hpq =>
      gammaTot_χ_comp f L n p q hpq

/-- `gammaTot_χ_key`, stated with the isomorphisms `total.mapIso` and `totalIsoOfFinite`. -/
theorem gammaTot_χ_key2 (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T')) :
    (HomologicalComplex₂.total.mapIso (secIso T
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapCochainComplexPlus.obj L).obj)
        (ComplexShape.up ℤ)).hom ≫
      HomologicalComplex₂.total.map (secDC f
          (𝟙 (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L.obj)))
          (ComplexShape.up ℤ) ≫
      (HomologicalComplex₂.total.mapIso (secIso T' L.obj) (ComplexShape.up ℤ)).inv ≫
      (HomologicalComplex₂.TotalMap.totalIsoOfFinite (globalSections T') (godDC T' L.obj)
        (finite_antidiagonal_godDC T' L)).hom =
    (HomologicalComplex₂.TotalMap.totalIsoOfFinite (globalSections T)
        (godDC T ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapCochainComplexPlus.obj L).obj)
        (finite_antidiagonal_godDC T
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapCochainComplexPlus.obj L))).hom ≫
      ((globalSections T).mapHomologicalComplex _).map (χ f L).hom :=
  gammaTot_χ_key f L

/-- `paste_iso`, with the right-hand side bracketed on the left. -/
theorem paste_iso' {C : Type*} [Category* C] {P Q R S U V : C} (e : P ≅ Q) (e' : R ≅ S)
    (g : Q ⟶ S) (s : P ≅ U) (d : U ⟶ V) (s' : R ≅ V)
    (key : s.hom ≫ d ≫ s'.inv ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv ≫ s'.hom = (e.inv ≫ s.hom) ≫ d := by
  rw [Category.assoc]
  exact paste_iso e e' g s d s' key

/-- Under `gammaTotIso`, the global sections of `χ` correspond to the map of total complexes of
Godement sections induced by the identity of `f_* L`. -/
theorem gammaTot_χ (L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T')) :
    ((globalSections T).mapHomologicalComplex _).map (χ f L).hom ≫ (gammaTotIso T' L).hom =
      (gammaTotIso T ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapCochainComplexPlus.obj L)).hom ≫
        HomologicalComplex₂.total.map (secDC f
          (𝟙 (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L.obj)))
          (ComplexShape.up ℤ) := by
  rw [gammaTotIso_hom_eq, gammaTotIso_hom_eq]
  exact paste_iso' _ _ _ _ _ _ (gammaTot_χ_key2 f L)

end SecChi2

/-- The image under a functor of a commutative square whose diagonal factors as `a ≫ x`. -/
theorem map_comp_map_eq_map_comp_map_comp_map {C D : Type*} [Category* C] [Category* D]
    (H : C ⥤ D) {P₀ P₁ P₂ P₃ P₄ : C}
    (p : P₀ ⟶ P₁) (k : P₁ ⟶ P₄) (a : P₀ ⟶ P₂) (x : P₂ ⟶ P₃) (y : P₃ ⟶ P₄) (z : P₀ ⟶ P₃)
    (hi : z ≫ y = p ≫ k) (hz : z = a ≫ x) :
    H.map p ≫ H.map k = H.map a ≫ H.map x ≫ H.map y := by
  rw [← H.map_comp, ← H.map_comp, ← H.map_comp, ← hi, hz, Category.assoc]

/-- The image under a functor of a commutative square, with the two maps inverted by the functor
moved across. -/
theorem map_comp_map_comp_inv_eq_inv_comp_map {C D : Type*} [Category* C] [Category* D]
    (H : C ⥤ D) {P₀ P₁ P₂ P₃ P₄ : C}
    (x : P₁ ⟶ P₂) (y : P₂ ⟶ P₃) (U1 : P₄ ⟶ P₁) (U2 : P₀ ⟶ P₂) (U3 : P₀ ⟶ P₃) (g : P₄ ⟶ P₀)
    (hU1 : IsIso (H.map U1)) (hU3 : IsIso (H.map U3)) (h3 : U2 ≫ y = U3)
    (h4 : g ≫ U2 = U1 ≫ x) :
    H.map x ≫ H.map y ≫ inv (H.map U3) = inv (H.map U1) ≫ H.map g := by
  rw [IsIso.eq_inv_comp, ← H.map_comp_assoc, ← H.map_comp_assoc, IsIso.comp_inv_eq,
    ← H.map_comp, ← h4, ← h3, Category.assoc]

/-- Pasting of four commutative squares into one commutative diagram, with the right-hand side
bracketed on the left. -/
theorem comp_eq_of_four_comm_squares {C : Type*} [Category* C]
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ : C}
    (p : P₀ ⟶ P₁) (k : P₁ ⟶ P₂) (u' : P₂ ⟶ P₃) (h' : P₃ ⟶ P₄) (t' : P₄ ⟶ P₅)
    (a : P₀ ⟶ P₆) (x : P₆ ⟶ P₇) (y : P₇ ⟶ P₂) (u : P₆ ⟶ P₈) (g : P₈ ⟶ P₃)
    (h : P₈ ⟶ P₉) (M : P₉ ⟶ P₄) (t : P₉ ⟶ P₁₀) (s : P₁₀ ⟶ P₅)
    (hA : p ≫ k = a ≫ x ≫ y) (hB : x ≫ y ≫ u' = u ≫ g) (hC : g ≫ h' = h ≫ M)
    (hD : M ≫ t' = t ≫ s) :
    p ≫ k ≫ u' ≫ h' ≫ t' = (a ≫ u ≫ h ≫ t) ≫ s := by
  rw [reassoc_of% hA, reassoc_of% hB, reassoc_of% hC, hD]
  simp only [Category.assoc]

section P1b

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] globalSections_additive

variable {X' X : AlgebraicGeometry.Scheme.{u}} (f : X' ⟶ X)

/-- On derived hypercohomology, the pushforward–pullback map commutes with the comparisons
`K ⟶ Tot G(K)` through the comparison `χ`. -/
theorem pp_Bp_hA (K : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} X'.carrier)) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map (f.pushforwardPullback K) ≫ (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map ((globalSections X'.carrier).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ((compNatPlus X'.carrier).app K))) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map ((globalSections X.carrier).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ((compNatPlus X.carrier).app ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K)))) ≫ (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map ((globalSections X.carrier).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (χ f.base K))) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map (f.pushforwardPullback ((godTotPlus X'.carrier).obj K)) := by
  have hii : ((compNatPlus X.carrier).app ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K)) ≫ χ f.base K =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.map ((compNatPlus X'.carrier).app K) := by
    ext : 1
    exact compNat_χ f.base K
  have hi := f.pushforwardPullback_naturality ((compNatPlus X'.carrier).app K)
  have hz : (globalSections X.carrier).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.map
        ((compNatPlus X'.carrier).app K))) =
      (globalSections X.carrier).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
        ((compNatPlus X.carrier).app ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K))) ≫
      (globalSections X.carrier).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (χ f.base K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hii]
  exact map_comp_map_eq_map_comp_map_comp_map _ _ _ _ _ _ _ hi hz

/-- On derived hypercohomology, `RΓ(χ)` followed by the pushforward–pullback map commutes with
the inverses of the derived-functor units on the Godement total complexes. -/
theorem pp_Bp_hB (K : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} X'.carrier)) (m : ℤ)
    (hU1 : IsIso ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
      (Uc X.carrier ((godTotPlus X.carrier).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K)))))
    (hU3 : IsIso ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
      (Uc X'.carrier ((godTotPlus X'.carrier).obj K)))) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
        ((globalSections X.carrier).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (χ f.base K))) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
        (f.pushforwardPullback ((godTotPlus X'.carrier).obj K)) ≫
      CategoryTheory.inv (I := hU3) ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
        (Uc X'.carrier ((godTotPlus X'.carrier).obj K))) =
    CategoryTheory.inv (I := hU1) ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
        (Uc X.carrier ((godTotPlus X.carrier).obj
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K)))) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
        (DerivedCategory.Plus.Q.map
          ((globalSections X.carrier).mapCochainComplexPlus.map (χ f.base K))) := by
  have hiii : Uc X.carrier ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj
      ((godTotPlus X'.carrier).obj K)) ≫ f.pushforwardPullback ((godTotPlus X'.carrier).obj K) =
      Uc X'.carrier ((godTotPlus X'.carrier).obj K) :=
    f.sectionsUnit_comp_pushforwardPullback _
  have hiv : DerivedCategory.Plus.Q.map ((globalSections X.carrier).mapCochainComplexPlus.map
        (χ f.base K)) ≫ Uc X.carrier
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj
            ((godTotPlus X'.carrier).obj K)) =
      Uc X.carrier ((godTotPlus X.carrier).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K)) ≫
      (globalSections X.carrier).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (χ f.base K)) :=
    (Functor.mapCochainComplexPlusDerivedUnit (globalSections X.carrier)).naturality (χ f.base K)
  exact map_comp_map_comp_inv_eq_inv_comp_map
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m) _ _ _ _ _ _
    hU1 hU3 hiii hiv

/-- `gammaTot_χ` on homology in degree `m`. -/
theorem pp_Bp_hD (K : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} X'.carrier)) (m : ℤ) :
    HomologicalComplex.homologyMap
        (((globalSections X.carrier).mapHomologicalComplex _).map (χ f.base K).hom) m ≫
      HomologicalComplex.homologyMap (gammaTotIso X'.carrier K).hom m =
      HomologicalComplex.homologyMap (gammaTotIso X.carrier
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K)).hom m ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
          (secDC f.base (𝟙 (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapHomologicalComplex
            _).obj K.obj))) (ComplexShape.up ℤ)) m :=
  (HomologicalComplex.homologyMap_comp _ _ m).symm.trans
    ((congrArg (fun χ => HomologicalComplex.homologyMap χ m) (gammaTot_χ f.base K)).trans
      (HomologicalComplex.homologyMap_comp _ _ m))

/-- The isomorphism `hypercohomologyIsoGodementTotal` between derived and Godement
hypercohomology is compatible with pullback along a morphism of schemes `f`. -/
theorem pp_Bp (K : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} X'.carrier)) (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map (f.pushforwardPullback K) ≫
        (hypercohomologyIsoGodementTotal X'.carrier K m).hom =
      (hypercohomologyIsoGodementTotal X.carrier
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K)
        m).hom ≫ HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
          (secDC f.base (𝟙 (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapHomologicalComplex
            _).obj K.obj))) (ComplexShape.up ℤ)) m := by
  haveI := isIso_Uc X.carrier ((godTotPlus X.carrier).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K)) fun n => by
    obtain ⟨a, ha⟩ := ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).mapCochainComplexPlus.obj K).2
    exact isFlasque_total_godDC X.carrier _ a n
  haveI := isIso_Uc X'.carrier ((godTotPlus X'.carrier).obj K) fun n => by
    obtain ⟨a, ha⟩ := K.2
    exact isFlasque_total_godDC X'.carrier K.obj a n
  rw [hypercohomologyIsoGodementTotal_hom_eq, hypercohomologyIsoGodementTotal_hom_eq]
  exact comp_eq_of_four_comm_squares _ _ _ _ _ _ _ _ _ _ _ _ _ _ (pp_Bp_hA f K m)
    (pp_Bp_hB f K m (Functor.map_isIso _ _) (Functor.map_isIso _ _))
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} m).hom.naturality
      ((globalSections X.carrier).mapCochainComplexPlus.map (χ f.base K)).hom) (pp_Bp_hD f K m)

end P1b

end GodPull

section Analytic

open CategoryTheory.Limits TopologicalSpace
open MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff

section SingCmpOpens

open Abelian Topology MMP MMP.Mori AlgebraicTopology Simplicial

namespace SingCmp

/-- `Hom(ULift ℤ, A) ≃+ A`. -/
private def uliftIntHomEquiv (A : AddCommGrpCat.{0}) : (AddCommGrpCat.of (ULift ℤ) ⟶ A) ≃+ A where
  toFun φ := φ (ULift.up 1)
  invFun a := AddCommGrpCat.ofHom ((zmultiplesHom A a).comp AddEquiv.ulift.toAddMonoidHom)
  left_inv φ := by
    ext ⟨k⟩
    change k • φ (ULift.up 1) = φ (ULift.up k)
    rw [← map_zsmul]
    congr 1
    exact ULift.ext (by simp)
  right_inv a := by
    change (1 : ℤ) • a = a
    exact one_zsmul a
  map_add' φ ψ := rfl

noncomputable section SingularBridge

variable (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]

private abbrev G : ModuleCat.{0} R ⥤ AddCommGrpCat.{0} :=
  forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0}
private abbrev chMod : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} R) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)
private abbrev chAb : TopCat.{0} ⥤ ChainComplex AddCommGrpCat.{0} ℕ :=
  (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))
private abbrev singAb : TopCat.{0}ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  chAb.op ⋙ HomologicalComplex.opFunctor _ _ ⋙
    (preadditiveYoneda.obj (AddCommGrpCat.of A)).mapHomologicalComplex _
private abbrev cochMod (M : TopCat.{0}) : CochainComplex (ModuleCat.{0} R) ℕ :=
  (singularCochainComplex R (ModuleCat.of R A)).obj (op M)

/-- The singular `k`-chains of `M` with coefficients in `R`. -/
private abbrev chainsR (M : TopCat.{0}) (k : ℕ) : ModuleCat.{0} R :=
  ((TopCat.toSSet.obj M).chainComplex (ModuleCat.of R R)).X k
/-- The singular `k`-chains of `M` with coefficients in `ℤ`. -/
private abbrev chainsZ (M : TopCat.{0}) (k : ℕ) : AddCommGrpCat.{0} :=
  ((TopCat.toSSet.obj M).chainComplex (AddCommGrpCat.of (ULift.{0} ℤ))).X k

variable {R A}

/-- The value of an `R`-linear singular cochain on a singular simplex. -/
private def valR {M : TopCat.{0}} {k : ℕ} (x : chainsR R M k ⟶ ModuleCat.of R A)
    (s : (TopCat.toSSet.obj M) _⦋k⦌) : A :=
  ((TopCat.toSSet.obj M).ιChainComplex s ≫ x) (1 : R)

/-- The value of an additive singular cochain on a singular simplex. -/
private def valAb {M : TopCat.{0}} {k : ℕ} (y : chainsZ M k ⟶ AddCommGrpCat.of A)
    (s : (TopCat.toSSet.obj M) _⦋k⦌) : A :=
  ((TopCat.toSSet.obj M).ιChainComplex s ≫ y) (ULift.up 1)

private lemma valR_injective {M : TopCat.{0}} {k : ℕ}
    {x x' : chainsR R M k ⟶ ModuleCat.of R A} (h : ∀ s, valR x s = valR x' s) :
    x = x' := by
  refine SSet.chainComplex_hom_ext fun s ↦ ?_
  ext
  exact h s

private lemma valAb_injective {M : TopCat.{0}} {k : ℕ}
    {y y' : chainsZ M k ⟶ AddCommGrpCat.of A} (h : ∀ s, valAb y s = valAb y' s) :
    y = y' :=
  SSet.chainComplex_hom_ext fun s ↦ (uliftIntHomEquiv _).injective (h s)

/-- The additive cochain with the same values as an `R`-linear one. -/
private def toAb {M : TopCat.{0}} {k : ℕ} (x : chainsR R M k ⟶ ModuleCat.of R A) :
    chainsZ M k ⟶ AddCommGrpCat.of A :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj M).isColimitChainComplexXCofan _ k)
    fun s ↦ (uliftIntHomEquiv (.of A)).symm (valR x s)

/-- The `R`-linear cochain with the same values as an additive one. -/
private def toMod {M : TopCat.{0}} {k : ℕ} (y : chainsZ M k ⟶ AddCommGrpCat.of A) :
    chainsR R M k ⟶ ModuleCat.of R A :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj M).isColimitChainComplexXCofan _ k)
    fun s ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton R A (valAb y s))

private lemma valAb_toAb {M : TopCat.{0}} {k : ℕ}
    (x : chainsR R M k ⟶ ModuleCat.of R A) (s) : valAb (toAb x) s = valR x s := by
  unfold valAb toAb
  erw [Cofan.IsColimit.fac]
  exact (uliftIntHomEquiv _).apply_symm_apply _

attribute [local simp] valAb_toAb

private lemma valR_toMod {M : TopCat.{0}} {k : ℕ}
    (y : chainsZ M k ⟶ AddCommGrpCat.of A) (s) : valR (toMod (R := R) y) s = valAb y s := by
  unfold valR toMod
  erw [Cofan.IsColimit.fac]
  exact one_smul R _

attribute [local simp] valR_toMod

private lemma valR_add {M : TopCat.{0}} {k : ℕ}
    (x x' : chainsR R M k ⟶ ModuleCat.of R A) (s) :
    valR (x + x') s = valR x s + valR x' s := by
  unfold valR
  rw [Preadditive.comp_add]
  rfl

attribute [local simp] valR_add

private lemma valR_smul {M : TopCat.{0}} {k : ℕ}
    (r : R) (x : chainsR R M k ⟶ ModuleCat.of R A) (s) :
    valR (r • x) s = r • valR x s := by
  unfold valR
  rw [Linear.comp_smul]
  rfl

attribute [local simp] valR_smul

private lemma valAb_add {M : TopCat.{0}} {k : ℕ}
    (y y' : chainsZ M k ⟶ AddCommGrpCat.of A) (s) :
    valAb (y + y') s = valAb y s + valAb y' s := by
  unfold valAb
  rw [Preadditive.comp_add]
  rfl

attribute [local simp] valAb_add

private lemma valR_d {M : TopCat.{0}} {k : ℕ}
    (x : chainsR R M k ⟶ ModuleCat.of R A) (s) :
    valR ((((TopCat.toSSet.obj M).chainComplex (ModuleCat.of R R)).d (k + 1) k) ≫ x) s =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • valR x ((TopCat.toSSet.obj M).δ i s) := by
  unfold valR
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp [Preadditive.sum_comp]

private lemma valAb_d {M : TopCat.{0}} {k : ℕ}
    (y : chainsZ M k ⟶ AddCommGrpCat.of A) (s) :
    valAb ((((TopCat.toSSet.obj M).chainComplex (AddCommGrpCat.of (ULift.{0} ℤ))).d (k + 1) k) ≫ y)
        s =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • valAb y ((TopCat.toSSet.obj M).δ i s) := by
  change uliftIntHomEquiv _ (_ ≫ _ ≫ y) = ∑ i : Fin (k + 2), _ • uliftIntHomEquiv _ (_ ≫ y)
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp, map_sum]
  simp only [Preadditive.zsmul_comp, map_zsmul]

private lemma valR_map {Z W : TopCat.{0}} (f : Z ⟶ W) {k : ℕ}
    (x : chainsR R W k ⟶ ModuleCat.of R A) (s) :
    valR ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f k ≫ x) s =
      valR x ((TopCat.toSSet.map f).app _ s) := by
  unfold valR
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]

private lemma valAb_map {Z W : TopCat.{0}} (f : Z ⟶ W) {k : ℕ}
    (y : chainsZ W k ⟶ AddCommGrpCat.of A) (s) :
    valAb ((SSet.chainComplexMap (TopCat.toSSet.map f) (AddCommGrpCat.of (ULift.{0} ℤ))).f k ≫ y)
      s =
      valAb y ((TopCat.toSSet.map f).app _ s) := by
  unfold valAb
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]

variable (R A) in
/-- `R`-linear and additive singular cochains with coefficients in `A` agree: both are the
functions on singular simplices. -/
private def cochainEquiv (M : TopCat.{0}) (k : ℕ) :
    (cochMod R A M).X k ≃+ ((singAb A).obj (op M)).X k where
  toFun x := toAb (show chainsR R M k ⟶
    ModuleCat.of R A from x)
  invFun y := toMod (R := R) (show ((TopCat.toSSet.obj M).chainComplex
    (AddCommGrpCat.of (ULift.{0} ℤ))).X k ⟶ AddCommGrpCat.of A from y)
  left_inv x := valR_injective fun s ↦ by rw [valR_toMod, valAb_toAb]
  right_inv y := valAb_injective fun s ↦ by rw [valAb_toAb, valR_toMod]
  map_add' x y := valAb_injective fun s ↦ by
    erw [valAb_add, valAb_toAb, valAb_toAb, valAb_toAb, valR_add]

private lemma cochainEquiv_d (M : TopCat.{0}) (k : ℕ) (x : (cochMod R A M).X k) :
    cochainEquiv R A M (k + 1) ((cochMod R A M).d k (k + 1) x) =
      ((singAb A).obj (op M)).d k (k + 1) (cochainEquiv R A M k x) :=
  valAb_injective fun s ↦ by
    change valAb (toAb (((TopCat.toSSet.obj M).chainComplex (ModuleCat.of R R)).d (k + 1) k ≫
      (show chainsR R M k ⟶ ModuleCat.of R A
        from x))) s = valAb (((TopCat.toSSet.obj M).chainComplex
          (AddCommGrpCat.of (ULift.{0} ℤ))).d (k + 1) k ≫ toAb x) s
    rw [valAb_toAb, valAb_d]
    simp only [valAb_toAb (M := M) (k := k) x]
    exact valR_d (M := M) x s

private lemma cochainEquiv_map {Z W : TopCat.{0}} (f : Z ⟶ W) (k : ℕ) (x : (cochMod R A W).X k) :
    cochainEquiv R A Z k (((singularCochainComplex R (ModuleCat.of R A)).map f.op).f k x) =
      ((singAb A).map f.op).f k (cochainEquiv R A W k x) :=
  valAb_injective fun s ↦ by
    change valAb (toAb ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f k ≫
      (show chainsR R W k ⟶ ModuleCat.of R A
        from x))) s = valAb ((SSet.chainComplexMap (TopCat.toSSet.map f)
          (AddCommGrpCat.of (ULift.{0} ℤ))).f k ≫ toAb x) s
    rw [valAb_toAb, valAb_map, valAb_toAb (M := W) (k := k) x]
    exact valR_map f x s

variable (A) in
/-- Post-composition of additive singular cochains with multiplication by `r : R`. -/
private abbrev smulCochains (r : R) : singAb A ⟶ singAb A :=
  Functor.whiskerLeft (chAb.op ⋙ HomologicalComplex.opFunctor _ _)
    (NatTrans.mapHomologicalComplex
      (preadditiveYoneda.map (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom A r))) _)

private lemma cochainEquiv_smul (M : TopCat.{0}) (k : ℕ) (r : R) (x : (cochMod R A M).X k) :
    cochainEquiv R A M k (r • x) = ((smulCochains A r).app (op M)).f k (cochainEquiv R A M k x) :=
  valAb_injective fun s ↦ by
    change valAb (toAb (r • (show chainsR R M k ⟶
      ModuleCat.of R A from x))) s = r • valAb (toAb x) s
    rw [valAb_toAb, valAb_toAb (M := M) (k := k) x]
    exact valR_smul r x s

variable (R A) in
private def cochIso (M : TopCat.{0}) :
    ((G R).mapHomologicalComplex _).obj (cochMod R A M) ≅ (singAb A).obj (op M) :=
  HomologicalComplex.Hom.isoOfComponents (fun k ↦ (cochainEquiv R A M k).toAddCommGrpIso) (by
    rintro i j (rfl : i + 1 = j)
    ext x
    exact (cochainEquiv_d M i x).symm)

private lemma cochIso_naturality {Z W : TopCat.{0}} (f : Z ⟶ W) :
    ((G R).mapHomologicalComplex _).map ((singularCochainComplex R (ModuleCat.of R A)).map f.op) ≫
      (cochIso R A Z).hom = (cochIso R A W).hom ≫ (singAb A).map f.op := by
  ext k x
  exact cochainEquiv_map f k x

private lemma cochIso_smul (M : TopCat.{0}) (r : R) :
    ((G R).mapHomologicalComplex _).map (r • 𝟙 (cochMod R A M)) ≫ (cochIso R A M).hom =
      (cochIso R A M).hom ≫ (smulCochains A r).app (op M) := by
  ext k x
  exact cochainEquiv_smul M k r x

private lemma emptyHom_ext (M : TopCat.{0}) (B : ModuleCat.{0} R) (k : ℕ)
    (x y : ((chMod R).obj (TopCat.of (∅ : Set M))).X k ⟶ B) : x = y := by
  refine Sigma.hom_ext _ _ (fun σ => ?_)
  exfalso
  obtain ⟨p⟩ : Nonempty (SimplexCategory.toTop.obj ⦋k⦌) := inferInstance
  exact (show (∅ : Set M) from
    (σ.down : SimplexCategory.toTop.obj ⦋k⦌ ⟶ TopCat.of (∅ : Set M)).hom p).2

variable (R A) in
private lemma restriction_empty_eq_zero (M : TopCat.{0}) :
    singularCochainRestriction R (ModuleCat.of R A) M ∅ = 0 := by
  ext k x
  exact emptyHom_ext M _ k _ _

variable (R A) in
private def relIso (M : TopCat.{0}) (n : ℕ) :
    relativeSingularCohomology R (ModuleCat.of R A) M ∅ n ≅ (cochMod R A M).homology n :=
  haveI := kernel.ι_of_zero (restriction_empty_eq_zero R A M)
  (relativeSingularCochainComplex R (ModuleCat.of R A) M ∅).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) rfl ≪≫
    HomologicalComplex.homologyMapIso (asIso (kernel.ι _)) n

private lemma relIso_naturality {Z W : TopCat.{0}} (f : Z ⟶ W) (n : ℕ) :
    relativeSingularCohomology.map R (ModuleCat.of R A) f (Set.empty_subset _) n ≫
      (relIso R A Z n).hom =
    (relIso R A W n).hom ≫ HomologicalComplex.homologyMap
      ((singularCochainComplex R (ModuleCat.of R A)).map f.op) n := by
  change relativeSingularCohomology.map R (ModuleCat.of R A) f (Set.empty_subset _) n ≫
      ((relativeSingularCochainComplex R (ModuleCat.of R A) Z ∅).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl).hom ≫
      HomologicalComplex.homologyMap (kernel.ι _) n =
    (((relativeSingularCochainComplex R (ModuleCat.of R A) W ∅).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl).hom ≫
      HomologicalComplex.homologyMap (kernel.ι _) n) ≫ _
  rw [relativeSingularCohomology.map]
  erw [HomologicalComplex.extendHomologyIso_hom_naturality_assoc]
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    relativeSingularCochainComplex.map_ι]
  rfl

variable (R A) in
/-- The cohomology of `R`-linear singular cochains, as an abelian group, is that of additive
singular cochains. -/
private def homIso (M : TopCat.{0}) (n : ℕ) :
    (G R).obj ((cochMod R A M).homology n) ≅ ((singAb A).obj (op M)).homology n :=
  (((cochMod R A M).sc n).mapHomologyIso (G R)).symm ≪≫
    HomologicalComplex.homologyMapIso (cochIso R A M) n

private lemma homIso_naturality {Z Z' : TopCat.{0}} (φ : cochMod R A Z' ⟶ cochMod R A Z)
    (ψ : (singAb A).obj (op Z') ⟶ (singAb A).obj (op Z))
    (h : ((G R).mapHomologicalComplex _).map φ ≫ (cochIso R A Z).hom = (cochIso R A Z').hom ≫ ψ)
    (n : ℕ) :
    (G R).map (HomologicalComplex.homologyMap φ n) ≫ (homIso R A Z n).hom =
      (homIso R A Z' n).hom ≫ HomologicalComplex.homologyMap ψ n := by
  simp only [homIso, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom]
  change (G R).map (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map
      φ)) ≫ (((cochMod R A Z).sc n).mapHomologyIso (G R)).inv ≫
        HomologicalComplex.homologyMap (cochIso R A Z).hom n =
    ((((cochMod R A Z').sc n).mapHomologyIso (G R)).inv ≫
        HomologicalComplex.homologyMap (cochIso R A Z').hom n) ≫ _
  have key := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (G R)
  have key3 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) h
  simp only [HomologicalComplex.homologyMap_comp] at key3
  refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _).symm
  refine (congrArg (· ≫ HomologicalComplex.homologyMap (cochIso R A Z).hom n) key).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg ((((cochMod R A Z').sc n).mapHomologyIso (G R)).inv ≫ ·) key3

variable (R A) in
private def totalIso (M : TopCat.{0}) (n : ℕ) :
    (G R).obj (relativeSingularCohomology R (ModuleCat.of R A) M ∅ n) ≅
      ((singAb A).obj (op M)).homology n :=
  (G R).mapIso (relIso R A M n) ≪≫ homIso R A M n

private lemma totalIso_naturality {Z W : TopCat.{0}} (f : Z ⟶ W) (n : ℕ) :
    (G R).map (relativeSingularCohomology.map R (ModuleCat.of R A) f (Set.empty_subset _) n) ≫
      (totalIso R A Z n).hom =
    (totalIso R A W n).hom ≫ HomologicalComplex.homologyMap ((singAb A).map f.op) n := by
  simp only [totalIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← (G R).map_comp_assoc, relIso_naturality, (G R).map_comp_assoc,
    homIso_naturality _ _ (cochIso_naturality f), Category.assoc]

private lemma homologyMap_smul_id (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (r : R) :
    HomologicalComplex.homologyMap (r • 𝟙 K) n = r • 𝟙 _ := by
  change ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map (r • 𝟙 K)) = _
  have : (HomologicalComplex.shortComplexFunctor _ _ n).map (r • 𝟙 K) = r • 𝟙 _ := by
    ext <;> rfl
  rw [this, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

private lemma totalIso_smul (M : TopCat.{0}) (n : ℕ) (r : R)
    (x : relativeSingularCohomology R (ModuleCat.of R A) M ∅ n) :
    (totalIso R A M n).hom (r • x) =
      HomologicalComplex.homologyMap ((smulCochains A r).app (op M)) n
        ((totalIso R A M n).hom x) := by
  have h₁ : (relIso R A M n).hom (r • x) =
      HomologicalComplex.homologyMap (r • 𝟙 (cochMod R A M)) n ((relIso R A M n).hom x) := by
    rw [homologyMap_smul_id, map_smul]
    rfl
  have h₂ := ConcreteCategory.congr_hom (homIso_naturality _ _ (cochIso_smul M r) n)
    ((relIso R A M n).hom x)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₂
  exact (congrArg (homIso R A M n).hom h₁).trans h₂

end SingularBridge

section Lambda

/-- The constant sheaf `ℂ_M`. -/
noncomputable abbrev constSh (M : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} M :=
  (constantSheaf (Opens.grothendieckTopology M) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ)

/-- The canonical map `f⁻¹ ℂ_M ⟶ ℂ_N`. -/
noncomputable abbrev toConst {M N : TopCat.{0}} (f : N ⟶ M) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj (constSh M) ⟶ constSh N :=
  (((constantSheafAdj (Opens.grothendieckTopology M) AddCommGrpCat.{0}
      Limits.isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)).homEquiv
      (AddCommGrpCat.of ℂ) (constSh N)).symm
    ((constantSheafAdj (Opens.grothendieckTopology N) AddCommGrpCat.{0}
        Limits.isTerminalTop).unit.app (AddCommGrpCat.of ℂ) ≫
      (constSh N).obj.map (homOfLE le_top).op)

/-- On metrizable locally contractible spaces, sheaf cohomology of the constant sheaf `ℂ_M` is
isomorphic to singular cohomology with coefficients in `ℂ`, compatibly with scalar
multiplication and with pullback along continuous maps. -/
theorem exists_singular (n : ℕ) :
    ∃ Λ : ∀ (M : TopCat.{0}) [MetrizableSpace M], LocallyContractibleSpace M →
        ((MMP.Analytic.sheafCohomology M n).obj (constSh M) ≃+
          relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) M ∅ n),
      (∀ (M : TopCat.{0}) [MetrizableSpace M] (hM : LocallyContractibleSpace M) (c : ℂ) x,
        Λ M hM ((MMP.Analytic.sheafCohomology M n).map
          ((constantSheaf _ AddCommGrpCat.{0}).map
            (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c))) x) = c • Λ M hM x) ∧
      ∀ (M N : TopCat.{0}) [MetrizableSpace M] [MetrizableSpace N]
        (hM : LocallyContractibleSpace M) (hN : LocallyContractibleSpace N) (f : N ⟶ M) x,
        Λ N hN ((MMP.Analytic.sheafCohomologyPullback f (constSh M) n ≫
          (MMP.Analytic.sheafCohomology N n).map (toConst f)) x) =
          relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) f (Set.empty_subset _) n
            (Λ M hM x) := by
  obtain ⟨E, hE, hEc⟩ := MMP.Analytic.exists_sheafCohomology_constantSheaf_iso_singularCohomology_natural
  let σ : ∀ M : TopCat.{0}, relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) M ∅ n ≃+
      ((singAb ℂ).obj (op M)).homology n :=
    fun M ↦ (totalIso ℂ ℂ M n).addCommGroupIsoToAddEquiv
  refine ⟨fun M _ hM ↦ (E (.of ℂ) M hM n).addCommGroupIsoToAddEquiv.trans (σ M).symm, ?_, ?_⟩
  · intro M _ hM c x
    have h := ConcreteCategory.congr_hom (hEc (.of ℂ) (.of ℂ)
      (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)) M hM n) x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    apply (σ M).injective
    change (σ M) ((σ M).symm ((E (.of ℂ) M hM n).hom ((MMP.Analytic.sheafCohomology M n).map
          ((constantSheaf _ AddCommGrpCat.{0}).map
            (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c))) x))) =
      (σ M) (c • (σ M).symm ((E (.of ℂ) M hM n).hom x))
    erw [AddEquiv.apply_symm_apply]
    have hs := totalIso_smul (R := ℂ) (A := ℂ) M n c ((σ M).symm ((E (.of ℂ) M hM n).hom x))
    change (σ M) (c • (σ M).symm ((E (.of ℂ) M hM n).hom x)) = _ at hs
    have e2 : (totalIso ℂ ℂ M n).hom ((σ M).symm ((E (.of ℂ) M hM n).hom x)) =
        (E (.of ℂ) M hM n).hom x := (σ M).apply_symm_apply _
    erw [hs, e2]
    exact h
  · intro M N _ _ hM hN f x
    have key := ConcreteCategory.congr_hom (hE (.of ℂ) M N hM hN f n) x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      at key
    apply (σ N).injective
    change (σ N) ((σ N).symm ((E (.of ℂ) N hN n).hom ((MMP.Analytic.sheafCohomologyPullback f
        (constSh M) n ≫ (MMP.Analytic.sheafCohomology N n).map (toConst f)) x))) =
      (σ N) ((relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) f (Set.empty_subset _) n)
        ((σ M).symm ((E (.of ℂ) M hM n).hom x)))
    erw [AddEquiv.apply_symm_apply]
    have hn := ConcreteCategory.congr_hom (totalIso_naturality (R := ℂ) (A := ℂ) f n)
      ((σ M).symm ((E (.of ℂ) M hM n).hom x))
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
    change (σ N) _ = HomologicalComplex.homologyMap ((singAb ℂ).map f.op) n
      ((σ M) ((σ M).symm ((E (.of ℂ) M hM n).hom x))) at hn
    erw [hn, AddEquiv.apply_symm_apply, ConcreteCategory.comp_apply]
    exact key.symm

end Lambda

end SingCmp

end SingCmpOpens

namespace DRCmp

section QIso

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] globalSections_additive

variable (T : TopCat.{u})

/-- Godement hypercohomology inverts quasi-isomorphisms of bounded below complexes. -/
public theorem isIso_hypercohomology_map_of_quasiIso
    {K L : CochainComplex.Plus (TopCat.Sheaf AddCommGrpCat.{u} T)} (φ : K ⟶ L)
    [hφ : QuasiIso φ.hom] (n : ℤ) : IsIso ((hypercohomology T n).map φ.hom) := by
  have hQ : IsIso (DerivedCategory.Plus.Q.map φ) := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map φ)) := by
      change IsIso (DerivedCategory.Q.map φ.hom)
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact hφ
    exact isIso_of_fully_faithful DerivedCategory.Plus.ι _
  have h := (bridgeIso T n).hom.naturality φ
  have h2 : IsIso ((DerivedCategory.Plus.Q ⋙ (globalSections T).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map φ) := by
    change IsIso ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
      ((globalSections T).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ)))
    infer_instance
  have h3 : (CochainComplex.Plus.ι _ ⋙ hypercohomology T n).map φ =
      CategoryTheory.inv ((bridgeIso T n).hom.app K) ≫
        (DerivedCategory.Plus.Q ⋙ (globalSections T).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map φ ≫
        (bridgeIso T n).hom.app L := by
    rw [h, IsIso.inv_hom_id_assoc]
  change IsIso ((CochainComplex.Plus.ι _ ⋙ hypercohomology T n).map φ)
  rw [h3]
  infer_instance

end QIso

section AlgZ

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (d : ℕ)

/-- Degrees, with negative degrees sent to `d + 1`. -/
def fdeg : ℤ → ℕ
  | Int.ofNat k => k
  | Int.negSucc _ => d + 1

/-- The modules of the de Rham complex, `Ω^{d+1} = 0` standing in negative degrees. -/
noncomputable abbrev FZ (p : ℤ) : X.Modules := sX.relativeDifferentialForms (fdeg d p : ℤ)

/-- Stacks' de Rham complex of abelian sheaves. -/
public noncomputable abbrev dRN :=
  AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras sX)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))

/-- The de Rham differential in degree `k`, as a map of abelian sheaves. -/
@[expose] public noncomputable def dZ (k : ℕ) : (SheafOfModules.toSheaf X.ringCatSheaf).obj
    (sX.relativeDifferentialForms (k : ℤ)) ⟶
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ)) :=
  (dRN sX).d k (k + 1)

/-- The de Rham differential in degree `p ∈ ℤ`, zero in negative degrees. -/
noncomputable def δZ : ∀ p : ℤ, (SheafOfModules.toSheaf X.ringCatSheaf).obj (FZ sX d p) ⟶
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (FZ sX d (p + 1))
  | Int.ofNat k => dZ sX k
  | Int.negSucc _ => 0

/-- The differentials `δZ` compose to zero. -/
lemma δZ_comp : ∀ p : ℤ, δZ sX d p ≫ δZ sX d (p + 1) = 0
  | Int.ofNat k => HomologicalComplex.d_comp_d _ _ _ _
  | Int.negSucc _ => zero_comp

/-- The algebraic de Rham complex in the form taken by GAGA. -/
noncomputable abbrev KZ : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X.carrier) ℤ :=
  CochainComplex.of (fun p => (SheafOfModules.toSheaf X.ringCatSheaf).obj (FZ sX d p))
    (δZ sX d) (δZ_comp sX d)

/-- Stacks' de Rham complex, extended by zero to `ℤ`. -/
noncomputable abbrev dRInt := (dRN sX).extend ComplexShape.embeddingUpNat

variable [SmoothOfRelativeDimension d sX]

/-- The de Rham modules vanish in negative degrees. -/
lemma isZero_FZ_negSucc (j : ℕ) : IsZero (FZ sX d (Int.negSucc j)) :=
  isZero_relativeDifferentialForms_of_lt sX d _ (by simp [fdeg])

/-- The underlying abelian sheaves of the de Rham modules vanish in negative degrees. -/
lemma isZero_toSheaf_FZ_negSucc (j : ℕ) :
    IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj (FZ sX d (Int.negSucc j))) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map_isZero (isZero_FZ_negSucc sX d j)

/-- The components of the comparison with Stacks' de Rham complex. -/
noncomputable def eKZX : ∀ p : ℤ, (KZ sX d).X p ≅ (dRInt sX).X p
  | Int.ofNat k => (HomologicalComplex.extendXIso (dRN sX) ComplexShape.embeddingUpNat
      (i := k) (i' := Int.ofNat k) rfl).symm
  | Int.negSucc j => (isZero_toSheaf_FZ_negSucc sX d j).iso
      (HomologicalComplex.isZero_extend_X _ _ _ (fun k => by
        change ((k : ℕ) : ℤ) ≠ Int.negSucc j; omega))

/-- The algebraic de Rham complex is Stacks' de Rham complex of abelian sheaves. -/
noncomputable def eKZ : KZ sX d ≅ dRInt sX :=
  HomologicalComplex.Hom.isoOfComponents (eKZX sX d) (by
    rintro i _ rfl
    cases i with
    | ofNat k =>
      rw [show (KZ sX d).d (Int.ofNat k) (Int.ofNat k + 1) = δZ sX d (Int.ofNat k) from
        CochainComplex.of_d _ (δZ sX d) (Int.ofNat k)]
      change (HomologicalComplex.extendXIso (dRN sX) ComplexShape.embeddingUpNat
          (i := k) (i' := Int.ofNat k) rfl).inv ≫ (dRInt sX).d (Int.ofNat k) (Int.ofNat k + 1) =
        dZ sX k ≫ (HomologicalComplex.extendXIso (dRN sX) ComplexShape.embeddingUpNat
          (i := k + 1) (i' := Int.ofNat k + 1) rfl).inv
      rw [HomologicalComplex.extend_d_eq (dRN sX) ComplexShape.embeddingUpNat (i := k) (j := k + 1)
        (i' := Int.ofNat k) (j' := Int.ofNat k + 1)
        (rfl : ComplexShape.embeddingUpNat.f k = Int.ofNat k)
        (rfl : ComplexShape.embeddingUpNat.f (k + 1) = Int.ofNat k + 1), Iso.inv_hom_id_assoc]
      rfl
    | negSucc j => exact (isZero_toSheaf_FZ_negSucc sX d j).eq_of_src _ _)

end AlgZ

section AnZ

attribute [local implicit_reducible] TopCat.Sheaf

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (d : ℕ)
variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
  (C : ∀ y, ChartData sX n Θ y)

/-- The holomorphic de Rham differential in degree `p ∈ ℤ`, zero in negative degrees. -/
noncomputable def δanZ : ∀ p : ℤ,
    (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (FZ sX d p)) ⟶
      (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (FZ sX d (p + 1)))
  | Int.ofNat k => δan sX hΘ C k
  | Int.negSucc _ => 0

/-- The differentials `δanZ` compose to zero. -/
lemma δanZ_comp : ∀ p : ℤ, δanZ sX d hΘ C p ≫ δanZ sX d hΘ C (p + 1) = 0
  | Int.ofNat k => δan_comp_δan sX hΘ C k
  | Int.negSucc _ => zero_comp

/-- The holomorphic de Rham complex, indexed by `ℤ`. -/
noncomputable abbrev KanZ : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} (space sX)) ℤ :=
  CochainComplex.of (fun p => (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj (FZ sX d p)))
    (δanZ sX d hΘ C) (δanZ_comp sX d hΘ C)

/-- Analytification of modules is a left adjoint. -/
theorem isLeftAdjoint_analytifyModule : (analytifyModule sX).IsLeftAdjoint :=
  (SheafOfModules.pullbackPushforwardAdjunction.{0} (ringCatSheafHom sX)).isLeftAdjoint

attribute [local instance] isLeftAdjoint_analytifyModule

/-- Pullback of abelian sheaves along `X^an ⟶ X` is a left adjoint. -/
theorem isLeftAdjoint_pullback_toSchemeHom : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).IsLeftAdjoint :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (toSchemeHom sX)).isLeftAdjoint

attribute [local instance] isLeftAdjoint_pullback_toSchemeHom

variable [SmoothOfRelativeDimension d sX]

/-- The holomorphic de Rham complex vanishes in negative degrees. -/
lemma isZero_KanZ_negSucc (j : ℕ) : IsZero ((KanZ sX d hΘ C).X (Int.negSucc j)) :=
  haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint (analytifyModule sX)
  (SheafOfModules.toSheaf _).map_isZero ((analytifyModule sX).map_isZero (isZero_FZ_negSucc sX d j))

omit [SmoothOfRelativeDimension d sX] in
/-- On sections, `dZ` is the de Rham differential. -/
public lemma dZ_app (k : ℕ) (V : X.Opens)
    (s : ((SheafOfModules.toSheaf X.ringCatSheaf).obj (sX.relativeDifferentialForms (k : ℤ))).obj.obj (op V)) :
    (dZ sX k).hom.app (op V) s = ((sX.deRhamComplex).d k (k + 1)).val.app (op V) s := by
  change ((AlgebraicGeometry.SheafOfModules.deRhamComplex _ _).d k (k + 1)).val.app (op V) s = _
  erw [AlgebraicGeometry.SheafOfModules.deRhamComplex_d]
  rfl

set_option maxRecDepth 10000 in
include hΘ in
/-- The analytification unit `Ω^k ⟶ h_* Ω^k_an` commutes with the algebraic and holomorphic de
Rham differentials. -/
theorem unit_comm (k : ℕ) :
    dZ sX k ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map
        (analytifyModuleUnit sX (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ))) =
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (analytifyModuleUnit sX (sX.relativeDifferentialForms (k : ℤ))) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).map (δan sX hΘ C k) :) := by
  refine ObjectProperty.hom_ext _ (TopCat.Sheaf.hom_ext _ _
    (B := fun V : X.affineOpens => (V : X.Opens)) (by simpa using X.isBasis_affineOpens)
    fun V => ?_)
  ext s
  change (analytifyModuleUnit sX (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ))).val.app (op V)
      ((dZ sX k).hom.app (op V) s) =
    (δan sX hΘ C k).hom.app (op ((Opens.map (toSchemeHom sX)).obj V))
      ((analytifyModuleUnit sX (sX.relativeDifferentialForms (k : ℤ))).val.app (op V) s)
  rw [δan_unit sX hΘ C k V V.2 s, dZ_app]

/-- The comparison `α⁻¹ Ω^•_X ⟶ Ω^•_{X^an}` commutes with `dZ` and `δan`. -/
public theorem ι_comm (k : ℕ) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).map (dZ sX k) ≫
        analytifyModuleι sX (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ)) =
      analytifyModuleι sX (sX.relativeDifferentialForms (k : ℤ)) ≫ δan sX hΘ C k := by
  have h1 := Adjunction.homEquiv_naturality_left_symm
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (toSchemeHom sX))
    (Y := (SheafOfModules.toSheaf _).obj
      ((analytifyModule sX).obj (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ)))) (dZ sX k)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (analytifyModuleUnit sX (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ))))
  have h2 := Adjunction.homEquiv_naturality_right_symm
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (toSchemeHom sX))
    (Y := (SheafOfModules.toSheaf _).obj
      ((analytifyModule sX).obj (sX.relativeDifferentialForms (k : ℤ))))
    ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (analytifyModuleUnit sX (sX.relativeDifferentialForms (k : ℤ)))) (δan sX hΘ C k)
  erw [unit_comm sX hΘ C k] at h1
  exact h1.symm.trans h2

/-- The pullback to `X^an` of the algebraic de Rham complex vanishes in negative degrees. -/
lemma isZero_pullback_KZ_negSucc (j : ℕ) :
    IsZero (((complexPullback (toSchemeHom sX)).obj (KZ sX d)).X (Int.negSucc j)) := by
  haveI := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX))
  exact (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).map_isZero
    (isZero_toSheaf_FZ_negSucc sX d j)

omit [SmoothOfRelativeDimension d sX] in
/-- In degree `k ≥ 0`, the differential of `KZ` is the de Rham differential `dZ`. -/
lemma KZ_d (k : ℕ) : (KZ sX d).d (Int.ofNat k) (Int.ofNat k + 1) = dZ sX k :=
  CochainComplex.of_d _ (δZ sX d) (Int.ofNat k)

omit [SmoothOfRelativeDimension d sX] in
/-- In degree `k ≥ 0`, the differential of `KanZ` is the holomorphic differential `δan`. -/
lemma KanZ_d (k : ℕ) : (KanZ sX d hΘ C).d (Int.ofNat k) (Int.ofNat k + 1) = δan sX hΘ C k :=
  CochainComplex.of_d _ (δanZ sX d hΘ C) (Int.ofNat k)

/-- The comparison `α⁻¹ Ω^•_X ⟶ Ω^•_{X^an}`. -/
noncomputable def ιZ : (complexPullback (toSchemeHom sX)).obj (KZ sX d) ⟶ KanZ sX d hΘ C where
  f p := analytifyModuleι sX (FZ sX d p)
  comm' := by
    rintro i _ rfl
    cases i with
    | ofNat k =>
      change analytifyModuleι sX (FZ sX d (Int.ofNat k)) ≫
          (KanZ sX d hΘ C).d (Int.ofNat k) (Int.ofNat k + 1) =
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).map
          ((KZ sX d).d (Int.ofNat k) (Int.ofNat k + 1)) ≫
            analytifyModuleι sX (FZ sX d (Int.ofNat k + 1))
      rw [KZ_d, KanZ_d]
      exact (ι_comm sX hΘ C k).symm
    | negSucc j => exact (isZero_pullback_KZ_negSucc sX d j).eq_of_src _ _

/-- The inclusion of the constants into the holomorphic de Rham complex. -/
noncomputable def εZ : (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{0} (space sX))
    (ComplexShape.up ℤ) 0).obj
    ((constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of ℂ)) ⟶ KanZ sX d hΘ C :=
  HomologicalComplex.mkHomFromSingle (εan sX hΘ C) (by
    intro k hk
    change (0 : ℤ) + 1 = k at hk
    subst hk
    exact (congrArg (εan sX hΘ C ≫ ·) (KanZ_d sX d hΘ C 0)).trans (εan_comp_δan sX hΘ C))

omit [SmoothOfRelativeDimension d sX] in
/-- In degree `0`, the inclusion of the constants is `εan`. -/
lemma εZ_f_zero : (εZ sX d hΘ C).f 0 =
    (HomologicalComplex.singleObjXSelf (V := TopCat.Sheaf AddCommGrpCat.{0} (space sX))
      (ComplexShape.up ℤ) 0 ((constantSheaf (Opens.grothendieckTopology (space sX))
        AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ))).hom ≫ εan sX hΘ C := by
  unfold εZ
  exact HomologicalComplex.mkHomFromSingle_f _ _

/-- The holomorphic de Rham complex is exact in every positive degree. -/
lemma exactAt_KanZ_succ (k : ℕ) : (KanZ sX d hΘ C).ExactAt (Int.ofNat (k + 1)) := by
  change (KanZ sX d hΘ C).ExactAt (Int.ofNat k + 1)
  rw [HomologicalComplex.exactAt_iff' _ (Int.ofNat k) (Int.ofNat k + 1) (Int.ofNat k + 1 + 1)
    (by simp) (by simp)]
  refine (ShortComplex.exact_iff_of_iso ?_).2 (exact_δan sX hΘ C k)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ δan sX hΘ C k = (KanZ sX d hΘ C).d (Int.ofNat k) (Int.ofNat k + 1) ≫ 𝟙 _
    rw [KanZ_d, Category.id_comp]
    exact (Category.comp_id _).symm
  · change 𝟙 _ ≫ δan sX hΘ C (k + 1) =
      (KanZ sX d hΘ C).d (Int.ofNat (k + 1)) (Int.ofNat (k + 1) + 1) ≫ 𝟙 _
    rw [KanZ_d, Category.id_comp]
    exact (Category.comp_id _).symm

/-- The inclusion of the constants `ℂ_{X^an} ⟶ Ω^•_{X^an}` is a quasi-isomorphism. -/
theorem quasiIso_εZ : QuasiIso (εZ sX d hΘ C) := ⟨fun q => by
  rcases q with (_ | k) | j
  · change QuasiIsoAt (εZ sX d hΘ C) 0
    rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp),
      ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨exact_εan sX hΘ C, mono_εan sX hΘ C⟩
      refine ShortComplex.isoMk (HomologicalComplex.singleObjXSelf
        (V := TopCat.Sheaf AddCommGrpCat.{0} (space sX)) (ComplexShape.up ℤ) 0
          ((constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).obj
            (AddCommGrpCat.of ℂ))) (Iso.refl _) (Iso.refl _) ?_ ?_
      · change (HomologicalComplex.singleObjXSelf _ 0 _).hom ≫ εan sX hΘ C =
          (εZ sX d hΘ C).f 0 ≫ 𝟙 _
        erw [Category.comp_id]
        exact (εZ_f_zero sX d hΘ C).symm
      · change 𝟙 _ ≫ δan sX hΘ C 0 = (KanZ sX d hΘ C).d (Int.ofNat 0) (Int.ofNat 0 + 1) ≫ 𝟙 _
        rw [KanZ_d, Category.id_comp]
        exact (Category.comp_id _).symm
    · exact (HomologicalComplex.isZero_single_obj_X (V := TopCat.Sheaf AddCommGrpCat.{0} (space sX))
        (ComplexShape.up ℤ) 0 ((constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ)) (-1) (by norm_num)).eq_of_src _ _
    · exact (HomologicalComplex.isZero_single_obj_X (V := TopCat.Sheaf AddCommGrpCat.{0} (space sX))
        (ComplexShape.up ℤ) 0 ((constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ)) 1 (by norm_num)).eq_of_tgt _ _
    · exact (isZero_KanZ_negSucc sX d hΘ C 0).eq_of_src _ _
  · rw [quasiIsoAt_iff_exactAt]
    · exact exactAt_KanZ_succ sX d hΘ C k
    · exact HomologicalComplex.exactAt_single_obj _ _ _ _ (by change ((k : ℤ) + 1) ≠ 0; omega)
  · rw [quasiIsoAt_iff_exactAt]
    · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_KanZ_negSucc sX d hΘ C j)
    · exact HomologicalComplex.exactAt_single_obj _ _ _ _ (by simp)⟩

end AnZ

section Linear

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- The restriction to `U` of the base scalar `c` is the image of `c` in `Γ(X, U)`. -/
lemma restrictGlobal_baseScalars (c : ℂ) (U : X.Opens) :
    Stacks.Perfect.FractionClass.resTop ((baseHom sX).hom.app (op ⊤) (baseScalars sX c)) (op U) =
      ComplexPoints.baseRingHom sX U c := by
  rw [baseHom_baseScalars]
  simp only [Stacks.Perfect.FractionClass.resTop, ComplexPoints.baseRingHom, Scheme.Hom.appLE,
    CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply]
  erw [X.presheaf.map_id]
  rfl

/-- The de Rham differential commutes with multiplication by a global section of the base. -/
lemma dZ_globalSmul (k : ℕ) (t : (baseSheaf sX).obj.obj (op ⊤)) :
    dZ sX k ≫ (_root_.SheafOfModules.toSheaf _).map
        (Stacks.Perfect.FractionClass.smulHom ((baseHom sX).hom.app (op ⊤) t) _) =
      (_root_.SheafOfModules.toSheaf _).map
        (Stacks.Perfect.FractionClass.smulHom ((baseHom sX).hom.app (op ⊤) t) _) ≫ dZ sX k := by
  rw [← toSheaf_smulEnd_restrictScalars, ← toSheaf_smulEnd_restrictScalars]
  unfold dZ dRN
  erw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp, ← Functor.map_comp,
    smulEnd_naturality]
  rfl

end Linear

section GAGAApp

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (d : ℕ)
variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
  (C : ∀ y, ChartData sX n Θ y)

variable [SmoothOfRelativeDimension d sX]

/-- The de Rham differential is `ℂ`-linear on sections over each open. -/
lemma δZ_smul (p : ℤ) (U : X.Opens) (c : ℂ) (s : (FZ sX d p).val.obj (op U)) :
    (δZ sX d p).hom.app (op U)
        ((show X.ringCatSheaf.obj.obj (op U) from ComplexPoints.baseRingHom sX U c) • s) =
      (show X.ringCatSheaf.obj.obj (op U) from ComplexPoints.baseRingHom sX U c) •
        (show (FZ sX d (p + 1)).val.obj (op U) from (δZ sX d p).hom.app (op U) s) := by
  cases p with
  | ofNat k =>
    have h := congrArg (fun φ => φ.hom.app (op U) s) (dZ_globalSmul sX k (baseScalars sX c))
    change Stacks.Perfect.FractionClass.resTop
        ((baseHom sX).hom.app (op ⊤) (baseScalars sX c)) (op U) •
        (show (sX.relativeDifferentialForms ((k + 1 : ℕ) : ℤ)).val.obj (op U) from
          (dZ sX k).hom.app (op U) s) =
      (dZ sX k).hom.app (op U)
        (Stacks.Perfect.FractionClass.resTop
          ((baseHom sX).hom.app (op ⊤) (baseScalars sX c)) (op U) • s) at h
    rw [restrictGlobal_baseScalars] at h
    exact h.symm
  | negSucc j =>
    have hz : IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (FZ sX d (Int.negSucc j))).obj.obj (op U)) :=
      ((sheafSections _ _).obj (op U)).map_isZero (isZero_toSheaf_FZ_negSucc sX d j)
    haveI := (AddCommGrpCat.isZero_iff_subsingleton).1 hz
    have hs : s = 0 := Subsingleton.elim (α := ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (FZ sX d (Int.negSucc j))).obj.obj (op U)) _ _
    subst hs
    erw [smul_zero, map_zero]
    exact (smul_zero (M := X.ringCatSheaf.obj.obj (op U))
      (A := (FZ sX d (Int.negSucc j + 1)).val.obj (op U)) _).symm

omit [SmoothOfRelativeDimension d sX] in
/-- For `X` locally of finite type, the de Rham modules are coherent. -/
lemma isCoherent_FZ [LocallyOfFiniteType sX] (p : ℤ) : Stacks.SheafOfModules.IsCoherent (FZ sX d p) :=
  let h := Scheme.Hom.isCoherent_relativeDifferentialForms sX (fdeg d p)
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- The de Rham modules vanish outside degrees `[0, d]`. -/
lemma isZero_FZ (p : ℤ) (hp : p < 0 ∨ (d : ℤ) < p) : IsZero (FZ sX d p) := by
  cases p with
  | ofNat k =>
    refine isZero_relativeDifferentialForms_of_lt sX d _ ?_
    change (d : ℤ) < (k : ℤ)
    rcases hp with hp | hp
    · exact absurd hp (by simp)
    · exact hp
  | negSucc j => exact isZero_FZ_negSucc sX d j

include hΘ in
/-- **GAGA for the de Rham complex**: for `X` projective, pullback to `X^an` followed by the
comparison `α⁻¹ Ω^•_X ⟶ Ω^•_{X^an}` is an isomorphism on hypercohomology. -/
theorem isIso_gaga [IsProjectiveVariety ℂ sX] (m : ℤ) :
    IsIso (hypercohomologyPullback (toSchemeHom sX) (KZ sX d) m ≫
      (hypercohomology (space sX) m).map (ιZ sX d hΘ C)) := by
  have hP : IsProjective sX := (isProjectiveVariety_iff_isProjective ℂ sX).mp inferInstance
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  exact MMP.Analytic.isIso_hypercohomologyComparison_of_isProjective sX hP (FZ sX d)
    (isCoherent_FZ sX d) 0 d (isZero_FZ sX d) (δZ sX d) (δZ_smul sX d) (δZ_comp sX d)
    (δanZ sX d hΘ C) (δanZ_comp sX d hΘ C) (ιZ sX d hΘ C) (fun p => rfl) m

end GAGAApp

section AbLinear

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

open Stacks.SheafOfModules.Tensor (ringSheaf)

variable {Xr : RingedSpace.{0}} {A : TopCat.Sheaf CommRingCat.{0} Xr.carrier} {φ : A ⟶ Xr.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology Xr.carrier)
      (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{0, 0, 0} φ))
  (D : AlgebraicGeometry.SheafOfModules.DeRhamDifferential B)

/-- Multiplication by a global section of the base on the de Rham complex of abelian sheaves. -/
noncomputable def ψdR (r : A.obj.obj (op ⊤)) :
    AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus B D ⟶
      AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus B D :=
  (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso B D).hom ≫
    (SheafOfModules.toSheaf _).mapCochainComplexPlus.map (ObjectProperty.homMk
      (smulComplex A r (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus B D).obj)) ≫
    (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso B D).inv

/-- Under the identification of abelian and module-valued de Rham cohomology, the map induced
by multiplication by `r` on the de Rham complex is scalar multiplication by `r`. -/
theorem abIso_hom_ψdR (r : A.obj.obj (op ⊤)) (n : ℤ)
    (x : AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelian B D n) :
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology B D n).hom
        (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} n).map
          ((Stacks.Cohomology.Leray.sectionsFunctor Xr.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map (ψdR B D r)))) x) =
      (show AlgebraicGeometry.SheafOfModules.deRhamCohomology B D n from
      (show ((AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤)) from r) •
        (show AlgebraicGeometry.SheafOfModules.deRhamCohomology B D n from
          (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology B D
            n).hom x)) := by
  have h1 := Stacks.Cech.Hypercohomology.realizationIsoOfIso_naturality
    (AlgebraicGeometry.SheafOfModules.baseRingedSpace A)
    (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso B D)
    (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso B D) (ψdR B D r)
    (ObjectProperty.homMk (smulComplex A r
      (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus B D).obj))
    (by unfold ψdR; erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl) n
  have h3 := hypercohomologyMap_smulComplex A
    (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus B D) r n
  erw [h3] at h1
  have h2 := ConcreteCategory.congr_hom h1 x
  change (Stacks.Cech.Hypercohomology.realizationIsoOfIso
        (AlgebraicGeometry.SheafOfModules.baseRingedSpace A)
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso B D) n).hom
      (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} n).map
          ((Stacks.Cohomology.Leray.sectionsFunctor Xr.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map (ψdR B D r)))) x) =
    (show Stacks.Cech.Hypercohomology.hypercohomology A
      (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus B D) n from
    (show ((AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤)) from r) •
      (show Stacks.Cech.Hypercohomology.hypercohomology A
        (AlgebraicGeometry.SheafOfModules.deRhamComplexPlus B D) n from
      (Stacks.Cech.Hypercohomology.realizationIsoOfIso
        (AlgebraicGeometry.SheafOfModules.baseRingedSpace A)
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso B D) n).hom x)) at h2
  change (AlgebraicGeometry.SheafOfModules.hypercohomologyIsoDeRhamCohomology B D n).hom
      ((Stacks.Cech.Hypercohomology.realizationIsoOfIso
        (AlgebraicGeometry.SheafOfModules.baseRingedSpace A)
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso B D) n).hom _) = _
  rw [h2]
  exact (AlgebraicGeometry.SheafOfModules.hypercohomologyIsoDeRhamCohomology B D n).hom.hom.map_smul
    _ _

/-- In degree `k ≥ 0`, multiplication by `r` on the de Rham complex is multiplication by `r` on
its `k`-th term. -/
theorem ψdR_f (r : A.obj.obj (op ⊤)) (k : ℕ) :
    (ψdR B D r).hom.f (Int.ofNat k) =
      ((AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex B D).extendXIso
          ComplexShape.embeddingUpNat (i := k) (i' := Int.ofNat k) rfl).hom ≫
        (SheafOfModules.toSheaf _).map
          (smulEnd A r ((AlgebraicGeometry.SheafOfModules.deRhamComplex B D).X k)) ≫
        ((AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex B D).extendXIso
          ComplexShape.embeddingUpNat (i := k) (i' := Int.ofNat k) rfl).inv := by
  change (HomologicalComplex.mapHomologicalComplexExtendIso (SheafOfModules.toSheaf _)
      (AlgebraicGeometry.SheafOfModules.deRhamComplex B D) ComplexShape.embeddingUpNat).hom.f _ ≫
      (SheafOfModules.toSheaf _).map (smulEnd A r _) ≫
      (HomologicalComplex.mapHomologicalComplexExtendIso (SheafOfModules.toSheaf _)
      (AlgebraicGeometry.SheafOfModules.deRhamComplex B D) ComplexShape.embeddingUpNat).inv.f _ = _
  rw [HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ (i := k) (i' := Int.ofNat k)
      rfl, GodPull.mapHCExtendIso_inv_f _ _ _ (i := k) (i' := Int.ofNat k) rfl]
  simp only [Category.assoc]
  congr 1
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  erw [smulEnd_naturality, Iso.inv_hom_id_assoc]
  rfl

end AbLinear

section MC

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (d : ℕ) [SmoothOfRelativeDimension d sX]

/-- Multiplication by a base scalar on the algebraic de Rham complex. -/
noncomputable def mC (t : (baseSheaf sX).obj.obj (op ⊤)) : KZ sX d ⟶ KZ sX d where
  f p := (_root_.SheafOfModules.toSheaf _).map
    (Stacks.Perfect.FractionClass.smulHom ((baseHom sX).hom.app (op ⊤) t) (FZ sX d p))
  comm' := by
    rintro i _ rfl
    cases i with
    | ofNat k =>
      change (_root_.SheafOfModules.toSheaf _).map (Stacks.Perfect.FractionClass.smulHom _ _) ≫
          (KZ sX d).d (Int.ofNat k) (Int.ofNat k + 1) =
        (KZ sX d).d (Int.ofNat k) (Int.ofNat k + 1) ≫
          (_root_.SheafOfModules.toSheaf _).map (Stacks.Perfect.FractionClass.smulHom _ _)
      rw [KZ_d]
      exact (dZ_globalSmul sX k t).symm
    | negSucc j => exact (isZero_toSheaf_FZ_negSucc sX d j).eq_of_src _ _

/-- The isomorphism `eKZ` intertwines multiplication by `t` on both de Rham complexes. -/
theorem eKZ_ψdR (t : (baseSheaf sX).obj.obj (op ⊤)) :
    (eKZ sX d).hom ≫ (ψdR _ _ t).hom = mC sX d t ≫ (eKZ sX d).hom := by
  ext p : 1
  cases p with
  | ofNat k =>
    have hψ := ψdR_f (Scheme.Hom.deRhamAlgebras sX)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) t k
    refine (congrArg ((eKZ sX d).hom.f (Int.ofNat k) ≫ ·) hψ).trans ?_
    change (HomologicalComplex.extendXIso (dRN sX) ComplexShape.embeddingUpNat
        (i := k) (i' := Int.ofNat k) rfl).inv ≫ (HomologicalComplex.extendXIso (dRN sX)
          ComplexShape.embeddingUpNat (i := k) (i' := Int.ofNat k) rfl).hom ≫ _ ≫ _ =
      (_root_.SheafOfModules.toSheaf _).map (Stacks.Perfect.FractionClass.smulHom _ _) ≫
        (HomologicalComplex.extendXIso (dRN sX) ComplexShape.embeddingUpNat
          (i := k) (i' := Int.ofNat k) rfl).inv
    rw [Iso.inv_hom_id_assoc]
    have h := toSheaf_smulEnd_restrictScalars sX t ((Scheme.Hom.deRhamAlgebras sX).exteriorPower k)
    refine Eq.trans ?_ (congrArg (fun φ => φ ≫ (HomologicalComplex.extendXIso (dRN sX)
      ComplexShape.embeddingUpNat (i := k) (i' := Int.ofNat k) rfl).inv) h)
    rfl
  | negSucc j => exact (isZero_toSheaf_FZ_negSucc sX d j).eq_of_src _ _

end MC

section AnLinear

attribute [local implicit_reducible] TopCat.Sheaf

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
  (C : ∀ y, ChartData sX n Θ y)

/-- The exterior derivative on a chart patch commutes with multiplication by a function that is
constant on the patch. -/
lemma δP_smul_const {y : ComplexPoints sX} (D : ChartData sX n Θ y) {p : ℕ}
    (O : Opens (EuclideanSpace ℂ (Fin n))) (r : (ringCatSheaf sX).obj.obj (op (patch sX D.φ O)))
    (c : ℂ) (hr : ∀ y', Θ.hom.hom.app (op (patch sX D.φ O)) r y' = c)
    (t : (Ωan sX p).val.obj (op (patch sX D.φ O))) :
    δP sX D O (r • t) = r • δP sX D O t := by
  apply D.inj (p + 1) O
  funext y'
  have hξ : ∀ y'' : patch sX D.φ O, (c • holExt sX D O t) (D.φ y'') = D.Ψ p O (r • t) y'' := by
    intro y''
    rw [D.smul, hr, Pi.smul_apply, (holExt_spec sX D O t).2]
  rw [Ψ_δP_of_ext sX D O _ _ hξ y', D.smul, hr, Ψ_δP, extDeriv_smul]

/-- Multiplication by a global analytic function on the sheaf of analytic `p`-forms. -/
noncomputable abbrev mulAn (r : (structureSheaf sX).obj.obj (op ⊤)) (M : SheafOfModules.{0} (ringCatSheaf sX)) :
    (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj M :=
  (SheafOfModules.toSheaf _).map (smulEnd (structureSheaf sX) r M)

include hΘ in
/-- The holomorphic de Rham differential commutes with multiplication by a constant global
analytic function. -/
theorem δan_mulAn (r : (structureSheaf sX).obj.obj (op ⊤)) (c : ℂ)
    (hr : ∀ (U : Opens (space sX)) (y' : U),
      Θ.hom.hom.app (op U) ((structureSheaf sX).obj.map (homOfLE le_top).op r) y' = c) (p : ℕ) :
    δan sX hΘ C p ≫ mulAn sX r (Ωan sX (p + 1)) = mulAn sX r (Ωan sX p) ≫ δan sX hΘ C p := by
  refine ObjectProperty.hom_ext _ (TopCat.Sheaf.hom_ext _ _ (isBasis_patchB sX C) fun i => ?_)
  ext t
  change (smulEnd (structureSheaf sX) r (Ωan sX (p + 1))).val.app _
      ((δan sX hΘ C p).hom.app _ t) =
    (δan sX hΘ C p).hom.app _ ((smulEnd (structureSheaf sX) r (Ωan sX p)).val.app _ t)
  erw [smulEnd_app, smulEnd_app, δan_app_patch, δan_app_patch]
  exact (δP_smul_const sX (C i.1) i.2 _ c (hr _) t).symm

include hΘ in
/-- The constant `0`-form `c * c'` is the product of the constant function `c` with the constant
`0`-form `c'`. -/
lemma εPre_smul (r : (structureSheaf sX).obj.obj (op ⊤)) (c : ℂ)
    (hr : ∀ (U : Opens (space sX)) (y' : U),
      Θ.hom.hom.app (op U) ((structureSheaf sX).obj.map (homOfLE le_top).op r) y' = c)
    (V : Opens (space sX)) (c' : ℂ) :
    (TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)).app (op V)
        (c * c') =
      (smulEnd (structureSheaf sX) r (Ωan sX 0)).val.app (op V)
        ((TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)).app
          (op V) c') := by
  refine TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf _).obj (Ωan sX 0)) _ _ _
    fun x hx => ?_
  obtain ⟨_, ⟨i, rfl⟩, hxB, hBV⟩ := (Opens.isBasis_iff_nbhd.mp (isBasis_patchB sX C)) hx
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hBV) x hxB]
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hBV) x hxB]
  congr 1
  have hn := PresheafOfModules.naturality_apply (smulEnd (structureSheaf sX) r (Ωan sX 0)).val
    (homOfLE hBV).op
    ((TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)).app (op V) c')
  erw [εPre_res sX hΘ C hBV, ← hn, εPre_res sX hΘ C hBV, smulEnd_app, εPre_app_patch,
    εPre_app_patch]
  apply (C i.1).inj 0 i.2
  funext y'
  erw [(C i.1).smul, hr, Ψ_εP, Ψ_εP]
  ext v
  simp

include hΘ in
/-- The inclusion of the constants intertwines multiplication by `c` on `ℂ_{X^an}` with
multiplication by the constant function `c` on `Ω⁰_an`. -/
theorem εan_mulAn (r : (structureSheaf sX).obj.obj (op ⊤)) (c : ℂ)
    (hr : ∀ (U : Opens (space sX)) (y' : U),
      Θ.hom.hom.app (op U) ((structureSheaf sX).obj.map (homOfLE le_top).op r) y' = c) :
    (constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).map
        (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)) ≫ εan sX hΘ C =
      εan sX hΘ C ≫ mulAn sX r (Ωan sX 0) := by
  refine ObjectProperty.hom_ext _ ?_
  change ((constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).map
      (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c))).hom ≫ (εan sX hΘ C).hom =
    (εan sX hΘ C).hom ≫ (mulAn sX r (Ωan sX 0)).hom
  refine sheafify_hom_ext _ _ _ ((SheafOfModules.toSheaf _).obj (Ωan sX 0)).property ?_
  ext V c'
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality
    (Opens.grothendieckTopology (space sX))
    ((Functor.const (Opens (space sX))ᵒᵖ).map
      (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)))) V) c'
  have h2 := fun x => ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_εan sX hΘ C) V) x
  change (εan sX hΘ C).hom.app V (((constantSheaf (Opens.grothendieckTopology (space sX))
      AddCommGrpCat.{0}).map (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c))).hom.app V
        ((toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX)).app V c')) =
    (smulEnd (structureSheaf sX) r (Ωan sX 0)).val.app V ((εan sX hΘ C).hom.app V
      ((toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX)).app V c'))
  erw [← hn, h2, h2]
  exact εPre_smul sX hΘ C r c hr V.unop c'

/-- The analytification of a global function. -/
noncomputable abbrev anGlobal (a : Γ(X, ⊤)) : (structureSheaf sX).obj.obj (op ⊤) :=
  (analytificationHom sX).hom.c.app (op ⊤) a

/-- The analytification unit `F ⟶ h_* F^an` intertwines multiplication by a global function `a`
with multiplication by its analytification. -/
theorem unit_globalSmul (F : X.Modules) (a : Γ(X, ⊤)) :
    (_root_.SheafOfModules.toSheaf _).map (Stacks.Perfect.FractionClass.smulHom a F) ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map (analytifyModuleUnit sX F) =
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (analytifyModuleUnit sX F) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).map
          (mulAn sX (anGlobal sX a) ((analytifyModule sX).obj F)) :) := by
  ext U s
  change (analytifyModuleUnit sX F).val.app U (Stacks.Perfect.FractionClass.resTop a U •
      (show F.val.obj U from s)) =
    (smulEnd (structureSheaf sX) (anGlobal sX a) ((analytifyModule sX).obj F)).val.app
      (op ((Opens.map (toSchemeHom sX)).obj U.unop)) ((analytifyModuleUnit sX F).val.app U s)
  refine (((analytifyModuleUnit sX F).val.app U).hom.map_smul _ _).trans ?_
  have hn := ConcreteCategory.congr_hom
    ((analytificationHom sX).hom.c.naturality (homOfLE (le_top : U.unop ≤ ⊤)).op) a
  change (show (ringCatSheaf sX).obj.obj (op ((Opens.map (toSchemeHom sX)).obj U.unop)) from
      (analytificationHom sX).hom.c.app U (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a)) •
        (show ((analytifyModule sX).obj F).val.obj (op ((Opens.map (toSchemeHom sX)).obj U.unop))
          from (analytifyModuleUnit sX F).val.app U s) =
    (show (ringCatSheaf sX).obj.obj (op ((Opens.map (toSchemeHom sX)).obj U.unop)) from
      (structureSheaf sX).obj.map (homOfLE le_top).op (anGlobal sX a)) •
        (show ((analytifyModule sX).obj F).val.obj (op ((Opens.map (toSchemeHom sX)).obj U.unop))
          from (analytifyModuleUnit sX F).val.app U s)
  congr 1

/-- The map `h⁻¹ F ⟶ F^an` intertwines multiplication by a global function `a` with
multiplication by its analytification. -/
theorem ι_mulAn (F : X.Modules) (a : Γ(X, ⊤)) :
    analytifyModuleι sX F ≫ mulAn sX (anGlobal sX a) ((analytifyModule sX).obj F) =
      (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).map
        ((_root_.SheafOfModules.toSheaf _).map (Stacks.Perfect.FractionClass.smulHom a F)) ≫
          analytifyModuleι sX F := by
  unfold analytifyModuleι
  have h1 := Adjunction.homEquiv_naturality_left_symm
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (toSchemeHom sX))
    (Y := (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F))
    ((_root_.SheafOfModules.toSheaf _).map (Stacks.Perfect.FractionClass.smulHom a F))
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (analytifyModuleUnit sX F))
  have h2 := Adjunction.homEquiv_naturality_right_symm
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (toSchemeHom sX))
    (Y := (SheafOfModules.toSheaf _).obj ((analytifyModule sX).obj F))
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (analytifyModuleUnit sX F))
    (mulAn sX (anGlobal sX a) ((analytifyModule sX).obj F))
  erw [unit_globalSmul sX F a] at h1
  exact h2.symm.trans h1

include hΘ in
/-- The analytification of the constant function `c` is the constant function `c`. -/
lemma anGlobal_baseRingHom_const (c : ℂ) (U : Opens (space sX)) (y' : U) :
    Θ.hom.hom.app (op U) ((structureSheaf sX).obj.map (homOfLE le_top).op
      (anGlobal sX (ComplexPoints.baseRingHom sX ⊤ c))) y' = c := by
  have hn := ConcreteCategory.congr_hom (Θ.hom.hom.naturality (homOfLE (le_top : U ≤ ⊤)).op)
    (anGlobal sX (ComplexPoints.baseRingHom sX ⊤ c))
  have h2 := congrArg (fun f => f y') hn
  refine h2.trans ?_
  exact (hΘ ⊤ (ComplexPoints.baseRingHom sX ⊤ c) ⟨y'.1, trivial⟩).trans
    (evalHom_baseRingHom _ _ c)

end AnLinear

section ChainLinear

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (d : ℕ)
variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
  (C : ∀ y, ChartData sX n Θ y)

/-- The image in `Γ(X, ⊤)` of the base scalar `c` is the constant function `c`. -/
lemma baseHom_baseScalars_top (c : ℂ) :
    (baseHom sX).hom.app (op ⊤) (baseScalars sX c) = ComplexPoints.baseRingHom sX ⊤ c := by
  have h := restrictGlobal_baseScalars sX c ⊤
  refine Eq.trans ?_ h
  change _ = X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op _
  erw [X.presheaf.map_id]
  rfl

/-- The base scalar `c`, as a global section of the inverse image of the base. -/
noncomputable def tC (c : ℂ) : (baseSheaf sX).obj.obj (op ⊤) := baseScalars sX c

/-- The constant sheaf `ℂ` on `X^an`. -/
noncomputable abbrev constAn : TopCat.Sheaf AddCommGrpCat.{0} (space sX) :=
  (constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ)

/-- Multiplication by `c` on the constant sheaf `ℂ`. -/
noncomputable def constMul (c : ℂ) : constAn sX ⟶ constAn sX :=
  (constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).map
    (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c))

/-- The image in `Γ(X, ⊤)` of `tC c` is the constant function `c`. -/
lemma baseHom_tC (c : ℂ) :
    (baseHom sX).hom.app (op ⊤) (tC sX c) = ComplexPoints.baseRingHom sX ⊤ c :=
  baseHom_baseScalars_top sX c

variable [SmoothOfRelativeDimension d sX]

/-- Multiplication by a complex number on the holomorphic de Rham complex. -/
noncomputable def mCanZ (c : ℂ) : KanZ sX d hΘ C ⟶ KanZ sX d hΘ C where
  f p := mulAn sX (anGlobal sX (ComplexPoints.baseRingHom sX ⊤ c))
    ((analytifyModule sX).obj (FZ sX d p))
  comm' := by
    rintro i _ rfl
    cases i with
    | ofNat k =>
      change mulAn sX _ _ ≫ (KanZ sX d hΘ C).d (Int.ofNat k) (Int.ofNat k + 1) =
        (KanZ sX d hΘ C).d (Int.ofNat k) (Int.ofNat k + 1) ≫ mulAn sX _ _
      rw [KanZ_d]
      exact (δan_mulAn sX hΘ C _ c (anGlobal_baseRingHom_const sX hΘ c) k).symm
    | negSucc j => exact (isZero_KanZ_negSucc sX d hΘ C j).eq_of_src _ _

/-- The comparison `α⁻¹ Ω^•_X ⟶ Ω^•_{X^an}` intertwines multiplication by `c` on both
complexes. -/
theorem ιZ_mC (c : ℂ) :
    ιZ sX d hΘ C ≫ mCanZ sX d hΘ C c =
      (complexPullback (toSchemeHom sX)).map (mC sX d (tC sX c)) ≫ ιZ sX d hΘ C := by
  ext p : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  change analytifyModuleι sX (FZ sX d p) ≫ mulAn sX _ _ =
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (toSchemeHom sX)).map
      ((_root_.SheafOfModules.toSheaf _).map (Stacks.Perfect.FractionClass.smulHom
        ((baseHom sX).hom.app (op ⊤) (tC sX c)) (FZ sX d p))) ≫ analytifyModuleι sX (FZ sX d p)
  rw [baseHom_tC]
  exact ι_mulAn sX (FZ sX d p) _

/-- The inclusion of the constants `ℂ_{X^an} ⟶ Ω^•_{X^an}` intertwines multiplication by `c` on
both complexes. -/
theorem εZ_mC (c : ℂ) :
    (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{0} (space sX)) (ComplexShape.up ℤ) 0).map
        (constMul sX c) ≫ εZ sX d hΘ C =
      εZ sX d hΘ C ≫ mCanZ sX d hΘ C c := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, εZ_f_zero]
  erw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun ψ => (HomologicalComplex.singleObjXSelf
    (V := TopCat.Sheaf AddCommGrpCat.{0} (space sX)) (ComplexShape.up ℤ) 0
      ((constantSheaf (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of ℂ))).hom ≫ ψ) (εan_mulAn sX hΘ C _ c (anGlobal_baseRingHom_const sX hΘ c))

end ChainLinear

section Compose

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Hom.relativeDifferentials
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] globalSections_additive
attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (d : ℕ)
variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
  (C : ∀ y, ChartData sX n Θ y)
variable [SmoothOfRelativeDimension d sX]

/-- The holomorphic de Rham complex is concentrated in nonnegative degrees. -/
lemma isStrictlyGE_KanZ : (KanZ sX d hΘ C).IsStrictlyGE 0 :=
  (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => by
    obtain ⟨j, rfl⟩ : ∃ j, i = Int.negSucc j := ⟨(-i - 1).toNat, by omega⟩
    exact isZero_KanZ_negSucc sX d hΘ C j

/-- The inclusion of the constants `ℂ_{X^an} ⟶ Ω^•_{X^an}` is an isomorphism on
hypercohomology. -/
theorem isIso_hypercohomology_εZ (m : ℤ) :
    IsIso ((hypercohomology (space sX) m).map (εZ sX d hΘ C)) := by
  haveI := quasiIso_εZ sX d hΘ C
  haveI := isStrictlyGE_KanZ sX d hΘ C
  exact isIso_hypercohomology_map_of_quasiIso (space sX)
    (K := ⟨(HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{0} (space sX))
      (ComplexShape.up ℤ) 0).obj ((constantSheaf (Opens.grothendieckTopology (space sX))
        AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ)), 0, inferInstance⟩)
    (L := ⟨KanZ sX d hΘ C, 0, inferInstance⟩) (ObjectProperty.homMk (εZ sX d hΘ C))
    (hφ := quasiIso_εZ sX d hΘ C) m

/-- The additive comparison `H^m_dR(X) ≅ H^m(X^an, ℂ)`. -/
noncomputable def Φ [IsProjectiveVariety ℂ sX] (m : ℤ) :
    Scheme.Hom.deRhamCohomology sX m ≅
      (sheafCohomology (space sX) m).obj ((constantSheaf (Opens.grothendieckTopology (space sX))
        AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℂ)) :=
  haveI := isIso_gaga sX d hΘ C m
  haveI := isIso_hypercohomology_εZ sX d hΘ C m
  GodPull.hypercohomologyIsoGodementTotal X.toTopCat
    (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus
      (Scheme.Hom.deRhamAlgebras sX)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))) m ≪≫
    (hypercohomology X.toTopCat m).mapIso (eKZ sX d).symm ≪≫
    asIso (hypercohomologyPullback (toSchemeHom sX) (KZ sX d) m ≫
      (hypercohomology (space sX) m).map (ιZ sX d hΘ C)) ≪≫
    (asIso ((hypercohomology (space sX) m).map (εZ sX d hΘ C))).symm

/-- The comparison `Φ` is the composite of `hypercohomologyIsoGodementTotal`, `eKZ`, GAGA and the
inverse of the inclusion of the constants, on hypercohomology. -/
theorem Φ_hom_eq [IsProjectiveVariety ℂ sX] (m : ℤ) :
    haveI := isIso_hypercohomology_εZ sX d hΘ C m
    (Φ sX d hΘ C m).hom = (GodPull.hypercohomologyIsoGodementTotal X.toTopCat
      (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (Scheme.Hom.deRhamAlgebras sX)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))) m).hom ≫
      ((hypercohomology X.toTopCat m).map (eKZ sX d).inv ≫
        ((hypercohomologyPullback (toSchemeHom sX) (KZ sX d) m ≫
          (hypercohomology (space sX) m).map (ιZ sX d hΘ C)) ≫
        CategoryTheory.inv ((hypercohomology (space sX) m).map (εZ sX d hΘ C)))) :=
  rfl

include hΘ in
/-- On hypercohomology, the analytic part of `Φ` intertwines multiplication by `c` on the
algebraic de Rham complex with multiplication by `c` on the constant sheaf. -/
theorem hypercohomology_map_mC_comp_comparison_eq [IsProjectiveVariety ℂ sX] (m : ℤ) (c : ℂ) :
    haveI := isIso_hypercohomology_εZ sX d hΘ C m
    (hypercohomology X.toTopCat m).map (mC sX d (tC sX c)) ≫
        (hypercohomologyPullback (toSchemeHom sX) (KZ sX d) m ≫
          (hypercohomology (space sX) m).map (ιZ sX d hΘ C)) ≫
        CategoryTheory.inv ((hypercohomology (space sX) m).map (εZ sX d hΘ C)) =
      (hypercohomologyPullback (toSchemeHom sX) (KZ sX d) m ≫
          (hypercohomology (space sX) m).map (ιZ sX d hΘ C)) ≫
        CategoryTheory.inv ((hypercohomology (space sX) m).map (εZ sX d hΘ C)) ≫
        (hypercohomology (space sX) m).map ((HomologicalComplex.single
          (TopCat.Sheaf AddCommGrpCat.{0} (space sX)) (ComplexShape.up ℤ) 0).map (constMul sX c)) := by
  haveI := isIso_hypercohomology_εZ sX d hΘ C m
  have e3 := hypercohomology_map_comp_hypercohomologyPullback (toSchemeHom sX)
    (mC sX d (tC sX c)) m
  have e4 := congrArg (hypercohomology (space sX) m).map (ιZ_mC sX d hΘ C c)
  have e5 := congrArg (hypercohomology (space sX) m).map (εZ_mC sX d hΘ C c)
  simp only [Functor.map_comp] at e4 e5
  have e5' : (hypercohomology (space sX) m).map (mCanZ sX d hΘ C c) ≫
      CategoryTheory.inv ((hypercohomology (space sX) m).map (εZ sX d hΘ C)) =
      CategoryTheory.inv ((hypercohomology (space sX) m).map (εZ sX d hΘ C)) ≫
        (hypercohomology (space sX) m).map ((HomologicalComplex.single
          (TopCat.Sheaf AddCommGrpCat.{0} (space sX)) (ComplexShape.up ℤ) 0).map (constMul sX c)) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← e5, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [Category.assoc, Category.assoc]
  erw [reassoc_of% e3]
  rw [← reassoc_of% e4, e5']

/-- The isomorphism `hypercohomologyIsoGodementTotal` intertwines multiplication by `c` on the de
Rham complex. -/
theorem Φ_linear_e1 (m : ℤ) (c : ℂ) :
    (DerivedCategory.Plus.Q ⋙ (globalSections X.toTopCat).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} m).map
      (ψdR (Scheme.Hom.deRhamAlgebras sX)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))
          (tC sX c)) ≫
      (GodPull.hypercohomologyIsoGodementTotal X.toTopCat
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (Scheme.Hom.deRhamAlgebras sX)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))) m).hom =
      (GodPull.hypercohomologyIsoGodementTotal X.toTopCat
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (Scheme.Hom.deRhamAlgebras sX)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))) m).hom ≫
        (hypercohomology X.toTopCat m).map (ψdR (Scheme.Hom.deRhamAlgebras sX)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))
            (tC sX c)).hom :=
  (GodPull.hypercohomologyIsoGodementTotal_hom_naturality X.toTopCat _ m).trans
    (whisker_eq _ (GodPull.hyp_map_eq _ m).symm)

/-- The inverse of `eKZ` intertwines multiplication by `c` on both de Rham complexes. -/
theorem Φ_linear_e2 (c : ℂ) :
    (ψdR (Scheme.Hom.deRhamAlgebras sX)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))
          (tC sX c)).hom ≫ (eKZ sX d).inv = (eKZ sX d).inv ≫ mC sX d (tC sX c) := by
  erw [Iso.comp_inv_eq, Category.assoc, ← eKZ_ψdR, Iso.inv_hom_id_assoc]

/-- `Φ_linear_e2` on hypercohomology in degree `m`. -/
theorem Φ_linear_e2' (m : ℤ) (c : ℂ) :
    (hypercohomology X.toTopCat m).map (ψdR (Scheme.Hom.deRhamAlgebras sX)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))
          (tC sX c)).hom ≫
      (hypercohomology X.toTopCat m).map (eKZ sX d).inv =
      (hypercohomology X.toTopCat m).map (eKZ sX d).inv ≫
        (hypercohomology X.toTopCat m).map (mC sX d (tC sX c)) := by
  erw [← Functor.map_comp, ← Functor.map_comp, Φ_linear_e2 sX d c]
  rfl

/-- Pasting of three commutation relations along a composite. -/
theorem paste_lin {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ : C} (f₀ : A₀ ⟶ A₀) (B : A₀ ⟶ A₁)
    (h : A₁ ⟶ A₁) (E : A₁ ⟶ A₂) (mc : A₂ ⟶ A₂) (P : A₂ ⟶ A₃) (V : A₃ ⟶ A₄) (M : A₄ ⟶ A₄)
    (e1 : f₀ ≫ B = B ≫ h) (e2 : h ≫ E = E ≫ mc) (e3 : mc ≫ P ≫ V = P ≫ V ≫ M) :
    f₀ ≫ B ≫ E ≫ P ≫ V = (B ≫ E ≫ P ≫ V) ≫ M := by
  rw [reassoc_of% e1, reassoc_of% e2, e3]
  simp only [Category.assoc]

/-- The comparison `Φ : H^m_dR(X) ≅ H^m(X^an, ℂ)` is `ℂ`-linear. -/
theorem Φ_linear [IsProjectiveVariety ℂ sX] (m : ℤ) (c : ℂ) :
    (DerivedCategory.Plus.Q ⋙ (globalSections X.toTopCat).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} m).map
      (ψdR (Scheme.Hom.deRhamAlgebras sX)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))
          (tC sX c)) ≫ (Φ sX d hΘ C m).hom =
      (Φ sX d hΘ C m).hom ≫ (hypercohomology (space sX) m).map ((HomologicalComplex.single
          (TopCat.Sheaf AddCommGrpCat.{0} (space sX)) (ComplexShape.up ℤ) 0).map (constMul sX c)) := by
  rw [Φ_hom_eq sX d hΘ C m]
  exact paste_lin _ _ _ _ _ _ _ _ (Φ_linear_e1 sX m c) (Φ_linear_e2' sX d m c)
    (hypercohomology_map_mC_comp_comparison_eq sX d hΘ C m c)

end Compose

end DRCmp

end Analytic

attribute [local instance] DRCmp.isLeftAdjoint_analytifyModule
  DRCmp.isLeftAdjoint_pullback_toSchemeHom

section Naturality

open CategoryTheory.Limits TopologicalSpace
open GodPull

section ManifoldPart

open AlgebraicGeometry MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff

namespace AnPull

section Val

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

attribute [local implicit_reducible] TopCat.Sheaf

variable {n : ℕ} [cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)]
  [hmfd : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX)]
  {Θ : structureSheaf sX ≅ 𝒪[n, ComplexPoints sX]}
  (hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
  (C : ∀ y, ChartData sX n Θ y)

/-- The chart open of `U` at `x`. -/
def OU (U : Opens (space sX)) (x : ComplexPoints sX) : Opens (EuclideanSpace ℂ (Fin n)) :=
  ⟨(C x).φ.target ∩ (C x).φ.symm ⁻¹' U, (C x).φ.isOpen_inter_preimage_symm U.2⟩

/-- The chart patch of `U` at `x` is contained in `U`. -/
lemma patch_OU_le (U : Opens (space sX)) (x : ComplexPoints sX) :
    patch sX (C x).φ (OU sX C U x) ≤ U := by
  rintro y ⟨hy1, -, hy3⟩
  have : (C x).φ.symm ((C x).φ y) ∈ U := hy3
  rwa [(C x).φ.left_inv hy1] at this

/-- A point `x ∈ U` lies in the chart patch of `U` at `x`. -/
lemma mem_patch_OU {U : Opens (space sX)} {x : ComplexPoints sX} (hx : x ∈ U) :
    x ∈ patch sX (C x).φ (OU sX C U x) := by
  refine ⟨(C x).hy, (C x).φ.map_source (C x).hy, ?_⟩
  show (C x).φ.symm ((C x).φ x) ∈ U
  rw [(C x).φ.left_inv (C x).hy]; exact hx

/-- The value of an analytic form at a point, in the chart at that point. -/
noncomputable def val {p : ℕ} {U : Opens (space sX)} (s : (Ωan sX p).val.obj (op U))
    (x : ComplexPoints sX) (hx : x ∈ U) : EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ :=
  (C x).Ψ p (OU sX C U x) ((Ωan sX p).val.presheaf.map (homOfLE (patch_OU_le sX C U x)).op s)
    ⟨x, mem_patch_OU sX C hx⟩

/-- The derivative of the transition from the chart at `y₀` to the chart at `x`, at `x`. -/
noncomputable abbrev tr (y₀ x : ComplexPoints sX) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  fderiv ℂ ((C x).φ ∘ (C y₀).φ.symm) ((C y₀).φ x)

/-- Restricting an analytic form from `U` to `V` and then to `W` is restricting it to `W`. -/
lemma res_res {p : ℕ} {U V W : Opens (space sX)} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (s : (Ωan sX p).val.obj (op U)) :
    (Ωan sX p).val.presheaf.map (homOfLE h₂).op ((Ωan sX p).val.presheaf.map (homOfLE h₁).op s) =
      (Ωan sX p).val.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  have := ConcreteCategory.congr_hom
    ((Ωan sX p).val.presheaf.map_comp (homOfLE h₁).op (homOfLE h₂).op) s
  exact this.symm

include hΘ in
set_option maxRecDepth 10000 in
/-- The chart expression at `y₀` of an analytic form is its value at each point, transported by
the derivative of the chart transition. -/
theorem Ψ_eq_val {p : ℕ} {U : Opens (space sX)} (s : (Ωan sX p).val.obj (op U))
    (y₀ : ComplexPoints sX) (O : Opens (EuclideanSpace ℂ (Fin n)))
    (hP : patch sX (C y₀).φ O ≤ U) (x : patch sX (C y₀).φ O) :
    (C y₀).Ψ p O ((Ωan sX p).val.presheaf.map (homOfLE hP).op s) x =
      (val sX C s x.1 (hP x.2)).compContinuousLinearMap (tr sX C y₀ x.1) := by
  let O'' : Opens (EuclideanSpace ℂ (Fin n)) := O ⊓
    ⟨(C y₀).φ.target ∩ (C y₀).φ.symm ⁻¹' (patch sX (C x.1).φ (OU sX C U x.1)),
      (C y₀).φ.isOpen_inter_preimage_symm (patch sX (C x.1).φ (OU sX C U x.1)).2⟩
  have h1 : patch sX (C y₀).φ O'' ≤ patch sX (C y₀).φ O := fun y hy => ⟨hy.1, hy.2.1⟩
  have h2 : patch sX (C y₀).φ O'' ≤ patch sX (C x.1).φ (OU sX C U x.1) := by
    rintro y ⟨hy1, -, -, hy4⟩
    have : (C y₀).φ.symm ((C y₀).φ y) ∈ patch sX (C x.1).φ (OU sX C U x.1) := hy4
    rwa [(C y₀).φ.left_inv hy1] at this
  have hx : x.1 ∈ patch sX (C y₀).φ O'' := by
    refine ⟨x.2.1, x.2.2, (C y₀).φ.map_source x.2.1, ?_⟩
    show (C y₀).φ.symm ((C y₀).φ x.1) ∈ (patch sX (C x.1).φ (OU sX C U x.1) : Set (ComplexPoints sX))
    rw [(C y₀).φ.left_inv x.2.1]
    exact mem_patch_OU sX C (hP x.2)
  have e1 := (C y₀).restr p O'' O h1 ((Ωan sX p).val.presheaf.map (homOfLE hP).op s) ⟨x.1, hx⟩
  rw [res_res] at e1
  have e2 := Ψ_res_transform sX hΘ (C y₀) (C x.1) O'' (OU sX C U x.1) h2
    ((Ωan sX p).val.presheaf.map (homOfLE (patch_OU_le sX C U x.1)).op s) ⟨x.1, hx⟩
  rw [res_res] at e2
  exact e1.symm.trans e2

include hΘ in
/-- An analytic form is determined by its values at the points of its domain. -/
theorem val_injective {p : ℕ} {U : Opens (space sX)} {s t : (Ωan sX p).val.obj (op U)}
    (h : ∀ x (hx : x ∈ U), val sX C s x hx = val sX C t x hx) : s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf (ringCatSheaf sX)).obj (Ωan sX p))
    (fun i : U => patch sX (C i.1).φ (OU sX C U i.1)) U
    (fun i => homOfLE (patch_OU_le sX C U i.1))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, mem_patch_OU sX C hx⟩) s t fun i => ?_
  change (Ωan sX p).val.presheaf.map (homOfLE (patch_OU_le sX C U i.1)).op s =
    (Ωan sX p).val.presheaf.map (homOfLE (patch_OU_le sX C U i.1)).op t
  apply (C i.1).inj p (OU sX C U i.1)
  funext y
  rw [Ψ_eq_val sX hΘ C s i.1 _ _ y, Ψ_eq_val sX hΘ C t i.1 _ _ y, h]

include hΘ in
/-- The value of the restriction of an analytic form is the value of the form. -/
theorem val_res {p : ℕ} {U V : Opens (space sX)} (hVU : V ≤ U) (s : (Ωan sX p).val.obj (op U))
    (x : ComplexPoints sX) (hx : x ∈ V) :
    val sX C ((Ωan sX p).val.presheaf.map (homOfLE hVU).op s) x hx = val sX C s x (hVU hx) := by
  have e := Ψ_eq_val sX hΘ C s x (OU sX C V x) ((patch_OU_le sX C V x).trans hVU)
    ⟨x, mem_patch_OU sX C hx⟩
  unfold val
  rw [res_res]
  refine e.trans ?_
  rw [tr, fderiv_comp_symm_self sX ((C x).φ.map_source (C x).hy), compCLM_id]
  rfl

/-- The value of an analytic form at a point is additive in the form. -/
lemma val_add {p : ℕ} {U : Opens (space sX)} (s t : (Ωan sX p).val.obj (op U))
    (x : ComplexPoints sX) (hx : x ∈ U) :
    val sX C (s + t) x hx = val sX C s x hx + val sX C t x hx := by
  unfold val
  erw [map_add (ConcreteCategory.hom ((Ωan sX p).val.presheaf.map
    (homOfLE (patch_OU_le sX C U x)).op)), map_add]
  rfl

/-- The value of `a • s` at `x` is `a(x)` times the value of `s` at `x`. -/
lemma val_smul {p : ℕ} {U : Opens (space sX)} (a : (ringCatSheaf sX).obj.obj (op U))
    (s : (Ωan sX p).val.obj (op U)) (x : ComplexPoints sX) (hx : x ∈ U) :
    val sX C (a • s) x hx = Θ.hom.hom.app (op U) a ⟨x, hx⟩ • val sX C s x hx := by
  unfold val
  erw [(Ωan sX p).val.map_smul, (C x).smul, Θ_res]
  rfl

/-- The transition map between two charts of the maximal atlas is smooth at each point of their
common source. -/
theorem transition_contDiffAt {e e' : OpenPartialHomeomorph (ComplexPoints sX) (EuclideanSpace ℂ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX))
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX))
    {x : ComplexPoints sX} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ContDiffAt ℂ ∞ (e' ∘ e.symm) (e x) := by
  have h := transition_contDiffOn sX he he' (s := e.source ∩ e'.source) Set.inter_subset_left
    Set.inter_subset_right
  have himg : e '' (e.source ∩ e'.source) = e.target ∩ e.symm ⁻¹' e'.source := by
    rw [e.image_source_inter_eq']
  rw [himg] at h
  exact h.contDiffAt ((e.isOpen_inter_preimage_symm e'.open_source).mem_nhds
    ⟨e.map_source hx, by simp only [Set.mem_preimage, e.left_inv hx]; exact hx'⟩)

/-- The derivatives of the transition maps between two charts are mutually inverse. -/
theorem fderiv_transition_comp {e e' : OpenPartialHomeomorph (ComplexPoints sX) (EuclideanSpace ℂ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX))
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX))
    {x : ComplexPoints sX} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    (fderiv ℂ (e' ∘ e.symm) (e x)).comp (fderiv ℂ (e ∘ e'.symm) (e' x)) =
      ContinuousLinearMap.id ℂ _ := by
  have h1 : DifferentiableAt ℂ (e' ∘ e.symm) (e x) :=
    (transition_contDiffAt sX he he' hx hx').differentiableAt (by simp)
  have h2 : DifferentiableAt ℂ (e ∘ e'.symm) (e' x) :=
    (transition_contDiffAt sX he' he hx' hx).differentiableAt (by simp)
  have hk : (e ∘ e'.symm) (e' x) = e x := by simp [e'.left_inv hx']
  rw [← hk] at h1
  rw [← hk, ← fderiv_comp _ h1 h2]
  have hev : ((e' ∘ e.symm) ∘ (e ∘ e'.symm)) =ᶠ[nhds (e' x)] id := by
    have hU : e'.target ∩ e'.symm ⁻¹' e.source ∈ nhds (e' x) :=
      (e'.isOpen_inter_preimage_symm e.open_source).mem_nhds
        ⟨e'.map_source hx', by simp only [Set.mem_preimage, e'.left_inv hx']; exact hx⟩
    filter_upwards [hU] with w hw
    simp only [Function.comp_apply, id]
    rw [e.left_inv hw.2, e'.right_inv hw.1]
  rw [hev.fderiv_eq, fderiv_id]

/-- Precomposition of alternating maps with a linear map `T` having a right inverse is
injective. -/
lemma compCLM_cancel {p : ℕ} {A B : EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ}
    {T T' : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)}
    (hTT' : T.comp T' = ContinuousLinearMap.id ℂ _)
    (h : A.compContinuousLinearMap T = B.compContinuousLinearMap T) : A = B := by
  ext v
  have h1 := DFunLike.congr_fun h (⇑T' ∘ v)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h1
  have hv : (⇑T ∘ ⇑T' ∘ v) = v := by
    funext i
    simpa using congrArg (fun L => L (v i)) hTT'
  rwa [hv] at h1

include hΘ in
/-- A family of values on `U` whose chart expression near each point is holomorphic is the
family of values of an analytic form on `U`. -/
theorem exists_of_val {p : ℕ} {U : Opens (space sX)}
    (v : ∀ x, x ∈ U → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ)
    (hv : ∀ x₀ (hx₀ : x₀ ∈ U), ∃ (O : Opens (EuclideanSpace ℂ (Fin n)))
      (hP : patch sX (C x₀).φ O ≤ U), x₀ ∈ patch sX (C x₀).φ O ∧
      ∃ ξ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ,
        DifferentiableOn ℂ ξ ((C x₀).φ.target ∩ O) ∧
        ∀ y (hy : y ∈ patch sX (C x₀).φ O),
          ξ ((C x₀).φ y) = (v y (hP hy)).compContinuousLinearMap (tr sX C x₀ y)) :
    ∃ s : (Ωan sX p).val.obj (op U), ∀ x hx, val sX C s x hx = v x hx := by
  choose O hP hmem ξ hξd hξ using hv
  have hloc : ∀ i : U, ∃ t : (Ωan sX p).val.obj (op (patch sX (C i.1).φ (O i.1 i.2))),
      ∀ y (hy : y ∈ patch sX (C i.1).φ (O i.1 i.2)), val sX C t y hy = v y (hP i.1 i.2 hy) := by
    intro i
    obtain ⟨t, ht⟩ := ((C i.1).range p (O i.1 i.2)
      (fun y' => ξ i.1 i.2 ((C i.1).φ y'))).2 ⟨ξ i.1 i.2, hξd i.1 i.2, fun _ => rfl⟩
    refine ⟨t, fun y hy => ?_⟩
    have e := Ψ_eq_val sX hΘ C t i.1 (O i.1 i.2) le_rfl ⟨y, hy⟩
    have hid : (Ωan sX p).val.presheaf.map (homOfLE (le_rfl :
        patch sX (C i.1).φ (O i.1 i.2) ≤ patch sX (C i.1).φ (O i.1 i.2))).op t = t := by
      rw [show (homOfLE (le_rfl : patch sX (C i.1).φ (O i.1 i.2) ≤ _)).op =
        𝟙 (op (patch sX (C i.1).φ (O i.1 i.2))) from rfl, CategoryTheory.Functor.map_id]
      rfl
    rw [hid] at e
    have e2 := congrFun ht ⟨y, hy⟩
    apply compCLM_cancel (T := tr sX C i.1 y)
      (T' := fderiv ℂ ((C i.1).φ ∘ (C y).φ.symm) ((C y).φ y))
      (fderiv_transition_comp sX (C i.1).mem (C y).mem hy.1 (C y).hy)
    rw [← e, e2]
    exact hξ i.1 i.2 y hy
  choose t ht using hloc
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    ((SheafOfModules.toSheaf (ringCatSheaf sX)).obj (Ωan sX p))
    (fun i : U => patch sX (C i.1).φ (O i.1 i.2)) U (fun i => homOfLE (hP i.1 i.2))
    (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem x hx⟩) t (by
      intro i j
      change (Ωan sX p).val.presheaf.map (homOfLE inf_le_left).op (t i) =
        (Ωan sX p).val.presheaf.map (homOfLE inf_le_right).op (t j)
      apply val_injective sX hΘ C
      intro y hy
      rw [val_res sX hΘ C, val_res sX hΘ C, ht, ht])
  refine ⟨s, fun x hx => ?_⟩
  have h1 := hs ⟨x, hx⟩
  change (Ωan sX p).val.presheaf.map (homOfLE (hP x hx)).op s = t ⟨x, hx⟩ at h1
  rw [← val_res sX hΘ C (hP x hx) s x (hmem x hx), h1]
  exact ht ⟨x, hx⟩ x (hmem x hx)

include hΘ in
/-- The value at `x` of the holomorphic differential of `s` is the exterior derivative of the
chart expression of `s` at `x`. -/
theorem val_δan {p : ℕ} {U : Opens (space sX)} (s : (Ωan sX p).val.obj (op U))
    (x : ComplexPoints sX) (hx : x ∈ U) (O : Opens (EuclideanSpace ℂ (Fin n)))
    (hP : patch sX (C x).φ O ≤ U) (hxP : x ∈ patch sX (C x).φ O)
    (ξ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin p]→L[ℂ] ℂ)
    (hξ : ∀ y : patch sX (C x).φ O,
      ξ ((C x).φ y) = (C x).Ψ p O ((Ωan sX p).val.presheaf.map (homOfLE hP).op s) y) :
    val sX C ((δan sX hΘ C p).hom.app (op U) s) x hx = extDeriv ξ ((C x).φ x) := by
  have e := Ψ_eq_val sX hΘ C ((δan sX hΘ C p).hom.app (op U) s) x O hP ⟨x, hxP⟩
  rw [tr, fderiv_comp_symm_self sX ((C x).φ.map_source (C x).hy), compCLM_id] at e
  rw [← e]
  have hn := ConcreteCategory.congr_hom ((δan sX hΘ C p).hom.naturality (homOfLE hP).op) s
  change (δan sX hΘ C p).hom.app (op (patch sX (C x).φ O))
      ((Ωan sX p).val.presheaf.map (homOfLE hP).op s) =
    (Ωan sX (p + 1)).val.presheaf.map (homOfLE hP).op ((δan sX hΘ C p).hom.app (op U) s) at hn
  rw [← hn]
  erw [δan_app_patch sX hΘ C p ⟨x, O⟩]
  exact Ψ_δP_of_ext sX (C x) O _ ξ hξ ⟨x, hxP⟩

include hΘ in
/-- The value at each point of the global constant `0`-form `c` is the constant `c`. -/
theorem val_εan_top (c : ℂ) (x : ComplexPoints sX) :
    val sX C ((εan sX hΘ C).hom.app (op ⊤)
      ((toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX)).app (op ⊤) c)) x
        trivial = ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) c := by
  have h1 := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.app (op ⊤)) (toSheafify_εan sX hΘ C)) c
  change ((toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX)).app (op ⊤) ≫
    (εan sX hΘ C).hom.app (op ⊤)) c = _ at h1
  unfold val
  erw [ConcreteCategory.comp_apply] at h1
  erw [h1]
  have hn := ConcreteCategory.congr_hom
    ((TopCat.Sheaf.restrictHomEquivHom _ _ (isBasis_patchB sX C) (εBasis sX hΘ C)).naturality
      (homOfLE (patch_OU_le sX C ⊤ x)).op) c
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
  erw [← hn]
  erw [εPre_app_patch sX hΘ C ⟨x, OU sX C ⊤ x⟩ c, Ψ_εP]

end Val

section Kappa

variable {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))

attribute [local implicit_reducible] TopCat.Sheaf

variable {nX : ℕ} [csX : ChartedSpace (EuclideanSpace ℂ (Fin nX)) (ComplexPoints sX)]
  [hmX : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin nX)) ∞ (ComplexPoints sX)]
  {ΘX : structureSheaf sX ≅ 𝒪[nX, ComplexPoints sX]}
  (hΘX : ∀ (V : X.Opens) (a : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      ΘX.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CX : ∀ y, ChartData sX nX ΘX y)
variable {nY : ℕ} [csY : ChartedSpace (EuclideanSpace ℂ (Fin nY)) (ComplexPoints sY)]
  [hmY : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin nY)) ∞ (ComplexPoints sY)]
  {ΘY : structureSheaf sY ≅ 𝒪[nY, ComplexPoints sY]}
  (hΘY : ∀ (V : Y.Opens) (a : Γ(Y, V)) (y : (Opens.map (toSchemeHom sY)).obj V),
      ΘY.hom.hom.app (op _) ((analytificationHom sY).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CY : ∀ y, ChartData sY nY ΘY y)
variable (g : X ⟶ Y) (hg : g ≫ sY = sX)

/-- The scheme point underlying the image of `x` under `g` is the image under `g` of the scheme
point underlying `x`. -/
lemma toScheme_realize (x : ComplexPoints sX) : (realize g hg x).toScheme = g.base x.toScheme :=
  rfl

/-- Evaluating the pullback `g^* f` at `y` is evaluating `f` at the image of `y` under `g`. -/
lemma evalHom_appLE' {W' : Y.Opens} {V : X.Opens} (h : V ≤ g ⁻¹ᵁ W')
    (y : chart (sX := sX) V) (f : Γ(Y, W')) :
    evalHom V y ((g.appLE W' V h).hom f) =
      evalHom W' ⟨realize g hg y.1, mem_chart_iff.2 (h (mem_chart_iff.1 y.2))⟩ f := by
  simp only [evalHom, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply (g.appLE W' V h), Scheme.Hom.appLE_comp_appLE]
  rfl

omit hmX in
set_option maxRecDepth 10000 in
/-- A regular function on an affine open is, in the chart at `y₀`, a holomorphic function. -/
theorem exists_holo_eval {y₀ : ComplexPoints sX} (D : ChartData sX nX ΘX y₀) (V : X.Opens)
    (hV : IsAffineOpen V) (O : Opens (EuclideanSpace ℂ (Fin nX)))
    (hPV : patch sX D.φ O ≤ (Opens.map (toSchemeHom sX)).obj V) (f : Γ(X, V)) :
    ∃ F : EuclideanSpace ℂ (Fin nX) → ℂ, DifferentiableOn ℂ F (D.φ.target ∩ O) ∧
      ∀ y : patch sX D.φ O, F (D.φ y) = evalHom V ⟨y.1, mem_chart_iff.2 (hPV y.2)⟩ f := by
  letI := MMP.Mori.sectionAlgebra sX V
  obtain ⟨ξ, hξd, hξ⟩ := (D.range 0 O (D.Ψ 0 O (an sX 0 V (patch sX D.φ O) hPV
    ((MMP.DeRham.formsAlgEquiv sX 0 ⟨V, hV⟩).symm
      ((exteriorPower.zeroEquiv Γ(X, V) Ω[Γ(X, V)⁄ℂ]).symm f))))).1 ⟨_, rfl⟩
  refine ⟨fun v => ξ v (fun _ => 0), fun v hv => ?_, fun y => ?_⟩
  · have hd := hξd.differentiableAt ((D.φ.open_target.inter O.2).mem_nhds hv)
    exact (hd.continuousAlternatingMap_apply (g := fun (_ : Fin 0) _ => 0)
      (fun _ => differentiableAt_const _)).differentiableWithinAt
  · have e := hξ y
    rw [D.deg0 V hV O hPV f y] at e
    simp only [e, ContinuousAlternatingMap.constOfIsEmpty_apply]

/-- A point of `U` in the source of the chart at `a` lies in the chart patch of `U` at `a`. -/
lemma mem_patch_OU' {U : Opens (space sX)} (a : ComplexPoints sX) {y : ComplexPoints sX}
    (hy : y ∈ (CX a).φ.source) (hyU : y ∈ U) : y ∈ patch sX (CX a).φ (OU sX CX U a) := by
  refine ⟨hy, (CX a).φ.map_source hy, ?_⟩
  show (CX a).φ.symm ((CX a).φ y) ∈ U
  rw [(CX a).φ.left_inv hy]; exact hyU

/-- The chart expression of the analytic map `X^an ⟶ Y^an` induced by `g` is smooth. -/
theorem contDiffAt_κ (a : ComplexPoints sX) (b : ComplexPoints sY) (y : ComplexPoints sX)
    (hya : y ∈ (CX a).φ.source) (hyb : realize g hg y ∈ (CY b).φ.source) :
    ContDiffAt ℂ ∞ ((CY b).φ ∘ realize g hg ∘ (CX a).φ.symm) ((CX a).φ y) := by
  have hyW : y.toScheme ∈ g ⁻¹ᵁ (CY b).W := by
    have := mem_chart_iff.1 ((CY b).hφ hyb)
    rw [toScheme_realize] at this
    exact this
  obtain ⟨V, hVaff, hyV, hVle⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hyW
  let S : Opens (space sX) := (Opens.map (toSchemeHom sX)).obj V ⊓
    ⟨realize g hg ⁻¹' (CY b).φ.source, (continuous_realize g hg).isOpen_preimage _
      (CY b).φ.open_source⟩
  have hPS := patch_OU_le sX CX S a
  have hyP : y ∈ patch sX (CX a).φ (OU sX CX S a) :=
    mem_patch_OU' sX CX a hya ⟨hyV, hyb⟩
  have hPV : patch sX (CX a).φ (OU sX CX S a) ≤ (Opens.map (toSchemeHom sX)).obj V :=
    hPS.trans inf_le_left
  have hF : ∀ i, ∃ F : EuclideanSpace ℂ (Fin nX) → ℂ,
      DifferentiableOn ℂ F ((CX a).φ.target ∩ OU sX CX S a) ∧
      ∀ y' : patch sX (CX a).φ (OU sX CX S a), F ((CX a).φ y') =
        evalHom V ⟨y'.1, mem_chart_iff.2 (hPV y'.2)⟩ ((g.appLE (CY b).W V hVle).hom ((CY b).z i)) :=
    fun i => exists_holo_eval sX (CX a) V hVaff _ hPV _
  choose F hFd hFv using hF
  let c : Fin nY → ℂ := fun i => evalHom (CY b).W ⟨b, (CY b).hφ (CY b).hy⟩ ((CY b).z i)
  let G : EuclideanSpace ℂ (Fin nX) → EuclideanSpace ℂ (Fin nY) :=
    fun v => (EuclideanSpace.equiv (Fin nY) ℂ).symm (fun i => F i v - c i)
  have hS : IsOpen ((CX a).φ.target ∩ (OU sX CX S a : Set (EuclideanSpace ℂ (Fin nX)))) :=
    (CX a).φ.open_target.inter (OU sX CX S a).2
  have hG : DifferentiableOn ℂ G ((CX a).φ.target ∩ OU sX CX S a) :=
    (EuclideanSpace.equiv (Fin nY) ℂ).symm.differentiable.comp_differentiableOn
      (differentiableOn_pi.2 fun i => (hFd i).sub_const _)
  have hv : (CX a).φ y ∈ (CX a).φ.target ∩ (OU sX CX S a : Set (EuclideanSpace ℂ (Fin nX))) :=
    ⟨(CX a).φ.map_source hya, hyP.2⟩
  have heq : G =ᶠ[nhds ((CX a).φ y)] ((CY b).φ ∘ realize g hg ∘ (CX a).φ.symm) := by
    filter_upwards [hS.mem_nhds hv] with w hw
    have hw' : (CX a).φ.symm w ∈ patch sX (CX a).φ (OU sX CX S a) := by
      refine ⟨(CX a).φ.map_target hw.1, ?_⟩
      show (CX a).φ ((CX a).φ.symm w) ∈ (OU sX CX S a : Set _)
      rw [(CX a).φ.right_inv hw.1]; exact hw.2
    have hwS := hPS hw'
    ext i
    have e1 : F i w = evalHom V ⟨(CX a).φ.symm w, mem_chart_iff.2 (hPV hw')⟩
        ((g.appLE (CY b).W V hVle).hom ((CY b).z i)) := by
      have := hFv i ⟨_, hw'⟩
      rwa [(CX a).φ.right_inv hw.1] at this
    change F i w - c i = (CY b).φ (realize g hg ((CX a).φ.symm w)) i
    rw [(CY b).coord _ hwS.2 i, e1, evalHom_appLE' sX sY g hg]
  exact ((contDiffOn_of_differentiableOn_vec hS hG).contDiffAt (hS.mem_nhds hv)).congr_of_eventuallyEq
    heq.symm

/-- Chain rule for the chart expressions of the analytic map induced by `g`, under a change of
charts on the source and on the target. -/
theorem fderiv_κ_chain (a a' : ComplexPoints sX) (b b' : ComplexPoints sY) (y : ComplexPoints sX)
    (hya : y ∈ (CX a).φ.source) (hya' : y ∈ (CX a').φ.source)
    (hyb : realize g hg y ∈ (CY b).φ.source) (hyb' : realize g hg y ∈ (CY b').φ.source) :
    (fderiv ℂ ((CY b').φ ∘ (CY b).φ.symm) ((CY b).φ (realize g hg y))).comp
        (fderiv ℂ ((CY b).φ ∘ realize g hg ∘ (CX a).φ.symm) ((CX a).φ y)) =
      (fderiv ℂ ((CY b').φ ∘ realize g hg ∘ (CX a').φ.symm) ((CX a').φ y)).comp
        (fderiv ℂ ((CX a').φ ∘ (CX a).φ.symm) ((CX a).φ y)) := by
  have hκ1 := (contDiffAt_κ sX sY CX CY g hg a b y hya hyb).differentiableAt (by simp)
  have hκ2 := (contDiffAt_κ sX sY CX CY g hg a' b' y hya' hyb').differentiableAt (by simp)
  have ht1 := (transition_contDiffAt sY (CY b).mem (CY b').mem hyb hyb').differentiableAt
    (n := ∞) (by simp)
  have ht2 := (transition_contDiffAt sX (CX a).mem (CX a').mem hya hya').differentiableAt
    (n := ∞) (by simp)
  have hk1 : ((CY b).φ ∘ realize g hg ∘ (CX a).φ.symm) ((CX a).φ y) = (CY b).φ (realize g hg y) := by
    simp [(CX a).φ.left_inv hya]
  have hk2 : ((CX a').φ ∘ (CX a).φ.symm) ((CX a).φ y) = (CX a').φ y := by
    simp [(CX a).φ.left_inv hya]
  rw [← hk1] at ht1
  rw [← hk2] at hκ2
  rw [← hk1, ← hk2, ← fderiv_comp _ ht1 hκ1, ← fderiv_comp _ hκ2 ht2]
  have hopen : IsOpen ((CX a).φ.target ∩ (CX a).φ.symm ⁻¹' ((CX a').φ.source ∩
      realize g hg ⁻¹' ((CY b).φ.source ∩ (CY b').φ.source))) :=
    (CX a).φ.isOpen_inter_preimage_symm ((CX a').φ.open_source.inter
      ((continuous_realize g hg).isOpen_preimage _ ((CY b).φ.open_source.inter (CY b').φ.open_source)))
  have hmem : (CX a).φ y ∈ (CX a).φ.target ∩ (CX a).φ.symm ⁻¹' ((CX a').φ.source ∩
      realize g hg ⁻¹' ((CY b).φ.source ∩ (CY b').φ.source)) := by
    refine ⟨(CX a).φ.map_source hya, ?_⟩
    simp only [Set.mem_preimage, (CX a).φ.left_inv hya]
    exact ⟨hya', hyb, hyb'⟩
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [hopen.mem_nhds hmem] with w hw
  obtain ⟨-, hw1, hw2, -⟩ := hw
  simp only [Function.comp_apply, (CY b).φ.left_inv hw2, (CX a').φ.left_inv hw1]

/-- Precomposing an alternating map with `S` and then `T` is precomposing it with `S.comp T`. -/
lemma compCLM_comp {m : ℕ} {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
    (A : E₁ [⋀^Fin m]→L[ℂ] ℂ) (S : E₂ →L[ℂ] E₁) (T : E₃ →L[ℂ] E₂) :
    (A.compContinuousLinearMap S).compContinuousLinearMap T =
      A.compContinuousLinearMap (S.comp T) := by
  ext v; rfl

/-- The derivative of `h` in the charts at `x` and at `h x`. -/
noncomputable abbrev Dκ (x : ComplexPoints sX) :
    EuclideanSpace ℂ (Fin nX) →L[ℂ] EuclideanSpace ℂ (Fin nY) :=
  fderiv ℂ ((CY (realize g hg x)).φ ∘ realize g hg ∘ (CX x).φ.symm) ((CX x).φ x)

/-- The value of the pull-back of an analytic form. -/
noncomputable def pv {p : ℕ} {U : Opens (space sY)} (t : (Ωan sY p).val.obj (op U))
    (x : ComplexPoints sX) (hx : realize g hg x ∈ U) :
    EuclideanSpace ℂ (Fin nX) [⋀^Fin p]→L[ℂ] ℂ :=
  (val sY CY t (realize g hg x) hx).compContinuousLinearMap (Dκ sX sY CX CY g hg x)

/-- The open of `X^an` over the chart patch of `U` at `h x₀`. -/
noncomputable def Srep (U : Opens (space sY)) (x₀ : ComplexPoints sX) : Opens (space sX) :=
  (Opens.map (analyticMap g hg)).obj (patch sY (CY (realize g hg x₀)).φ
    (OU sY CY U (realize g hg x₀)))

/-- The chart open of the representative at `x₀`. -/
noncomputable def Orep (U : Opens (space sY)) (x₀ : ComplexPoints sX) : Opens (EuclideanSpace ℂ (Fin nX)) :=
  OU sX CX (Srep sX sY CY g hg U x₀) x₀

/-- The chart map `κ` at `x₀`. -/
noncomputable abbrev κ (x₀ : ComplexPoints sX) :
    EuclideanSpace ℂ (Fin nX) → EuclideanSpace ℂ (Fin nY) :=
  (CY (realize g hg x₀)).φ ∘ realize g hg ∘ (CX x₀).φ.symm

/-- The chart representative of the pull-back of `t` at `x₀`. -/
noncomputable def ξrep {p : ℕ} {U : Opens (space sY)} (t : (Ωan sY p).val.obj (op U))
    (x₀ : ComplexPoints sX) :
    EuclideanSpace ℂ (Fin nX) → EuclideanSpace ℂ (Fin nX) [⋀^Fin p]→L[ℂ] ℂ := fun v =>
  (holExt sY (CY (realize g hg x₀)) (OU sY CY U (realize g hg x₀))
      ((Ωan sY p).val.presheaf.map (homOfLE (patch_OU_le sY CY U (realize g hg x₀))).op t)
      (κ sX sY CX CY g hg x₀ v)).compContinuousLinearMap
    (fderiv ℂ (κ sX sY CX CY g hg x₀) v)

/-- The chart patch of the representative at `x₀` is contained in the preimage of `U`. -/
lemma Srep_le (U : Opens (space sY)) (x₀ : ComplexPoints sX) :
    patch sX (CX x₀).φ (Orep sX sY CX CY g hg U x₀) ≤ (Opens.map (analyticMap g hg)).obj U :=
  (patch_OU_le sX CX _ x₀).trans ((Opens.map (analyticMap g hg)).monotone (patch_OU_le sY CY U _))

/-- If the image of `x₀` lies in `U`, then `x₀` lies in the chart patch of the representative at
`x₀`. -/
lemma mem_Orep {U : Opens (space sY)} {x₀ : ComplexPoints sX} (hx₀ : realize g hg x₀ ∈ U) :
    x₀ ∈ patch sX (CX x₀).φ (Orep sX sY CX CY g hg U x₀) :=
  mem_patch_OU sX CX (mem_patch_OU sY CY hx₀)

/-- The chart representative of the pull-back of `t` at `x₀` is holomorphic. -/
theorem differentiableOn_ξrep {p : ℕ} {U : Opens (space sY)} (t : (Ωan sY p).val.obj (op U))
    (x₀ : ComplexPoints sX) :
    DifferentiableOn ℂ (ξrep sX sY CX CY g hg t x₀)
      ((CX x₀).φ.target ∩ Orep sX sY CX CY g hg U x₀) := by
  let b := realize g hg x₀
  have hPS := patch_OU_le sX CX (Srep sX sY CY g hg U x₀) x₀
  obtain ⟨hζd, -⟩ := holExt_spec sY (CY b) (OU sY CY U b)
    ((Ωan sY p).val.presheaf.map (homOfLE (patch_OU_le sY CY U b)).op t)
  intro v hv
  have hy : (CX x₀).φ.symm v ∈ patch sX (CX x₀).φ (Orep sX sY CX CY g hg U x₀) := by
    refine ⟨(CX x₀).φ.map_target hv.1, ?_⟩
    show (CX x₀).φ ((CX x₀).φ.symm v) ∈ (Orep sX sY CX CY g hg U x₀ : Set _)
    rw [(CX x₀).φ.right_inv hv.1]; exact hv.2
  have hyS := hPS hy
  have hκc := contDiffAt_κ sX sY CX CY g hg x₀ b _ hy.1 hyS.1
  rw [(CX x₀).φ.right_inv hv.1] at hκc
  have hζ : DifferentiableAt ℂ (holExt sY (CY b) (OU sY CY U b)
      ((Ωan sY p).val.presheaf.map (homOfLE (patch_OU_le sY CY U b)).op t))
      (κ sX sY CX CY g hg x₀ v) :=
    hζd.differentiableAt (((CY b).φ.open_target.inter (OU sY CY U b).2).mem_nhds
      ⟨(CY b).φ.map_source hyS.1, hyS.2⟩)
  exact ((hζ.comp v (hκc.differentiableAt (by simp))).continuousAlternatingMapCompContinuousLinearMap
    ((hκc.fderiv_right (m := 1) (by simp)).differentiableAt (by simp))).differentiableWithinAt

include hΘY in
/-- The chart representative of the pull-back of `t` at `x₀` is the value of the pull-back,
transported by the derivative of the chart transition. -/
theorem ξrep_eq {p : ℕ} {U : Opens (space sY)} (t : (Ωan sY p).val.obj (op U))
    (x₀ : ComplexPoints sX) (y : ComplexPoints sX)
    (hy : y ∈ patch sX (CX x₀).φ (Orep sX sY CX CY g hg U x₀)) :
    ξrep sX sY CX CY g hg t x₀ ((CX x₀).φ y) =
      (pv sX sY CX CY g hg t y (Srep_le sX sY CX CY g hg U x₀ hy)).compContinuousLinearMap
        (tr sX CX x₀ y) := by
  let b := realize g hg x₀
  have hPS := patch_OU_le sX CX (Srep sX sY CY g hg U x₀) x₀
  have hyS := hPS hy
  obtain ⟨-, hζv⟩ := holExt_spec sY (CY b) (OU sY CY U b)
    ((Ωan sY p).val.presheaf.map (homOfLE (patch_OU_le sY CY U b)).op t)
  have hκy : κ sX sY CX CY g hg x₀ ((CX x₀).φ y) = (CY b).φ (realize g hg y) := by
    simp only [κ, Function.comp_apply, (CX x₀).φ.left_inv hy.1]
    rfl
  unfold ξrep
  rw [hκy]
  have e1 := hζv ⟨realize g hg y, hyS⟩
  have e2 := Ψ_eq_val sY hΘY CY t b (OU sY CY U b) (patch_OU_le sY CY U b) ⟨realize g hg y, hyS⟩
  erw [e1, e2]
  unfold pv Dκ
  rw [compCLM_comp, compCLM_comp]
  congr 1
  exact fderiv_κ_chain sX sY CX CY g hg x₀ y b (realize g hg y) y hy.1 (CX y).hy hyS.1 (CY _).hy

include hΘX hΘY in
/-- The pointwise pull-back of an analytic form on `U` is an analytic form on the preimage of
`U`. -/
theorem exists_θ {p : ℕ} {U : Opens (space sY)} (t : (Ωan sY p).val.obj (op U)) :
    ∃ s : (Ωan sX p).val.obj (op ((Opens.map (analyticMap g hg)).obj U)),
      ∀ x hx, val sX CX s x hx = pv sX sY CX CY g hg t x hx :=
  exists_of_val sX hΘX CX (fun x hx => pv sX sY CX CY g hg t x hx) fun x₀ hx₀ =>
    ⟨Orep sX sY CX CY g hg U x₀, Srep_le sX sY CX CY g hg U x₀, mem_Orep sX sY CX CY g hg hx₀,
      ξrep sX sY CX CY g hg t x₀, differentiableOn_ξrep sX sY CX CY g hg t x₀,
      fun y hy => ξrep_eq sX sY CX hΘY CY g hg t x₀ y hy⟩

/-- The pull-back of an analytic form along `h`. -/
noncomputable def θfun {p : ℕ} {U : Opens (space sY)} (t : (Ωan sY p).val.obj (op U)) :
    (Ωan sX p).val.obj (op ((Opens.map (analyticMap g hg)).obj U)) :=
  (exists_θ sX sY hΘX CX hΘY CY g hg t).choose

/-- The values of the pull-back `θfun t` are the pointwise pull-backs of the values of `t`. -/
lemma val_θfun {p : ℕ} {U : Opens (space sY)} (t : (Ωan sY p).val.obj (op U))
    (x : ComplexPoints sX) (hx : x ∈ (Opens.map (analyticMap g hg)).obj U) :
    val sX CX (θfun sX sY hΘX CX hΘY CY g hg t) x hx = pv sX sY CX CY g hg t x hx :=
  (exists_θ sX sY hΘX CX hΘY CY g hg t).choose_spec x hx

/-- The value of the pull-back is additive in the form. -/
lemma pv_add {p : ℕ} {U : Opens (space sY)} (t t' : (Ωan sY p).val.obj (op U))
    (x : ComplexPoints sX) (hx : realize g hg x ∈ U) :
    pv sX sY CX CY g hg (t + t') x hx = pv sX sY CX CY g hg t x hx + pv sX sY CX CY g hg t' x hx := by
  unfold pv
  rw [val_add]
  ext v; rfl

include hΘY in
/-- The value of the pull-back of a restricted form is the value of the pull-back of the form. -/
lemma pv_res {p : ℕ} {U V : Opens (space sY)} (hVU : V ≤ U) (t : (Ωan sY p).val.obj (op U))
    (x : ComplexPoints sX) (hx : realize g hg x ∈ V) :
    pv sX sY CX CY g hg ((Ωan sY p).val.presheaf.map (homOfLE hVU).op t) x hx =
      pv sX sY CX CY g hg t x (hVU hx) := by
  unfold pv
  rw [val_res sY hΘY CY hVU]

/-- The pull-back of analytic forms is additive. -/
lemma θfun_add {p : ℕ} {U : Opens (space sY)} (t t' : (Ωan sY p).val.obj (op U)) :
    θfun sX sY hΘX CX hΘY CY g hg (t + t') =
      θfun sX sY hΘX CX hΘY CY g hg t + θfun sX sY hΘX CX hΘY CY g hg t' := by
  apply val_injective sX hΘX CX
  intro x hx
  exact (val_θfun sX sY hΘX CX hΘY CY g hg _ x hx).trans ((pv_add sX sY CX CY g hg t t' x hx).trans
    ((congrArg₂ (· + ·) (val_θfun sX sY hΘX CX hΘY CY g hg t x hx).symm
      (val_θfun sX sY hΘX CX hΘY CY g hg t' x hx).symm).trans (val_add sX CX _ _ x hx).symm))

/-- The pull-back of analytic forms commutes with restriction. -/
lemma θfun_res {p : ℕ} {U V : Opens (space sY)} (hVU : V ≤ U) (t : (Ωan sY p).val.obj (op U)) :
    θfun sX sY hΘX CX hΘY CY g hg ((Ωan sY p).val.presheaf.map (homOfLE hVU).op t) =
      (Ωan sX p).val.presheaf.map (homOfLE ((Opens.map (analyticMap g hg)).monotone hVU)).op
        (θfun sX sY hΘX CX hΘY CY g hg t) := by
  apply val_injective sX hΘX CX
  intro x hx
  exact (val_θfun sX sY hΘX CX hΘY CY g hg _ x hx).trans
    ((pv_res sX sY CX hΘY CY g hg hVU t x hx).trans
      ((val_θfun sX sY hΘX CX hΘY CY g hg t x _).symm.trans (val_res sX hΘX CX _ _ x hx).symm))

/-- **The pull-back of analytic forms** along `h : X^an ⟶ Y^an`. -/
noncomputable def θS (p : ℕ) :
    (SheafOfModules.toSheaf (ringCatSheaf sY)).obj (Ωan sY p) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).obj
        ((SheafOfModules.toSheaf (ringCatSheaf sX)).obj (Ωan sX p)) :=
  ObjectProperty.homMk
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun t => θfun sX sY hΘX CX hΘY CY g hg (U := U.unop) t)
        (fun t t' => θfun_add sX sY hΘX CX hΘY CY g hg t t'))
      naturality := fun U V f => by
        ext t
        exact θfun_res sX sY hΘX CX hΘY CY g hg (leOfHom f.unop) t }

include hΘX hΘY in
/-- If the values of `s` are the pull-backs of the values of `t`, then the values of `ds` are the
pull-backs of the values of `dt`. -/
theorem val_δ_of_val_eq {p : ℕ} {W : Opens (space sX)} {U : Opens (space sY)}
    (s : (Ωan sX p).val.obj (op W)) (t : (Ωan sY p).val.obj (op U))
    (hW : W ≤ (Opens.map (analyticMap g hg)).obj U)
    (hst : ∀ y (hy : y ∈ W), val sX CX s y hy = pv sX sY CX CY g hg t y (hW hy))
    (x : ComplexPoints sX) (hx : x ∈ W) :
    val sX CX ((δan sX hΘX CX p).hom.app (op W) s) x hx =
      pv sX sY CX CY g hg ((δan sY hΘY CY p).hom.app (op U) t) x (hW hx) := by
  let b := realize g hg x
  let S' : Opens (space sX) := W ⊓ Srep sX sY CY g hg U x
  have hPS := patch_OU_le sX CX S' x
  have hxP : x ∈ patch sX (CX x).φ (OU sX CX S' x) :=
    mem_patch_OU sX CX ⟨hx, mem_patch_OU sY CY (hW hx)⟩
  have hsub : ∀ y, y ∈ patch sX (CX x).φ (OU sX CX S' x) →
      y ∈ patch sX (CX x).φ (Orep sX sY CX CY g hg U x) := by
    rintro y ⟨hy1, hy2, hy3⟩
    exact ⟨hy1, hy2, (hy3 : _ ∈ S').2⟩
  rw [val_δan sX hΘX CX s x hx (OU sX CX S' x) (hPS.trans inf_le_left) hxP
    (ξrep sX sY CX CY g hg t x) (fun y => by
      rw [ξrep_eq sX sY CX hΘY CY g hg t x y.1 (hsub y.1 y.2),
        Ψ_eq_val sX hΘX CX s x _ (hPS.trans inf_le_left) y, hst])]
  obtain ⟨hζd, hζv⟩ := holExt_spec sY (CY b) (OU sY CY U b)
    ((Ωan sY p).val.presheaf.map (homOfLE (patch_OU_le sY CY U b)).op t)
  have hκc := contDiffAt_κ sX sY CX CY g hg x b x (CX x).hy (CY b).hy
  have hκx : κ sX sY CX CY g hg x ((CX x).φ x) = (CY b).φ b := by
    simp only [κ, Function.comp_apply, (CX x).φ.left_inv (CX x).hy]
    rfl
  have hζ : DifferentiableAt ℂ (holExt sY (CY b) (OU sY CY U b)
      ((Ωan sY p).val.presheaf.map (homOfLE (patch_OU_le sY CY U b)).op t))
      (κ sX sY CX CY g hg x ((CX x).φ x)) := by
    rw [hκx]
    exact hζd.differentiableAt (((CY b).φ.open_target.inter (OU sY CY U b).2).mem_nhds
      ⟨(CY b).φ.map_source (CY b).hy, (mem_patch_OU sY CY (hW hx)).2⟩)
  unfold ξrep
  rw [extDeriv_pullback (r := ∞) hζ hκc (by simp), hκx]
  unfold pv Dκ
  rw [val_δan sY hΘY CY t b (hW hx) (OU sY CY U b) (patch_OU_le sY CY U b) (mem_patch_OU sY CY (hW hx))
    _ (fun z => hζv z)]

/-- The pull-back of analytic forms commutes with the holomorphic de Rham differential. -/
theorem θS_δan (p : ℕ) :
    θS sX sY hΘX CX hΘY CY g hg p ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).map (δan sX hΘX CX p) =
      δan sY hΘY CY p ≫ θS sX sY hΘX CX hΘY CY g hg (p + 1) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  ext t
  change (δan sX hΘX CX p).hom.app _ (θfun sX sY hΘX CX hΘY CY g hg t) =
    θfun sX sY hΘX CX hΘY CY g hg ((δan sY hΘY CY p).hom.app U t)
  apply val_injective sX hΘX CX
  intro x hx
  exact (val_δ_of_val_eq sX sY hΘX CX hΘY CY g hg _ t le_rfl
    (fun y hy => val_θfun sX sY hΘX CX hΘY CY g hg t y hy) x hx).trans
      (val_θfun sX sY hΘX CX hΘY CY g hg _ x hx).symm

end Kappa

section ThetaZ

open DRCmp

variable {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) (dX dY : ℕ)

attribute [local implicit_reducible] TopCat.Sheaf

variable {nX : ℕ} [csX : ChartedSpace (EuclideanSpace ℂ (Fin nX)) (ComplexPoints sX)]
  [hmX : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin nX)) ∞ (ComplexPoints sX)]
  {ΘX : structureSheaf sX ≅ 𝒪[nX, ComplexPoints sX]}
  (hΘX : ∀ (V : X.Opens) (a : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      ΘX.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CX : ∀ y, ChartData sX nX ΘX y)
variable {nY : ℕ} [csY : ChartedSpace (EuclideanSpace ℂ (Fin nY)) (ComplexPoints sY)]
  [hmY : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin nY)) ∞ (ComplexPoints sY)]
  {ΘY : structureSheaf sY ≅ 𝒪[nY, ComplexPoints sY]}
  (hΘY : ∀ (V : Y.Opens) (a : Γ(Y, V)) (y : (Opens.map (toSchemeHom sY)).obj V),
      ΘY.hom.hom.app (op _) ((analytificationHom sY).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CY : ∀ y, ChartData sY nY ΘY y)
variable (g : X ⟶ Y) (hg : g ≫ sY = sX)
variable [SmoothOfRelativeDimension dX sX] [SmoothOfRelativeDimension dY sY]

/-- The components of the pull-back of holomorphic de Rham complexes. -/
noncomputable def θAf : ∀ p : ℤ, (KanZ sY dY hΘY CY).X p ⟶
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (KanZ sX dX hΘX CX)).X p
  | Int.ofNat k => θS sX sY hΘX CX hΘY CY g hg k
  | Int.negSucc _ => 0

/-- **The pull-back of holomorphic de Rham complexes** `Ω^•_{Y^an} ⟶ h_* Ω^•_{X^an}`. -/
noncomputable def θA : KanZ sY dY hΘY CY ⟶
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (KanZ sX dX hΘX CX) where
  f := θAf sX sY dX dY hΘX CX hΘY CY g hg
  comm' := by
    rintro i _ rfl
    cases i with
    | ofNat k =>
      change θS sX sY hΘX CX hΘY CY g hg k ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).map
            ((KanZ sX dX hΘX CX).d (Int.ofNat k) (Int.ofNat k + 1)) =
        (KanZ sY dY hΘY CY).d (Int.ofNat k) (Int.ofNat k + 1) ≫ θS sX sY hΘX CX hΘY CY g hg (k + 1)
      rw [KanZ_d, KanZ_d]
      exact θS_δan sX sY hΘX CX hΘY CY g hg k
    | negSucc j => exact (isZero_KanZ_negSucc sY dY hΘY CY j).eq_of_src _ _

end ThetaZ

section AlgPull

open KaehlerDifferential Stacks.AlgebraicGeometry.AffineOpenDeRham

variable {X X' : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ)) (g : X' ⟶ X)
  (hg : g ≫ sX = sX')

set_option maxRecDepth 20000 in
include hg in
/-- Over affine opens `W' ≤ g⁻¹ W`, the pull-back of `dc₁ ∧ ⋯ ∧ dc_q` along `g` is
`d(g^* c₁) ∧ ⋯ ∧ d(g^* c_q)`. -/
theorem formsSectionsIso_hom_map_ιMulti_d (q : ℕ)
    (W : X.affineOpens) (W' : X'.affineOpens) (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (c : Fin q → Γ(X, W)) :
    (formsSectionsIso sX' (W'.2) (isAffineOpen_top _) (by simp) q).hom
        ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op
          (deRhamFormsPushforwardSections g sX sX' (𝟙 _) (by rw [hg, Category.comp_id]) q
            ((formsSectionsIso sX (W.2) (isAffineOpen_top _)
                (by simp) q).inv
              (exteriorPower.ιMulti Γ(X, W) q fun i ↦
                CommRingCat.KaehlerDifferential.d (c i))))) =
      exteriorPower.ιMulti Γ(X', W') q fun i ↦
        CommRingCat.KaehlerDifferential.d ((g.appLE W W' h).hom (c i)) := by
  have e1 := formsSectionsIso_inv_ιMulti_d sX (W.2) (isAffineOpen_top _)
    (by simp) q c
  have e2 := Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft g sX sX' (𝟙 _)
    (by rw [hg, Category.comp_id]) (op (W : X.Opens)) q c
  have e3 := Stacks.GradedAlgebra.homogeneousProdLeft_naturality
    (Scheme.Hom.deRhamAlgebras sX').exterior.toPresheafGradedAlgebra (homOfLE h).op q
    (fun i ↦ SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX') (op (g ⁻¹ᵁ (W : X.Opens)))
      ((g.app W).hom (c i)))
  have e4 := formsSectionsIso_inv_ιMulti_d sX' (W'.2) (isAffineOpen_top _)
    (by simp) q fun i ↦ (g.appLE W W' h).hom (c i)
  have e5 : ∀ i, ((Scheme.Hom.deRhamAlgebras sX').exteriorPower 1).val.map (homOfLE h).op
      (SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX') (op (g ⁻¹ᵁ (W : X.Opens)))
        ((g.app W).hom (c i))) =
      SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX') (op (W' : X'.Opens))
        ((g.appLE W W' h).hom (c i)) := fun i ↦
    SheafOfModules.exactOne_map (Scheme.Hom.deRhamAlgebras sX') (homOfLE h).op _
  refine (congrArg (fun t ↦ (formsSectionsIso sX' (W'.2) (isAffineOpen_top _)
    (by simp) q).hom ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE h).op (deRhamFormsPushforwardSections g sX sX' (𝟙 _)
        (by rw [hg, Category.comp_id]) q t))) e1).trans ?_
  refine (congrArg (fun t ↦ (formsSectionsIso sX' (W'.2) (isAffineOpen_top _)
    (by simp) q).hom ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE h).op t)) e2).trans ?_
  refine (congrArg (fun t ↦ (formsSectionsIso sX' (W'.2) (isAffineOpen_top _)
    (by simp) q).hom t) e3).trans ?_
  refine (congrArg (fun t ↦ (formsSectionsIso sX' (W'.2) (isAffineOpen_top _)
    (by simp) q).hom
      ((Scheme.Hom.deRhamAlgebras sX').exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        (op (W' : X'.Opens)) q t)) (funext e5)).trans ?_
  refine (congrArg (formsSectionsIso sX' (W'.2) (isAffineOpen_top _)
    (by simp) q).hom e4.symm).trans ?_
  exact Iso.inv_hom_id_apply _ _

end AlgPull

section Iota

open DRCmp

variable {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))

attribute [local implicit_reducible] TopCat.Sheaf

variable {nX : ℕ} [csX : ChartedSpace (EuclideanSpace ℂ (Fin nX)) (ComplexPoints sX)]
  [hmX : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin nX)) ∞ (ComplexPoints sX)]
  {ΘX : structureSheaf sX ≅ 𝒪[nX, ComplexPoints sX]}
  (hΘX : ∀ (V : X.Opens) (a : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      ΘX.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CX : ∀ y, ChartData sX nX ΘX y)
variable {nY : ℕ} [csY : ChartedSpace (EuclideanSpace ℂ (Fin nY)) (ComplexPoints sY)]
  [hmY : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin nY)) ∞ (ComplexPoints sY)]
  {ΘY : structureSheaf sY ≅ 𝒪[nY, ComplexPoints sY]}
  (hΘY : ∀ (V : Y.Opens) (a : Γ(Y, V)) (y : (Opens.map (toSchemeHom sY)).obj V),
      ΘY.hom.hom.app (op _) ((analytificationHom sY).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CY : ∀ y, ChartData sY nY ΘY y)
variable (g : X ⟶ Y) (hg : g ≫ sY = sX)

/-- The analytification of a section of algebraic forms. -/
noncomputable abbrev uS {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {k : ℕ} {V : Z.Opens}
    (s : Γ(sZ.relativeDifferentialForms (k : ℤ), V)) :
    (Ωan sZ k).val.obj (op ((Opens.map (toSchemeHom sZ)).obj V)) :=
  (analytifyModuleUnit sZ (sZ.relativeDifferentialForms (k : ℤ))).val.app (op V) s

/-- The algebraic pull-back of forms along `g`. -/
noncomputable abbrev φS {k : ℕ} {U : Y.Opens} (s : Γ(sY.relativeDifferentialForms (k : ℤ), U)) :
    Γ(sX.relativeDifferentialForms (k : ℤ), g ⁻¹ᵁ U) :=
  ((Scheme.Hom.deRhamFormsPushforwardHom g sY sX (𝟙 _) (by rw [hg, Category.comp_id])).app
    (k : ℤ)).val.app (op U) s

/-- The compatibility of analytification with pull-back, at the values. -/
def PI {k : ℕ} {U : Y.Opens} (s : Γ(sY.relativeDifferentialForms (k : ℤ), U)) : Prop :=
  ∀ x (hx : x ∈ (Opens.map (toSchemeHom sX)).obj (g ⁻¹ᵁ U)),
    val sX CX (uS sX (φS sX sY g hg s)) x hx = pv sX sY CX CY g hg (uS sY s) x hx

/-- The compatibility `PI` is closed under addition. -/
lemma PI_add {k : ℕ} {U : Y.Opens} (s t : Γ(sY.relativeDifferentialForms (k : ℤ), U))
    (hs : PI sX sY CX CY g hg s) (ht : PI sX sY CX CY g hg t) :
    PI sX sY CX CY g hg (s + t) := by
  intro x hx
  have e1 : uS sX (φS sX sY g hg (s + t)) = uS sX (φS sX sY g hg s) + uS sX (φS sX sY g hg t) := by
    unfold uS φS
    erw [map_add, map_add]
    rfl
  have e2 : uS sY (s + t) = uS sY s + uS sY t := by
    unfold uS
    erw [map_add]
    rfl
  rw [e1, val_add, hs x hx, ht x hx, e2]
  exact (pv_add sX sY CX CY g hg _ _ x hx).symm

omit hmX in
include hΘX in
/-- The analytification of a regular function `a` on `V`, evaluated at `y`, is `a(y)`. -/
lemma Θ_ring (V : X.Opens) (a : Γ(X, V)) (y : ComplexPoints sX)
    (hy : y ∈ (Opens.map (toSchemeHom sX)).obj V) :
    ΘX.hom.hom.app (op _) ((ringCatSheafHom sX).hom.app (op V) a) ⟨y, hy⟩ =
      evalHom V ⟨y, mem_chart_iff.2 hy⟩ a :=
  hΘX V a ⟨y, hy⟩

/-- Analytification of algebraic forms is linear over regular functions. -/
lemma uS_smul {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {k : ℕ} {V : Z.Opens} (a : Γ(Z, V))
    (s : Γ(sZ.relativeDifferentialForms (k : ℤ), V)) :
    uS sZ (a • s) = (show (ringCatSheaf sZ).obj.obj (op ((Opens.map (toSchemeHom sZ)).obj V)) from
      (ringCatSheafHom sZ).hom.app (op V) a) • uS sZ s :=
  ((analytifyModuleUnit sZ (sZ.relativeDifferentialForms (k : ℤ))).val.app (op V)).hom.map_smul a s

/-- Evaluating the pullback `g^* f` at `y` is evaluating `f` at the image of `y` under `g`. -/
lemma evalHom_app' {W' : Y.Opens} (y : chart (sX := sX) (g ⁻¹ᵁ W')) (f : Γ(Y, W')) :
    evalHom (g ⁻¹ᵁ W') y ((g.app W').hom f) =
      evalHom W' ⟨realize g hg y.1, mem_chart_iff.2 (mem_chart_iff.1 y.2)⟩ f := by
  rw [Scheme.Hom.app_eq_appLE]
  exact evalHom_appLE' sX sY g hg le_rfl y f

/-- The value of the pull-back of `a • t` at `x` is `a(g x)` times the value of the pull-back of
`t`. -/
lemma pv_smul {p : ℕ} {U : Opens (space sY)} (a : (ringCatSheaf sY).obj.obj (op U))
    (t : (Ωan sY p).val.obj (op U)) (x : ComplexPoints sX) (hx : realize g hg x ∈ U) :
    pv sX sY CX CY g hg (a • t) x hx =
      ΘY.hom.hom.app (op U) a ⟨realize g hg x, hx⟩ • pv sX sY CX CY g hg t x hx := by
  unfold pv
  rw [val_smul]
  ext v; rfl

include hΘX hΘY in
/-- The compatibility `PI` is closed under multiplication by regular functions. -/
lemma PI_smul {k : ℕ} {U : Y.Opens} (b : Γ(Y, U)) (s : Γ(sY.relativeDifferentialForms (k : ℤ), U))
    (hs : PI sX sY CX CY g hg s) : PI sX sY CX CY g hg (b • s) := by
  intro x hx
  have e1 : φS sX sY g hg (b • s) = (g.app U).hom b • φS sX sY g hg s :=
    Scheme.Hom.deRhamFormsPushforwardHom_smul g sY sX (𝟙 _) _ (k : ℤ) (op U) b s
  rw [e1, uS_smul, val_smul, Θ_ring sX hΘX, hs x hx, uS_smul, evalHom_app' sX sY g hg]
  exact ((pv_smul sX sY CX CY g hg _ (uS sY s) x hx).trans
    (congrArg (· • pv sX sY CX CY g hg (uS sY s) x hx) (Θ_ring sY hΘY U b _ hx))).symm

set_option maxRecDepth 10000 in
/-- Analytification of algebraic forms commutes with the de Rham differentials. -/
theorem uS_d {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {n : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sZ)]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sZ)]
    {Θ : structureSheaf sZ ≅ 𝒪[n, ComplexPoints sZ]}
    (hΘ : ∀ (V : Z.Opens) (a : Γ(Z, V)) (y : (Opens.map (toSchemeHom sZ)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sZ).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
    (C : ∀ y, ChartData sZ n Θ y) {k : ℕ} {V : Z.Opens}
    (m : Γ(sZ.relativeDifferentialForms (k : ℤ), V)) :
    uS sZ (((sZ.deRhamComplex).d k (k + 1)).val.app (op V) m) =
      (δan sZ hΘ C k).hom.app (op ((Opens.map (toSchemeHom sZ)).obj V)) (uS sZ m) := by
  have h : (analytifyModuleUnit sZ (sZ.relativeDifferentialForms ((k + 1 : ℕ) : ℤ))).val.app (op V)
        ((dZ sZ k).hom.app (op V) m) =
      (δan sZ hΘ C k).hom.app (op ((Opens.map (toSchemeHom sZ)).obj V))
        ((analytifyModuleUnit sZ (sZ.relativeDifferentialForms (k : ℤ))).val.app (op V) m) :=
    ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op V)) (unit_comm sZ hΘ C k)) m
  refine Eq.trans ?_ h
  exact congrArg (fun z => (analytifyModuleUnit sZ (sZ.relativeDifferentialForms ((k + 1 : ℕ) : ℤ))).val.app (op V) z)
    (dZ_app sZ k V m).symm

include hΘX hΘY in
/-- The compatibility `PI` is closed under the de Rham differential. -/
lemma PI_d {k : ℕ} {U : Y.Opens} (s : Γ(sY.relativeDifferentialForms (k : ℤ), U))
    (hs : PI sX sY CX CY g hg s) :
    PI sX sY CX CY g hg (((sY.deRhamComplex).d k (k + 1)).val.app (op U) s) := by
  intro x hx
  have e1 : φS sX sY g hg (((sY.deRhamComplex).d k (k + 1)).val.app (op U) s) =
      ((sX.deRhamComplex).d k (k + 1)).val.app (op (g ⁻¹ᵁ U)) (φS sX sY g hg s) :=
    (Scheme.Hom.deRhamFormsPushforwardHom_comm_d g sY sX (𝟙 _) _ k (op U) s).symm
  rw [e1, uS_d sX hΘX CX]
  refine (val_δ_of_val_eq sX sY hΘX CX hΘY CY g hg (uS sX (φS sX sY g hg s)) (uS sY s)
    (fun y hy => hy) hs x hx).trans ?_
  rw [uS_d sY hΘY CY]

set_option maxRecDepth 10000 in
/-- The analytification of the function `1` has constant value `1`. -/
theorem val_uS_one {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {n : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sZ)]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sZ)]
    {Θ : structureSheaf sZ ≅ 𝒪[n, ComplexPoints sZ]}
    (C : ∀ y, ChartData sZ n Θ y) (V : Z.affineOpens) (y : ComplexPoints sZ)
    (hy : y ∈ (Opens.map (toSchemeHom sZ)).obj (V : Z.Opens)) :
    letI := MMP.Mori.sectionAlgebra sZ V
    val sZ C (uS sZ ((MMP.DeRham.formsAlgEquiv sZ 0 V).symm
      ((exteriorPower.zeroEquiv Γ(Z, V) Ω[Γ(Z, V)⁄ℂ]).symm 1))) y hy =
      ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin n)) (Fin 0) 1 := by
  letI := MMP.Mori.sectionAlgebra sZ V
  have h := (C y).deg0 V V.2 (OU sZ C _ y) (patch_OU_le sZ C _ y) 1 ⟨y, mem_patch_OU sZ C hy⟩
  rw [RingHom.map_one] at h
  exact h

/-- The empty wedge product of differentials is the function `1`. -/
theorem formsSectionsIso_inv_ιMulti_zero {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    (V : Z.affineOpens) :
    letI := MMP.Mori.sectionAlgebra sZ V
    (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso sZ V.2 (isAffineOpen_top _)
        (by simp) 0).inv
      (exteriorPower.ιMulti Γ(Z, V) 0 fun i : Fin 0 ↦
        CommRingCat.KaehlerDifferential.d (i.elim0 : Γ(Z, V))) =
      (MMP.DeRham.formsAlgEquiv sZ 0 V).symm
        ((exteriorPower.zeroEquiv Γ(Z, V) Ω[Γ(Z, V)⁄ℂ]).symm 1) := by
  letI := MMP.Mori.sectionAlgebra sZ V
  apply (MMP.DeRham.formsAlgEquiv sZ 0 V).injective
  rw [LinearEquiv.apply_symm_apply, MMP.DeRham.formsAlgEquiv_apply, Iso.inv_hom_id_apply,
    exteriorPower.map_apply_ιMulti]
  apply (exteriorPower.zeroEquiv Γ(Z, V) Ω[Γ(Z, V)⁄ℂ]).injective
  rw [LinearEquiv.apply_symm_apply, exteriorPower.zeroEquiv_ιMulti]

/-- The unit form `1` over an affine open. -/
noncomputable abbrev oneForm {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (V : Z.affineOpens) :
    Γ(sZ.relativeDifferentialForms ((0 : ℕ) : ℤ), V) :=
  (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso sZ V.2 (isAffineOpen_top _)
      (by simp) 0).inv
    (exteriorPower.ιMulti Γ(Z, V) 0 fun i : Fin 0 ↦
      CommRingCat.KaehlerDifferential.d (i.elim0 : Γ(Z, V)))

include hΘX in
set_option maxRecDepth 10000 in
/-- The unit form `1` satisfies the compatibility `PI`. -/
lemma PI_one (V' : Y.affineOpens) :
    PI sX sY CX CY g hg (k := 0) (U := V') (oneForm sY V') := by
  intro x hx
  have hR : pv sX sY CX CY g hg (uS sY (oneForm sY V')) x hx =
      ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin nX)) (Fin 0) 1 := by
    unfold pv oneForm
    rw [formsSectionsIso_inv_ιMulti_zero sY V', val_uS_one sY CY V' _ hx]
    ext v; rfl
  rw [hR]
  obtain ⟨V, hVaff, hxV, hVle⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x.toScheme ∈ g ⁻¹ᵁ (V' : Y.Opens) from hx)
  have hVle' : (Opens.map (toSchemeHom sX)).obj V ≤
      (Opens.map (toSchemeHom sX)).obj (g ⁻¹ᵁ (V' : Y.Opens)) := (Opens.map _).monotone hVle
  rw [← val_res sX hΘX CX hVle' _ x hxV]
  have hnat := ConcreteCategory.congr_hom
    ((analytifyModuleUnit sX (sX.relativeDifferentialForms ((0 : ℕ) : ℤ))).val.naturality
      (homOfLE hVle).op) (φS sX sY g hg (oneForm sY V'))
  have key := formsSectionsIso_hom_map_ιMulti_d sY sX g hg 0 V' ⟨V, hVaff⟩ hVle
    (fun i : Fin 0 => i.elim0)
  have hres : (sX.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hVle).op
      (φS sX sY g hg (oneForm sY V')) =
      (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso sX hVaff (isAffineOpen_top _)
        (by simp) 0).inv
        (exteriorPower.ιMulti Γ(X, V) 0 fun i : Fin 0 ↦
          CommRingCat.KaehlerDifferential.d (i.elim0 : Γ(X, V))) := by
    have e := congrArg (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso sX hVaff
      (isAffineOpen_top _) (by simp) 0).inv key
    rw [Iso.hom_inv_id_apply] at e
    refine e.trans ?_
    congr 2
  have e2 : (Ωan sX 0).val.presheaf.map (homOfLE hVle').op (uS sX (φS sX sY g hg (oneForm sY V'))) =
      uS sX ((sX.relativeDifferentialForms ((0 : ℕ) : ℤ)).presheaf.map (homOfLE hVle).op
        (φS sX sY g hg (oneForm sY V'))) := hnat.symm
  rw [e2, hres, formsSectionsIso_inv_ιMulti_zero sX ⟨V, hVaff⟩]
  exact val_uS_one sX CX ⟨V, hVaff⟩ x hxV

/-- The zero form has value zero. -/
lemma val_zero {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {n : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sZ)]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sZ)]
    {Θ : structureSheaf sZ ≅ 𝒪[n, ComplexPoints sZ]}
    (C : ∀ y, ChartData sZ n Θ y) {p : ℕ} {U : Opens (space sZ)} (x : ComplexPoints sZ)
    (hx : x ∈ U) : val sZ C (0 : (Ωan sZ p).val.obj (op U)) x hx = 0 := by
  unfold val
  erw [map_zero, map_zero]
  rfl

/-- The zero form satisfies the compatibility `PI`. -/
lemma PI_zero {k : ℕ} {U : Y.Opens} :
    PI sX sY CX CY g hg (0 : Γ(sY.relativeDifferentialForms (k : ℤ), U)) := by
  intro x hx
  have e1 : uS sX (φS sX sY g hg (0 : Γ(sY.relativeDifferentialForms (k : ℤ), U))) = 0 := by
    unfold uS φS
    erw [map_zero, map_zero]
    rfl
  have e2 : uS sY (0 : Γ(sY.relativeDifferentialForms (k : ℤ), U)) = 0 := by
    unfold uS
    erw [map_zero]
    rfl
  rw [e1, val_zero, e2]
  unfold pv
  refine Eq.trans ?_ (congrArg (fun A => A.compContinuousLinearMap (Dκ sX sY CX CY g hg x))
    (val_zero sY CY (realize g hg x) hx)).symm
  ext v; rfl

include hΘX hΘY in
set_option maxRecDepth 20000 in
/-- On an affine open, every wedge product `dc₁ ∧ ⋯ ∧ dc_k` satisfies the compatibility `PI`. -/
theorem PI_ιMulti (V' : Y.affineOpens) :
    letI := MMP.Mori.sectionAlgebra sY V'
    ∀ (k : ℕ) (c : Fin k → Γ(Y, V')),
      PI sX sY CX CY g hg ((MMP.DeRham.formsAlgEquiv sY k V').symm
        (exteriorPower.ιMulti Γ(Y, V') k fun i ↦ KaehlerDifferential.D ℂ Γ(Y, V') (c i))) := by
  letI := MMP.Mori.sectionAlgebra sY V'
  intro k
  induction k with
  | zero =>
    intro c
    have h1 : (exteriorPower.ιMulti Γ(Y, V') 0 fun i ↦ KaehlerDifferential.D ℂ Γ(Y, V') (c i)) =
        (exteriorPower.zeroEquiv Γ(Y, V') Ω[Γ(Y, V')⁄ℂ]).symm 1 := by
      apply (exteriorPower.zeroEquiv Γ(Y, V') Ω[Γ(Y, V')⁄ℂ]).injective
      rw [LinearEquiv.apply_symm_apply, exteriorPower.zeroEquiv_ιMulti]
    rw [h1, ← formsSectionsIso_inv_ιMulti_zero sY V']
    exact PI_one sX sY hΘX CX CY g hg V'
  | succ k ih =>
    intro c
    have h1 := KaehlerDifferential.deRhamDifferential_smul_ιMulti_D (A := ℂ) (B := Γ(Y, V')) k c
    have h2 := MMP.DeRham.formsAlgEquiv_d sY k V' ((MMP.DeRham.formsAlgEquiv sY k V').symm
      (c 0 • exteriorPower.ιMulti Γ(Y, V') k fun i ↦ KaehlerDifferential.D ℂ Γ(Y, V') (c i.succ)))
    rw [LinearEquiv.apply_symm_apply, h1] at h2
    have h3 : (MMP.DeRham.formsAlgEquiv sY (k + 1) V').symm
        (exteriorPower.ιMulti Γ(Y, V') (k + 1) fun i ↦ KaehlerDifferential.D ℂ Γ(Y, V') (c i)) =
        ((sY.deRhamComplex).d k (k + 1)).val.app (op (V' : Y.Opens))
          ((MMP.DeRham.formsAlgEquiv sY k V').symm
            (c 0 • exteriorPower.ιMulti Γ(Y, V') k fun i ↦ KaehlerDifferential.D ℂ Γ(Y, V') (c i.succ))) := by
      rw [← h2]
      exact LinearEquiv.symm_apply_apply _ _
    rw [h3]
    refine PI_d sX sY hΘX CX hΘY CY g hg _ ?_
    rw [LinearEquiv.map_smul]
    exact PI_smul sX sY hΘX CX hΘY CY g hg _ _ (ih _)

include hΘX hΘY in
set_option maxRecDepth 20000 in
/-- Every algebraic form on an affine open satisfies the compatibility `PI`. -/
theorem PI_affine (V' : Y.affineOpens) (k : ℕ)
    (s : Γ(sY.relativeDifferentialForms (k : ℤ), (V' : Y.Opens))) :
    PI sX sY CX CY g hg s := by
  letI := MMP.Mori.sectionAlgebra sY V'
  obtain ⟨η, rfl⟩ : ∃ η, (MMP.DeRham.formsAlgEquiv sY k V').symm η = s :=
    ⟨MMP.DeRham.formsAlgEquiv sY k V' s, LinearEquiv.symm_apply_apply _ _⟩
  have hspan := Crystalline.span_range_smul_ιMulti_eq_top (R := Γ(Y, V')) (S := Γ(Y, V'))
    (KaehlerDifferential.D ℂ Γ(Y, V')) (KaehlerDifferential.span_range_derivation ℂ Γ(Y, V')) k
  have hη := (Submodule.eq_top_iff'.1 hspan) η
  induction hη using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨c, rfl⟩ := hy
    rw [LinearEquiv.map_smul]
    exact PI_smul sX sY hΘX CX hΘY CY g hg _ _
      (PI_ιMulti sX sY hΘX CX hΘY CY g hg V' k (fun i => c i.succ))
  | zero =>
    rw [map_zero]
    exact PI_zero sX sY CX CY g hg
  | add y z _ _ hy hz =>
    rw [map_add]
    exact PI_add sX sY CX CY g hg _ _ hy hz
  | smul b y _ hy =>
    rw [LinearEquiv.map_smul]
    exact PI_smul sX sY hΘX CX hΘY CY g hg _ _ hy

include hΘX hΘY in
/-- Every algebraic form satisfies the compatibility `PI`. -/
theorem PI_all {k : ℕ} {U : Y.Opens} (s : Γ(sY.relativeDifferentialForms (k : ℤ), U)) :
    PI sX sY CX CY g hg s := by
  intro x hx
  obtain ⟨V', hV'aff, hxV', hV'le⟩ :=
    (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) (show (realize g hg x).toScheme ∈ U from hx)
  have hP := PI_affine sX sY hΘX CX hΘY CY g hg ⟨V', hV'aff⟩ k
    ((sY.relativeDifferentialForms (k : ℤ)).presheaf.map (homOfLE hV'le).op s) x hxV'
  have hle1 : g ⁻¹ᵁ V' ≤ g ⁻¹ᵁ U := (Opens.map g.base).monotone hV'le
  have hle2 : (Opens.map (toSchemeHom sX)).obj (g ⁻¹ᵁ V') ≤
      (Opens.map (toSchemeHom sX)).obj (g ⁻¹ᵁ U) := (Opens.map _).monotone hle1
  have hle3 : (Opens.map (toSchemeHom sY)).obj V' ≤ (Opens.map (toSchemeHom sY)).obj U :=
    (Opens.map _).monotone hV'le
  have nφ : φS sX sY g hg ((sY.relativeDifferentialForms (k : ℤ)).presheaf.map (homOfLE hV'le).op s) =
      (sX.relativeDifferentialForms (k : ℤ)).presheaf.map (homOfLE hle1).op (φS sX sY g hg s) :=
    (ConcreteCategory.congr_hom (((Scheme.Hom.deRhamFormsPushforwardHom g sY sX (𝟙 _)
      (by rw [hg, Category.comp_id])).app (k : ℤ)).val.naturality (homOfLE hV'le).op) s)
  have nuX : uS sX ((sX.relativeDifferentialForms (k : ℤ)).presheaf.map (homOfLE hle1).op
      (φS sX sY g hg s)) = (Ωan sX k).val.presheaf.map (homOfLE hle2).op (uS sX (φS sX sY g hg s)) :=
    (ConcreteCategory.congr_hom ((analytifyModuleUnit sX (sX.relativeDifferentialForms (k : ℤ))).val.naturality
      (homOfLE hle1).op) (φS sX sY g hg s))
  have nuY : uS sY ((sY.relativeDifferentialForms (k : ℤ)).presheaf.map (homOfLE hV'le).op s) =
      (Ωan sY k).val.presheaf.map (homOfLE hle3).op (uS sY s) :=
    (ConcreteCategory.congr_hom ((analytifyModuleUnit sY (sY.relativeDifferentialForms (k : ℤ))).val.naturality
      (homOfLE hV'le).op) s)
  rw [nφ, nuX, nuY] at hP
  exact (val_res sX hΘX CX hle2 _ x hxV').symm.trans
    (hP.trans (pv_res sX sY CX hΘY CY g hg hle3 _ x hxV'))

include hΘX hΘY in
/-- Analytification commutes with pull-back of forms: the analytification of `g^* s` is the
analytic pull-back of the analytification of `s`. -/
theorem uS_φS_eq {k : ℕ} {U : Y.Opens} (s : Γ(sY.relativeDifferentialForms (k : ℤ), U)) :
    uS sX (φS sX sY g hg s) = (Ωan sX k).val.presheaf.map (homOfLE (fun y hy => hy :
      (Opens.map (toSchemeHom sX)).obj (g ⁻¹ᵁ U) ≤
        (Opens.map (analyticMap g hg)).obj ((Opens.map (toSchemeHom sY)).obj U))).op
      (θfun sX sY hΘX CX hΘY CY g hg (uS sY s)) := by
  apply val_injective sX hΘX CX
  intro x hx
  exact (PI_all sX sY hΘX CX hΘY CY g hg s x hx).trans
    ((val_θfun sX sY hΘX CX hΘY CY g hg (uS sY s) x hx).symm.trans (val_res sX hΘX CX _ _ x hx).symm)

end Iota

end AnPull

end ManifoldPart

namespace NatCmp

section SecDC

attribute [local implicit_reducible] MMP.Analytic.godementResolution
  MMP.Analytic.CokernelCoresolution.complexFunctor

variable {T T' T'' : TopCat.{u}} (f : T' ⟶ T) (f' : T'' ⟶ T')

/-- The map `secDC f a` followed by the map induced by `b : L ⟶ L'` is `secDC f (a ≫ f_* b)`. -/
theorem secDC_comp_map {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L L' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (a : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L)
    (b : L ⟶ L') :
    secDC f a ≫ ((godementSections T').mapHomologicalComplex _).map b =
      secDC f (a ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map b) := by
  ext p : 1
  have h := secHom_naturality f (𝟙 (K.X p)) (b.f p) (a.f p) (a.f p ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (b.f p)) (Category.id_comp _)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h.symm

/-- The map induced by `b : K' ⟶ K` followed by `secDC f a` is `secDC f (b ≫ a)`. -/
theorem map_comp_secDC {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ} (b : K' ⟶ K)
    (a : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L) :
    ((godementSections T).mapHomologicalComplex _).map b ≫ secDC f a = secDC f (b ≫ a) := by
  ext p : 1
  have h := secHom_naturality f (b.f p) (𝟙 (L.X p)) (b.f p ≫ a.f p) (a.f p)
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id])
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- The maps `secDC` along `f` and `f'` compose to the map `secDC` along `f' ≫ f`. -/
theorem secDC_comp {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    {M : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T'') ℤ}
    (a : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L)
    (b : L ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').mapHomologicalComplex _).obj M) :
    secDC f a ≫ secDC f' b = secDC (f' ≫ f)
      (a ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map b) := by
  ext p : 1
  exact secHom_comp f f' (a.f p) (b.f p)

/-- The unit `K ⟶ f_* f⁻¹ K` of complexes. -/
noncomputable abbrev unitC (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) :
    K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj
      ((complexPullback f).obj K) :=
  (NatTrans.mapHomologicalComplex
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit _).app K

/-- `map_comp_secDC` on homology of the total complexes in degree `m`. -/
theorem hm_map_comp_secDC {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ} (b : K' ⟶ K)
    (a : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L)
    (m : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (((godementSections T).mapHomologicalComplex _).map b) (ComplexShape.up ℤ)) m ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (secDC f a)
        (ComplexShape.up ℤ)) m =
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (secDC f (b ≫ a))
        (ComplexShape.up ℤ)) m := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex₂.total.map_comp, map_comp_secDC]

/-- If `x ≫ y = z`, the maps induced on homology of total complexes compose accordingly. -/
theorem hm_tot_comp {A B C : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)} [A.HasTotal (ComplexShape.up ℤ)] [B.HasTotal (ComplexShape.up ℤ)]
    [C.HasTotal (ComplexShape.up ℤ)] (x : A ⟶ B) (y : B ⟶ C) (z : A ⟶ C) (h : x ≫ y = z)
    (m : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map x (ComplexShape.up ℤ)) m ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map y (ComplexShape.up ℤ)) m =
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map z (ComplexShape.up ℤ)) m := by
  rw [← h, HomologicalComplex₂.total.map_comp, HomologicalComplex.homologyMap_comp]

/-- `H^m(Tot(secDC f a))`. -/
noncomputable abbrev hS {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (a : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L)
    (m : ℤ) :=
  HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (secDC f a) (ComplexShape.up ℤ)) m

/-- The map `hS f a` followed by hypercohomology of `b : L ⟶ L'` is `hS f (a ≫ f_* b)`. -/
theorem hS_comp_hyp {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L L' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (a : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L)
    (b : L ⟶ L') (m : ℤ) :
    hS f a m ≫ (hypercohomology T' m).map b =
      hS f (a ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map b) m := by
  rw [hyp_map_eq]
  exact hm_tot_comp _ _ _ (secDC_comp_map f a b) m

/-- Hypercohomology of `b : K' ⟶ K` followed by `hS f a` is `hS f (b ≫ a)`. -/
theorem hyp_comp_hS {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ} (b : K' ⟶ K)
    (a : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L)
    (m : ℤ) :
    (hypercohomology T m).map b ≫ hS f a m = hS f (b ≫ a) m := by
  rw [hyp_map_eq]
  exact hm_map_comp_secDC f b a m

/-- The maps `hS` along `f` and `f'` compose to the map `hS` along `f' ≫ f`. -/
theorem hS_comp_hS {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    {M : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T'') ℤ}
    (a : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj L)
    (b : L ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').mapHomologicalComplex _).obj M)
    (m : ℤ) :
    hS f a m ≫ hS f' b m = hS (f' ≫ f)
      (a ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map b) m :=
  hm_tot_comp _ _ _ (secDC_comp f f' a b) m

/-- The pullback map of Godement sections double complexes is `secDC` of the unit
`K ⟶ f_* f⁻¹ K`. -/
theorem gsdcPullback_eq (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) :
    godementSectionsDoubleComplexPullback f K = secDC f (unitC f K) := by
  ext p : 1
  have h := godementSectionsPullback_comp_map f (K.X p) (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_id] at h
  erw [Category.comp_id] at h
  exact h

/-- Transport of `secDC` along an equality of continuous maps `F₁ = F₂`. -/
theorem secDC_transport {F₁ F₂ : T' ⟶ T} (hF : F₁ = F₂)
    {K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ}
    {L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ}
    (a₁ : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} F₁).mapHomologicalComplex _).obj L)
    (a₂ : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} F₂).mapHomologicalComplex _).obj L)
    (h : ∀ (p : ℤ) (U : Opens T) (s : (K.X p).obj.obj (op U)),
      (a₁.f p).hom.app (op U) s =
        (L.X p).obj.map (homOfLE (by subst hF; exact le_rfl :
          (Opens.map F₁).obj U ≤ (Opens.map F₂).obj U)).op ((a₂.f p).hom.app (op U) s)) :
    secDC F₁ a₁ = secDC F₂ a₂ := by
  subst hF
  suffices e : a₁ = a₂ by rw [e]
  ext p : 1
  refine sheafHom_ext fun U s => ?_
  refine (h p U.unop s).trans ?_
  change (L.X p).obj.map (𝟙 _) _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The pullback map on Godement hypercohomology is `hS` of the unit `K ⟶ f_* f⁻¹ K`. -/
theorem hpb_eq_hS (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) (m : ℤ) :
    hypercohomologyPullback f K m = hS f (unitC f K) m := by
  rw [hpb_eq, gsdcPullback_eq]

end SecDC

section Reduce

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] globalSections_additive

variable {X Y : AlgebraicGeometry.Scheme.{0}} (sX : X ⟶ AlgebraicGeometry.Spec (.of ℂ))
  (sY : Y ⟶ AlgebraicGeometry.Spec (.of ℂ)) (g : X ⟶ Y) (hg : g ≫ sY = sX)

/-- The pullback on de Rham cohomology along `g` is `RΓ` of the pushforward map of de Rham
complexes followed by the pushforward–pullback map. -/
theorem pullback_eq (m : ℤ) :
    AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback g sY sX (𝟙 _)
        (by rw [hg, Category.comp_id]) m =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} m).map
          ((Stacks.Cohomology.Leray.sectionsFunctor Y.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map
              (AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
                (by rw [hg, Category.comp_id])))) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} m).map
          (g.pushforwardPullback
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus
              (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sX)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sX)))) := by
  ext ξ
  exact AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback_apply g sY sX (𝟙 _) _ m ξ

/-- Pasting of two commutative squares and a triangle. -/
theorem paste3 {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ P₅ : C} (x : P₀ ⟶ P₁) (y : P₁ ⟶ P₂)
    (B : P₂ ⟶ P₃) (B' : P₁ ⟶ P₄) (s : P₄ ⟶ P₃) (B0 : P₀ ⟶ P₅) (t : P₅ ⟶ P₄) (u : P₅ ⟶ P₃)
    (h1 : y ≫ B = B' ≫ s) (h2 : x ≫ B' = B0 ≫ t) (h3 : t ≫ s = u) : x ≫ y ≫ B = B0 ≫ u := by
  rw [h1, reassoc_of% h2, h3]

/-- Under `hypercohomologyIsoGodementTotal`, the pullback on de Rham cohomology along `g` is the
map on homology of total complexes induced by `secDC` of the pushforward map of de Rham
complexes. -/
theorem bridge_pullback (m : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} m).map
          ((Stacks.Cohomology.Leray.sectionsFunctor Y.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map
              (AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
                (by rw [hg, Category.comp_id])))) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} m).map
          (g.pushforwardPullback
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus
              (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sX)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sX)))) ≫
        (hypercohomologyIsoGodementTotal X.carrier
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus
              (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sX)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sX))) m).hom =
      (hypercohomologyIsoGodementTotal Y.carrier
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus
              (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sY)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sY))) m).hom ≫
        HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
          (secDC g.base (AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
                (by rw [hg, Category.comp_id])).hom) (ComplexShape.up ℤ)) m := by
  have h1 := pp_Bp g (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus
              (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sX)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras sX))) m
  have h2 := hypercohomologyIsoGodementTotal_hom_naturality Y.carrier
    (AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMapPlus
    g sY sX (𝟙 _) (by rw [hg, Category.comp_id])) m
  have h3 := (hm_map_comp_secDC g.base (AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMapPlus
    g sY sX (𝟙 _) (by rw [hg, Category.comp_id])).hom (𝟙 _) m).trans
      (congrArg (fun a => HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (secDC g.base a) (ComplexShape.up ℤ)) m) (Category.comp_id _))
  exact paste3 _ _ _ _ _ _ _ _ h1 h2 h3

end Reduce

section R3

open AlgebraicGeometry MMP.Analytic.Analytification MMP.Analytic.ComplexPoints DRCmp SingCmp
open scoped ContDiff

attribute [local instance] globalSections_additive

variable {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) (dX dY : ℕ)
variable {nX : ℕ} [csX : ChartedSpace (EuclideanSpace ℂ (Fin nX)) (ComplexPoints sX)]
  [hmX : IsManifold (modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin nX))) ∞ (ComplexPoints sX)]
  {ΘX : structureSheaf sX ≅ smoothSheafCommRing (modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin nX))) (modelWithCornersSelf ℂ ℂ) (ComplexPoints sX) ℂ}
  (hΘX : ∀ (V : X.Opens) (a : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      ΘX.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CX : ∀ y, ChartData sX nX ΘX y)
variable {nY : ℕ} [csY : ChartedSpace (EuclideanSpace ℂ (Fin nY)) (ComplexPoints sY)]
  [hmY : IsManifold (modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin nY))) ∞ (ComplexPoints sY)]
  {ΘY : structureSheaf sY ≅ smoothSheafCommRing (modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin nY))) (modelWithCornersSelf ℂ ℂ) (ComplexPoints sY) ℂ}
  (hΘY : ∀ (V : Y.Opens) (a : Γ(Y, V)) (y : (Opens.map (toSchemeHom sY)).obj V),
      ΘY.hom.hom.app (op _) ((analytificationHom sY).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CY : ∀ y, ChartData sY nY ΘY y)
variable [SmoothOfRelativeDimension dX sX] [SmoothOfRelativeDimension dY sY]
variable (g : X ⟶ Y) (hg : g ≫ sY = sX)

/-- The square formed by `X^an ⟶ X`, `Y^an ⟶ Y`, `g` and its analytification commutes. -/
theorem toSchemeHom_comp_base :
    toSchemeHom sX ≫ g.base = analyticMap g hg ≫ toSchemeHom sY := by
  ext x
  rfl

/-- The map `ℂ_{Y^an}[0] ⟶ h_* ℂ_{X^an}[0]` adjoint to `h⁻¹ ℂ_{Y^an} ⟶ ℂ_{X^an}`. -/
noncomputable abbrev εR :
    (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{0} (space sY)) (ComplexShape.up ℤ) 0).obj
        (constSh (space sY)) ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).obj
        ((HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{0} (space sX))
          (ComplexShape.up ℤ) 0).obj (constSh (space sX))) :=
  unitC (analyticMap g hg) _ ≫
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)) (ComplexShape.up ℤ) 0).hom.app
          (constSh (space sY)) ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (toConst (analyticMap g hg)))

/-- The pullback on sheaf cohomology of the constant sheaf along `h : X^an ⟶ Y^an` is
`hS h εR`. -/
theorem shpb_eq_hS (m : ℤ) :
    sheafCohomologyPullback (analyticMap g hg) (constSh (space sY)) m ≫
        (sheafCohomology (space sX) m).map (toConst (analyticMap g hg)) =
      hS (analyticMap g hg) (εR sX sY g hg) m := by
  unfold sheafCohomologyPullback
  change (hypercohomologyPullback (analyticMap g hg) _ m ≫ (hypercohomology _ m).map _) ≫
    (hypercohomology _ m).map _ = _
  rw [Category.assoc, ← Functor.map_comp, hpb_eq_hS]
  exact hS_comp_hyp _ _ _ m

/-- Reassociation of a composite under a functor, with an inserted isomorphism and its
inverse. -/
theorem comp_map_comp_map_eq_inv_hom_comp_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {P Q : D} {R S T U : C}
    (e : P ≅ Q) (φ : Q ⟶ F.obj R) (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ U) :
    (φ ≫ F.map a) ≫ F.map (b ≫ c) = e.inv ≫ e.hom ≫ φ ≫ F.map (a ≫ b ≫ c) := by
  simp

/-- A commutative square with isomorphisms `S` and `E` on two sides, rewritten with their
inverses. -/
theorem inv_comp_eq_comp_inv_of_comm_sq {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ : C}
    (S : P₀ ⟶ P₁) (T : P₀ ⟶ P₂)
    (E : P₂ ⟶ P₃) (w : P₁ ⟶ P₃) (iS : IsIso S) (iE : IsIso E) (h : T ≫ E = S ≫ w) :
    CategoryTheory.inv S ≫ T = w ≫ CategoryTheory.inv E := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, h]

/-- For a map `θA` of holomorphic de Rham complexes compatible with the inclusions of the
constants, pullback on constant-sheaf cohomology commutes with `εZ` and `hS θA`. -/
theorem R3_hT
    (θA : KanZ sY dY hΘY CY ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).obj
        (KanZ sX dX hΘX CX))
    (hε : εZ sY dY hΘY CY ≫ θA = εR sX sY g hg ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).map
        (εZ sX dX hΘX CX)) (m : ℤ) :
    (sheafCohomologyPullback (analyticMap g hg) (constSh (space sY)) m ≫
        (sheafCohomology (space sX) m).map (toConst (analyticMap g hg))) ≫
      (hypercohomology (space sX) m).map (εZ sX dX hΘX CX) =
      (hypercohomology (space sY) m).map (εZ sY dY hΘY CY) ≫ hS (analyticMap g hg) θA m :=
  (congrArg (· ≫ (hypercohomology (space sX) m).map (εZ sX dX hΘX CX))
    (shpb_eq_hS sX sY g hg m)).trans ((hS_comp_hyp (analyticMap g hg) (εR sX sY g hg)
        (εZ sX dX hΘX CX) m).trans
      ((congrArg (fun a => hS (analyticMap g hg) a m) hε.symm).trans
        (hyp_comp_hS (analyticMap g hg) (εZ sY dY hΘY CY) θA m).symm))

/-- `R3_hT`, with the isomorphisms induced by `εZ` inverted. -/
theorem R3_f6
    (θA : KanZ sY dY hΘY CY ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).obj
        (KanZ sX dX hΘX CX))
    (hε : εZ sY dY hΘY CY ≫ θA = εR sX sY g hg ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).map
        (εZ sX dX hΘX CX)) (m : ℤ) :
    CategoryTheory.inv (I := isIso_hypercohomology_εZ sY dY hΘY CY m)
        ((hypercohomology (space sY) m).map (εZ sY dY hΘY CY)) ≫
      (sheafCohomologyPullback (analyticMap g hg) (constSh (space sY)) m ≫
          (sheafCohomology (space sX) m).map (toConst (analyticMap g hg))) =
      hS (analyticMap g hg) θA m ≫
        CategoryTheory.inv (I := isIso_hypercohomology_εZ sX dX hΘX CX m)
          ((hypercohomology (space sX) m).map (εZ sX dX hΘX CX)) :=
  inv_comp_eq_comp_inv_of_comm_sq ((hypercohomology (space sY) m).map (εZ sY dY hΘY CY))
    (sheafCohomologyPullback (analyticMap g hg) (constSh (space sY)) m ≫
      (sheafCohomology (space sX) m).map (toConst (analyticMap g hg)))
    ((hypercohomology (space sX) m).map (εZ sX dX hΘX CX)) (hS (analyticMap g hg) θA m)
    (isIso_hypercohomology_εZ sY dY hΘY CY m) (isIso_hypercohomology_εZ sX dX hΘX CX m)
    (R3_hT sX sY dX dY hΘX CX hΘY CY g hg θA hε m)

/-- Moving the inverse of `eKZ` across the map `hS` along `X^an ⟶ X ⟶ Y`. -/
theorem R3_f4 (m : ℤ) :
    hS (L := KanZ sX dX hΘX CX) (toSchemeHom sX ≫ g.base) (((Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          (eKZ sX dX).inv) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          (unitC (toSchemeHom sX) (KZ sX dX) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).mapHomologicalComplex
              _).map (ιZ sX dX hΘX CX))) m =
      (hypercohomology Y.toTopCat m).map (eKZ sY dY).inv ≫
        hS (L := KanZ sX dX hΘX CX) (toSchemeHom sX ≫ g.base) ((eKZ sY dY).hom ≫
        (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          ((eKZ sX dX).inv ≫ unitC (toSchemeHom sX) (KZ sX dX) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).mapHomologicalComplex
              _).map (ιZ sX dX hΘX CX))) m := by
  refine Eq.trans ?_ (hyp_comp_hS _ _ _ m).symm
  congr 1
  exact comp_map_comp_map_eq_inv_hom_comp_map _ _ _ _ _ _

/-- Pasting of commutative squares along `A1 ≫ B1 ≫ (C1 ≫ D1) ≫ E1`. -/
theorem comp_eq_of_paste_left {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ P₅ Q₁ : C}
    (A1 : P₀ ⟶ P₁) (B1 : P₁ ⟶ P₂) (C1 : P₂ ⟶ P₃) (D1 : P₃ ⟶ P₄) (E1 : P₄ ⟶ P₅)
    (x1 : P₀ ⟶ P₂) (x2 : P₂ ⟶ P₄) (x3 : P₀ ⟶ P₄) (P : P₀ ⟶ Q₁) (y1 : Q₁ ⟶ P₄)
    (f1 : A1 ≫ B1 = x1) (f2 : C1 ≫ D1 = x2) (f3 : x1 ≫ x2 = x3) (f4 : x3 = P ≫ y1) :
    A1 ≫ B1 ≫ (C1 ≫ D1) ≫ E1 = P ≫ y1 ≫ E1 := by
  rw [reassoc_of% f1, f2, reassoc_of% f3, f4, Category.assoc]

/-- Pasting of commutative squares and a triangle along `P ≫ (Q ≫ R) ≫ iS ≫ T`. -/
theorem comp_eq_of_paste_right {C : Type*} [Category* C] {P₄ P₅ Q₀ Q₁ Q₂ Q₃ Q₄ : C}
    (P : Q₀ ⟶ Q₁) (Q : Q₁ ⟶ Q₂) (R : Q₂ ⟶ Q₃) (z1 : Q₁ ⟶ Q₃) (iS : Q₃ ⟶ Q₄) (T : Q₄ ⟶ P₅)
    (w : Q₃ ⟶ P₄) (E1 : P₄ ⟶ P₅) (y2 : Q₁ ⟶ P₄)
    (f5 : Q ≫ R = z1) (f6 : iS ≫ T = w ≫ E1) (f7 : z1 ≫ w = y2) :
    P ≫ (Q ≫ R) ≫ iS ≫ T = P ≫ y2 ≫ E1 := by
  rw [f5, f6, reassoc_of% f7]

/-- Two morphisms written as `P ≫ y₁ ≫ E` and `P ≫ y₂ ≫ E` with `y₁ = y₂` are equal. -/
theorem eq_of_eq_comp_comp_of_eq {C : Type*} [Category* C] {A Q₁ P₄ B : C} {X Y : A ⟶ B}
    (P : A ⟶ Q₁) (y1 y2 : Q₁ ⟶ P₄) (E : P₄ ⟶ B)
    (l : X = P ≫ y1 ≫ E) (r : Y = P ≫ y2 ≫ E) (h : y1 = y2) : X = Y := by
  rw [l, r, h]

/-- The pullback along `g` followed by the comparison for `X`, written as a single map `hS` along
`X^an ⟶ X ⟶ Y`. -/
theorem R3_lhs (m : ℤ) :
    hS g.base (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom m ≫
        (hypercohomology X.toTopCat m).map (eKZ sX dX).inv ≫
        (hypercohomologyPullback (toSchemeHom sX) (KZ sX dX) m ≫
          (hypercohomology (space sX) m).map (ιZ sX dX hΘX CX)) ≫
        CategoryTheory.inv (I := isIso_hypercohomology_εZ sX dX hΘX CX m)
          ((hypercohomology (space sX) m).map (εZ sX dX hΘX CX)) =
      (hypercohomology Y.toTopCat m).map (eKZ sY dY).inv ≫
        hS (K := KZ sY dY) (L := KanZ sX dX hΘX CX) (toSchemeHom sX ≫ g.base)
      ((eKZ sY dY).hom ≫
        (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          ((eKZ sX dX).inv ≫ unitC (toSchemeHom sX) (KZ sX dX) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).mapHomologicalComplex
              _).map (ιZ sX dX hΘX CX))) m ≫
        CategoryTheory.inv (I := isIso_hypercohomology_εZ sX dX hΘX CX m)
          ((hypercohomology (space sX) m).map (εZ sX dX hΘX CX)) := by
  have f1 := hS_comp_hyp g.base (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom (eKZ sX dX).inv m
  have f2 := (congrArg (· ≫ (hypercohomology (space sX) m).map (ιZ sX dX hΘX CX))
    (hpb_eq_hS (toSchemeHom sX) (KZ sX dX) m)).trans
      (hS_comp_hyp (toSchemeHom sX) (unitC (toSchemeHom sX) (KZ sX dX)) (ιZ sX dX hΘX CX) m)
  have f3 := hS_comp_hS g.base (toSchemeHom sX)
    ((Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          (eKZ sX dX).inv)
    (unitC (toSchemeHom sX) (KZ sX dX) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).mapHomologicalComplex
              _).map (ιZ sX dX hΘX CX)) m
  have f4 := R3_f4 sX sY dX dY hΘX CX g hg m
  exact comp_eq_of_paste_left _ _ _ _ _ _ _ _ _ _ f1 f2 f3 f4

/-- The comparison for `Y` followed by pullback along `h : X^an ⟶ Y^an`, written as a single
map `hS` along `X^an ⟶ Y^an ⟶ Y`. -/
theorem R3_rhs
    (θA : KanZ sY dY hΘY CY ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).obj
        (KanZ sX dX hΘX CX))
    (hε : εZ sY dY hΘY CY ≫ θA = εR sX sY g hg ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).map
        (εZ sX dX hΘX CX)) (m : ℤ) :
    (hypercohomology Y.toTopCat m).map (eKZ sY dY).inv ≫
        (hypercohomologyPullback (toSchemeHom sY) (KZ sY dY) m ≫
          (hypercohomology (space sY) m).map (ιZ sY dY hΘY CY)) ≫
        CategoryTheory.inv (I := isIso_hypercohomology_εZ sY dY hΘY CY m)
          ((hypercohomology (space sY) m).map (εZ sY dY hΘY CY)) ≫
        sheafCohomologyPullback (analyticMap g hg) (constSh (space sY)) m ≫
          (sheafCohomology (space sX) m).map (toConst (analyticMap g hg)) =
      (hypercohomology Y.toTopCat m).map (eKZ sY dY).inv ≫
        hS (K := KZ sY dY) (L := KanZ sX dX hΘX CX) (analyticMap g hg ≫ toSchemeHom sY)
        ((unitC (toSchemeHom sY) (KZ sY dY) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sY)).mapHomologicalComplex
              _).map (ιZ sY dY hΘY CY)) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sY)).mapHomologicalComplex
              _).map θA) m ≫
        CategoryTheory.inv (I := isIso_hypercohomology_εZ sX dX hΘX CX m)
          ((hypercohomology (space sX) m).map (εZ sX dX hΘX CX)) := by
  have f5 := (congrArg (· ≫ (hypercohomology (space sY) m).map (ιZ sY dY hΘY CY))
    (hpb_eq_hS (toSchemeHom sY) (KZ sY dY) m)).trans
      (hS_comp_hyp (toSchemeHom sY) (unitC (toSchemeHom sY) (KZ sY dY)) (ιZ sY dY hΘY CY) m)
  have f7 := hS_comp_hS (toSchemeHom sY) (analyticMap g hg)
    (unitC (toSchemeHom sY) (KZ sY dY) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sY)).mapHomologicalComplex
              _).map (ιZ sY dY hΘY CY)) θA m
  have f6 := R3_f6 sX sY dX dY hΘX CX hΘY CY g hg θA hε m
  exact comp_eq_of_paste_right _ _ _ _ _ _ _ _ _ f5 f6 f7

/-- The analytic part of the de Rham–Betti comparison commutes with pullback along `g`, given a
map `θA` of holomorphic de Rham complexes compatible with the constants and with `ιZ`. -/
theorem R3_eq [IsProjectiveVariety ℂ sX] [IsProjectiveVariety ℂ sY]
    (θA : KanZ sY dY hΘY CY ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).obj
        (KanZ sX dX hΘX CX))
    (hε : εZ sY dY hΘY CY ≫ θA = εR sX sY g hg ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).map
        (εZ sX dX hΘX CX))
    (hι : secDC (K := KZ sY dY) (L := KanZ sX dX hΘX CX) (toSchemeHom sX ≫ g.base)
      ((eKZ sY dY).hom ≫
        (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          ((eKZ sX dX).inv ≫ unitC (toSchemeHom sX) (KZ sX dX) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).mapHomologicalComplex
              _).map (ιZ sX dX hΘX CX))) =
      secDC (K := KZ sY dY) (L := KanZ sX dX hΘX CX) (analyticMap g hg ≫ toSchemeHom sY)
        ((unitC (toSchemeHom sY) (KZ sY dY) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sY)).mapHomologicalComplex
              _).map (ιZ sY dY hΘY CY)) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sY)).mapHomologicalComplex
              _).map θA)) (m : ℤ) :
    haveI := isIso_hypercohomology_εZ sX dX hΘX CX m
    haveI := isIso_hypercohomology_εZ sY dY hΘY CY m
    hS g.base (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom m ≫
        (hypercohomology X.toTopCat m).map (eKZ sX dX).inv ≫
        (hypercohomologyPullback (toSchemeHom sX) (KZ sX dX) m ≫
          (hypercohomology (space sX) m).map (ιZ sX dX hΘX CX)) ≫
        CategoryTheory.inv ((hypercohomology (space sX) m).map (εZ sX dX hΘX CX)) =
      (hypercohomology Y.toTopCat m).map (eKZ sY dY).inv ≫
        (hypercohomologyPullback (toSchemeHom sY) (KZ sY dY) m ≫
          (hypercohomology (space sY) m).map (ιZ sY dY hΘY CY)) ≫
        CategoryTheory.inv ((hypercohomology (space sY) m).map (εZ sY dY hΘY CY)) ≫
        sheafCohomologyPullback (analyticMap g hg) (constSh (space sY)) m ≫
          (sheafCohomology (space sX) m).map (toConst (analyticMap g hg)) := by
  exact eq_of_eq_comp_comp_of_eq _ _ _ _ (R3_lhs sX sY dX dY hΘX CX g hg m)
    (R3_rhs sX sY dX dY hΘX CX hΘY CY g hg θA hε m)
    (congrArg (fun χ => HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map χ (ComplexShape.up ℤ)) m) hι)

end R3

section Eps

open AlgebraicGeometry MMP.Analytic.Analytification MMP.Analytic.ComplexPoints DRCmp SingCmp
open AnPull
open scoped Manifold ContDiff

attribute [local implicit_reducible] TopCat.Sheaf

variable {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
variable {nX : ℕ} [csX : ChartedSpace (EuclideanSpace ℂ (Fin nX)) (ComplexPoints sX)]
  [hmX : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin nX)) ∞ (ComplexPoints sX)]
  {ΘX : structureSheaf sX ≅ 𝒪[nX, ComplexPoints sX]}
  (hΘX : ∀ (V : X.Opens) (a : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
      ΘX.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CX : ∀ y, ChartData sX nX ΘX y)
variable {nY : ℕ} [csY : ChartedSpace (EuclideanSpace ℂ (Fin nY)) (ComplexPoints sY)]
  [hmY : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin nY)) ∞ (ComplexPoints sY)]
  {ΘY : structureSheaf sY ≅ 𝒪[nY, ComplexPoints sY]}
  (hΘY : ∀ (V : Y.Opens) (a : Γ(Y, V)) (y : (Opens.map (toSchemeHom sY)).obj V),
      ΘY.hom.hom.app (op _) ((analytificationHom sY).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
  (CY : ∀ y, ChartData sY nY ΘY y)
variable (g : X ⟶ Y) (hg : g ≫ sY = sX)

/-- The hom-equivalence of a composite adjunction, in terms of the unit of the second one. -/
theorem adj_comp_unit {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F₁ : C ⥤ D} {G₁ : D ⥤ C} {F₂ : D ⥤ E} {G₂ : E ⥤ D} (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)
    {A : C} {M : E} (f : F₂.obj (F₁.obj A) ⟶ M) :
    adj₁.homEquiv A (G₂.obj M) (adj₂.unit.app (F₁.obj A) ≫ G₂.map f) =
      (adj₁.comp adj₂).homEquiv A M f := by
  simp [Adjunction.comp_homEquiv, Adjunction.homEquiv_unit]

/-- The hom-equivalence of an adjunction is natural in the target. -/
theorem adj_symm_comp {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {A : C} {M N : D} (w : A ⟶ G.obj M) (e : M ⟶ N) :
    adj.homEquiv A N ((adj.homEquiv A M).symm w ≫ e) = w ≫ G.map e := by
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]

/-- The pull-back of analytic `0`-forms is compatible with the inclusions of the constants. -/
theorem εan_θS :
    εan sY hΘY CY ≫ θS sX sY hΘX CX hΘY CY g hg 0 =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (analyticMap g hg)).unit.app
          (constSh (space sY)) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).map
          (toConst (analyticMap g hg) ≫ εan sX hΘX CX) := by
  have h1 := adj_comp_unit (constantSheafAdj (Opens.grothendieckTopology (space sY))
    AddCommGrpCat.{0} Limits.isTerminalTop)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (analyticMap g hg))
    (A := AddCommGrpCat.of ℂ) (M := (SheafOfModules.toSheaf (ringCatSheaf sX)).obj (Ωan sX 0))
    (toConst (analyticMap g hg) ≫ εan sX hΘX CX)
  have h2 := adj_symm_comp ((constantSheafAdj (Opens.grothendieckTopology (space sY))
    AddCommGrpCat.{0} Limits.isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (analyticMap g hg)))
    ((constantSheafAdj (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}
        Limits.isTerminalTop).unit.app (AddCommGrpCat.of ℂ) ≫
      (constSh (space sX)).obj.map (homOfLE le_top).op) (εan sX hΘX CX)
  have key : (constantSheafAdj (Opens.grothendieckTopology (space sY)) AddCommGrpCat.{0}
      Limits.isTerminalTop).unit.app (AddCommGrpCat.of ℂ) ≫
      ((sheafSections (Opens.grothendieckTopology (space sY)) AddCommGrpCat.{0}).obj (op ⊤)).map
        (εan sY hΘY CY ≫ θS sX sY hΘX CX hΘY CY g hg 0) =
      ((constantSheafAdj (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}
        Limits.isTerminalTop).unit.app (AddCommGrpCat.of ℂ) ≫
      (constSh (space sX)).obj.map (homOfLE le_top).op) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg) ⋙
        (sheafSections (Opens.grothendieckTopology (space sY)) AddCommGrpCat.{0}).obj (op ⊤)).map
          (εan sX hΘX CX) := by
    ext c
    have hL : ((constantSheafAdj (Opens.grothendieckTopology (space sY)) AddCommGrpCat.{0}
        Limits.isTerminalTop).unit.app (AddCommGrpCat.of ℂ) ≫
        ((sheafSections (Opens.grothendieckTopology (space sY)) AddCommGrpCat.{0}).obj (op ⊤)).map
          (εan sY hΘY CY ≫ θS sX sY hΘX CX hΘY CY g hg 0)) c =
        θfun sX sY hΘX CX hΘY CY g hg ((εan sY hΘY CY).hom.app (op ⊤)
          ((toSheafify (Opens.grothendieckTopology (space sY)) (constPre sY)).app (op ⊤) c)) := rfl
    have hR : (((constantSheafAdj (Opens.grothendieckTopology (space sX)) AddCommGrpCat.{0}
        Limits.isTerminalTop).unit.app (AddCommGrpCat.of ℂ) ≫
      (constSh (space sX)).obj.map (homOfLE le_top).op) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg) ⋙
        (sheafSections (Opens.grothendieckTopology (space sY)) AddCommGrpCat.{0}).obj (op ⊤)).map
          (εan sX hΘX CX)) c =
        (Ωan sX 0).val.presheaf.map (homOfLE (le_top :
          (Opens.map (analyticMap g hg)).obj ⊤ ≤ ⊤)).op ((εan sX hΘX CX).hom.app (op ⊤)
          ((toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX)).app (op ⊤) c)) :=
      (ConcreteCategory.congr_hom ((εan sX hΘX CX).hom.naturality
        (homOfLE (le_top : (Opens.map (analyticMap g hg)).obj ⊤ ≤ ⊤)).op)
        ((toSheafify (Opens.grothendieckTopology (space sX)) (constPre sX)).app (op ⊤) c))
    rw [hL, hR]
    apply val_injective sX hΘX CX
    intro x hx
    have hconst : ∀ (c' : ℂ) (D : EuclideanSpace ℂ (Fin nX) →L[ℂ] EuclideanSpace ℂ (Fin nY)),
        (ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin nY)) (Fin 0)
          c').compContinuousLinearMap D =
        ContinuousAlternatingMap.constOfIsEmpty ℂ (EuclideanSpace ℂ (Fin nX)) (Fin 0) c' := by
      intro c' D; ext v; rfl
    exact (val_θfun sX sY hΘX CX hΘY CY g hg _ x hx).trans
      ((congrArg (fun A => A.compContinuousLinearMap (Dκ sX sY CX CY g hg x))
        (val_εan_top sY hΘY CY c (realize g hg x))).trans ((hconst _ _).trans
          ((val_εan_top sX hΘX CX c x).symm.trans (val_res sX hΘX CX _ _ x hx).symm)))
  apply ((constantSheafAdj (Opens.grothendieckTopology (space sY)) AddCommGrpCat.{0}
    Limits.isTerminalTop).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]
  exact key.trans (h2.symm.trans h1.symm)

/-- Cancellation of an isomorphism and its inverse in the middle of a composite. -/
theorem cancel_mid {C : Type*} [Category* C] {P Q R S U : C} (x : P ⟶ Q) (y : Q ⟶ R)
    (e : S ≅ R) (z : R ⟶ U) (w : P ⟶ Q) (hw : w = x) :
    (x ≫ y ≫ e.inv) ≫ e.hom ≫ z = w ≫ y ≫ z := by
  subst hw; simp

/-- A map `εY` equal to the adjoint of `t`, precomposed with an isomorphism, is the adjoint of the
correspondingly transported map. -/
theorem hom_comp_eq_unit_app_comp_map_of_eq {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (R : D ⥤ C)
    (adj : L ⊣ R) {S c : C} {P M : D} (e : S ≅ c) (i : P ≅ L.obj c) (t : L.obj c ⟶ M)
    (εY : c ⟶ R.obj M) (hKE : εY = adj.unit.app c ≫ R.map (t)) :
    e.hom ≫ εY = adj.unit.app S ≫ R.map ((L.map e.hom ≫ i.inv) ≫ (i.hom ≫ t)) := by
  rw [hKE, ← Category.assoc]
  have hn := adj.unit.naturality e.hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [hn]
  simp

variable (dX dY : ℕ) [SmoothOfRelativeDimension dX sX] [SmoothOfRelativeDimension dY sY]

/-- The pull-back of holomorphic de Rham complexes is compatible with the inclusions of the
constants. -/
theorem hε_θA : εZ sY dY hΘY CY ≫ θA sX sY dX dY hΘX CX hΘY CY g hg =
    εR sX sY g hg ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).map
        (εZ sX dX hΘX CX) := by
  apply HomologicalComplex.from_single_hom_ext
  have e1 : (εZ sY dY hΘY CY ≫ θA sX sY dX dY hΘX CX hΘY CY g hg).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (constSh (space sY))).hom ≫
        (εan sY hΘY CY ≫ θS sX sY hΘX CX hΘY CY g hg 0) := by
    rw [HomologicalComplex.comp_f, εZ_f_zero]
    exact Category.assoc _ _ _
  have e3 : ((HomologicalComplex.singleMapHomologicalComplex
        (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)) (ComplexShape.up ℤ) 0).hom.app
          (constSh (space sY)) ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (toConst (analyticMap g hg))).f 0 ≫
        (εZ sX dX hΘX CX).f 0 =
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (constSh (space sY))).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).obj
            (constSh (space sY)))).inv) ≫
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).obj
            (constSh (space sY)))).hom ≫ (toConst (analyticMap g hg) ≫ εan sX hΘX CX)) := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, εZ_f_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact cancel_mid ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (constSh (space sY))).hom)
      (toConst (analyticMap g hg))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (constSh (space sX)))
      (εan sX hΘX CX) _ rfl
  have e2 : (εR sX sY g hg ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).mapHomologicalComplex _).map
        (εZ sX dX hΘX CX)).f 0 =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (analyticMap g hg)).unit.app
          (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (constSh (space sY))).X 0) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg)).map
          (((HomologicalComplex.singleMapHomologicalComplex
            (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)) (ComplexShape.up ℤ) 0).hom.app
              (constSh (space sY)) ≫
            (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
              (toConst (analyticMap g hg))).f 0 ≫ (εZ sX dX hΘX CX).f 0) := by
    simp only [HomologicalComplex.comp_f, Functor.map_comp, Category.assoc]
    rfl
  rw [e1, e2, e3]
  exact hom_comp_eq_unit_app_comp_map_of_eq
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg))
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (analyticMap g hg))
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (analyticMap g hg))
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (constSh (space sY)))
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (analyticMap g hg)).obj (constSh (space sY))))
    (toConst (analyticMap g hg) ≫ εan sX hΘX CX)
    (εan sY hΘY CY ≫ θS sX sY hΘX CX hΘY CY g hg 0) (εan_θS sX sY hΘX CX hΘY CY g hg)

/-- Splitting the image of a composite under a functor. -/
theorem comp_comp_map_comp_eq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {P Q : D} {R S T : C}
    (a : P ⟶ Q) (b : Q ⟶ F.obj R) (c : R ⟶ S) (d : S ⟶ T) :
    a ≫ b ≫ F.map (c ≫ d) = (a ≫ b ≫ F.map c) ≫ F.map d := by
  simp

/-- Cancellation of two isomorphisms and their inverses around `d`. -/
theorem inv_hom_comp_comp_map_inv_comp_map_hom {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B : D} {P Q : C}
    (e : A ≅ B) (e' : P ≅ Q) (d : B ⟶ F.obj Q) :
    e.inv ≫ (e.hom ≫ d ≫ F.map e'.inv) ≫ F.map e'.hom = d := by
  simp [← F.map_comp]

/-- In each degree, the unit `KZ ⟶ α_* α⁻¹ KZ` followed by `α_* ιZ` is the analytification unit
of the de Rham module. -/
theorem unit_ι_f {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (d : ℕ) {n : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sZ)]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sZ)]
    {Θ : structureSheaf sZ ≅ 𝒪[n, ComplexPoints sZ]}
    (hΘ : ∀ (V : Z.Opens) (a : Γ(Z, V)) (y : (Opens.map (toSchemeHom sZ)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom sZ).hom.c.app (op V) a) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ a)
    (C : ∀ y, ChartData sZ n Θ y) [SmoothOfRelativeDimension d sZ] (p : ℤ) :
    (unitC (toSchemeHom sZ) (KZ sZ d)).f p ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sZ)).map ((ιZ sZ d hΘ C).f p) =
      (SheafOfModules.toSheaf _).map (analytifyModuleUnit sZ (FZ sZ d p)) := by
  have h := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0}
    (toSchemeHom sZ)).homEquiv_unit (X := (SheafOfModules.toSheaf _).obj (FZ sZ d p))
    (Y := (SheafOfModules.toSheaf _).obj ((analytifyModule sZ).obj (FZ sZ d p)))
    (analytifyModuleι sZ (FZ sZ d p))).symm
  unfold analytifyModuleι at h
  exact h.trans (Equiv.apply_symm_apply _ _)

/-- The algebraic pull-back of de Rham complexes along `g` followed by analytification agrees with
analytification followed by the analytic pull-back `θA`, as maps of Godement sections double
complexes. -/
theorem hι_θA :
    secDC (K := KZ sY dY) (L := KanZ sX dX hΘX CX) (toSchemeHom sX ≫ g.base)
      ((eKZ sY dY).hom ≫
        (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          ((eKZ sX dX).inv ≫ unitC (toSchemeHom sX) (KZ sX dX) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).mapHomologicalComplex
              _).map (ιZ sX dX hΘX CX))) =
      secDC (K := KZ sY dY) (L := KanZ sX dX hΘX CX) (analyticMap g hg ≫ toSchemeHom sY)
        ((unitC (toSchemeHom sY) (KZ sY dY) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sY)).mapHomologicalComplex
              _).map (ιZ sY dY hΘY CY)) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sY)).mapHomologicalComplex
              _).map (θA sX sY dX dY hΘX CX hΘY CY g hg)) := by
  refine secDC_transport (toSchemeHom_comp_base sX sY g hg) _ _ (fun p U s => ?_)
  cases p with
  | ofNat k =>
    have hφ := HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
      (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{0, 0} g.base)
      (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras sX)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)))
      (Scheme.Hom.deRhamAbelianPushforwardMap g sY sX (𝟙 _) (by rw [hg, Category.comp_id]))
      ComplexShape.embeddingUpNat (i := k) (i' := Int.ofNat k) rfl
    have hu := unit_ι_f sX dX hΘX CX (Int.ofNat k)
    have hu' := unit_ι_f sY dY hΘY CY (Int.ofNat k)
    have e2 : ((((unitC (toSchemeHom sY) (KZ sY dY) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sY)).mapHomologicalComplex
              _).map (ιZ sY dY hΘY CY)) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sY)).mapHomologicalComplex
              _).map (θA sX sY dX dY hΘX CX hΘY CY g hg)).f (Int.ofNat k)).hom.app (op U) s) =
        θfun sX sY hΘX CX hΘY CY g hg (uS sY s) :=
      congrArg (θfun sX sY hΘX CX hΘY CY g hg)
        (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op U)) hu') s)
    have hZ : (((eKZ sY dY).hom ≫
        (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          (eKZ sX dX).inv).f (Int.ofNat k)).hom.app (op U) s = φS sX sY g hg s := by
      have h0 := inv_hom_comp_comp_map_inv_comp_map_hom
        (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{0, 0} g.base)
        ((AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras sY)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras sY))).extendXIso ComplexShape.embeddingUpNat
            (i := k) (i' := Int.ofNat k) rfl)
        ((AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras sX)
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras sX))).extendXIso ComplexShape.embeddingUpNat
            (i := k) (i' := Int.ofNat k) rfl)
        ((Scheme.Hom.deRhamAbelianPushforwardMap g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).f k)
      have h2 : ((eKZ sY dY).hom ≫
          (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
            (by rw [hg, Category.comp_id])).hom ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
            (eKZ sX dX).inv).f (Int.ofNat k) =
          (Scheme.Hom.deRhamAbelianPushforwardMap g sY sX (𝟙 _)
            (by rw [hg, Category.comp_id])).f k := by
        refine Eq.trans (rfl : _ = (HomologicalComplex.extendXIso
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras sY)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras sY))) ComplexShape.embeddingUpNat
                (i := k) (i' := Int.ofNat k) rfl).inv ≫
          (HomologicalComplex.extendMap
            (Scheme.Hom.deRhamAbelianPushforwardMap g sY sX (𝟙 _) (by rw [hg, Category.comp_id]))
            ComplexShape.embeddingUpNat ≫
          (HomologicalComplex.mapHomologicalComplexExtendIso
            (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{0, 0} g.base)
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras sX)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)))
            ComplexShape.embeddingUpNat).hom).f (Int.ofNat k) ≫
          (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{0, 0} g.base).map
            (HomologicalComplex.extendXIso
            (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras sX)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras sX))) ComplexShape.embeddingUpNat
                (i := k) (i' := Int.ofNat k) rfl).hom) ?_
        rw [hφ]
        exact h0
      rw [h2]
      rfl
    have hsplit : (eKZ sY dY).hom ≫
        (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          ((eKZ sX dX).inv ≫ unitC (toSchemeHom sX) (KZ sX dX) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).mapHomologicalComplex
              _).map (ιZ sX dX hΘX CX)) =
        ((eKZ sY dY).hom ≫
        (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          (eKZ sX dX).inv) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          (unitC (toSchemeHom sX) (KZ sX dX) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).mapHomologicalComplex
              _).map (ιZ sX dX hΘX CX)) :=
      comp_comp_map_comp_eq _ _ _ _ _
    have e1 : (((eKZ sY dY).hom ≫
        (Scheme.Hom.deRhamAbelianPushforwardMapPlus g sY sX (𝟙 _)
          (by rw [hg, Category.comp_id])).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} g.base).mapHomologicalComplex _).map
          ((eKZ sX dX).inv ≫ unitC (toSchemeHom sX) (KZ sX dX) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (toSchemeHom sX)).mapHomologicalComplex
              _).map (ιZ sX dX hΘX CX))).f (Int.ofNat k)).hom.app (op U) s =
        uS sX (φS sX sY g hg s) := by
      rw [hsplit, HomologicalComplex.comp_f]
      erw [ConcreteCategory.comp_apply]
      rw [hZ]
      exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op (g ⁻¹ᵁ U))) hu)
        (φS sX sY g hg s)
    exact e1.trans ((uS_φS_eq sX sY hΘX CX hΘY CY g hg (k := k) s).trans (congrArg _ e2.symm))
  | negSucc j =>
    have hz := isZero_toSheaf_FZ_negSucc sY dY j
    have hs : s = 0 := by
      have h := ConcreteCategory.congr_hom
        (congrArg (fun φ => φ.hom.app (op U)) (hz.eq_of_src (𝟙 _) 0)) s
      exact h
    subst hs
    erw [map_zero, map_zero]
    rfl

/-- A commutative square `x ≫ y ≫ z = w ≫ v`, postcomposed with `R`. -/
theorem comp_comp_eq_comp_comp_of_comm {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ Q₃ : C}
    (x : P₀ ⟶ P₁) (y : P₁ ⟶ P₂) (z : P₂ ⟶ P₃) (R : P₃ ⟶ P₄) (w : P₀ ⟶ Q₃) (v : Q₃ ⟶ P₃)
    (h2 : x ≫ y ≫ z = w ≫ v) : (x ≫ y) ≫ (z ≫ R) = w ≫ (v ≫ R) := by
  simp only [Category.assoc]
  rw [reassoc_of% h2]

/-- Reassociation of a composite of seven morphisms. -/
theorem assoc7 {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : C}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (d : P₃ ⟶ P₄) (e : P₄ ⟶ P₅) (s : P₅ ⟶ P₆)
    (t : P₆ ⟶ P₇) :
    a ≫ b ≫ c ≫ d ≫ e ≫ s ≫ t = (a ≫ b ≫ c ≫ d ≫ e) ≫ s ≫ t := by
  simp only [Category.assoc]

/-- The comparison `Φ : H^m_dR(X) ≅ H^m(X^an, ℂ)` is natural in morphisms of smooth projective
varieties over `ℂ`. -/
theorem Φ_natural [IsProjectiveVariety ℂ sX] [IsProjectiveVariety ℂ sY] (m : ℤ) :
    Scheme.Hom.deRhamCohomologyPullback g sY sX (𝟙 _) (by rw [hg, Category.comp_id]) m ≫
        (Φ sX dX hΘX CX m).hom =
      (Φ sY dY hΘY CY m).hom ≫ sheafCohomologyPullback (analyticMap g hg) (constSh (space sY)) m ≫
        (sheafCohomology (space sX) m).map (toConst (analyticMap g hg)) := by
  haveI := isIso_gaga sX dX hΘX CX m
  haveI := isIso_hypercohomology_εZ sX dX hΘX CX m
  haveI := isIso_gaga sY dY hΘY CY m
  haveI := isIso_hypercohomology_εZ sY dY hΘY CY m
  have h2 := bridge_pullback sX sY g hg m
  have h3 := R3_eq sX sY dX dY hΘX CX hΘY CY g hg (θA sX sY dX dY hΘX CX hΘY CY g hg)
      (hε_θA sX sY hΘX CX hΘY CY g hg dX dY) (hι_θA sX sY hΘX CX hΘY CY g hg dX dY) m
  rw [pullback_eq sX sY g hg m, Φ_hom_eq sX dX hΘX CX m, Φ_hom_eq sY dY hΘY CY m]
  refine (comp_comp_eq_comp_comp_of_comm _ _ _ _ _ _ h2).trans ?_
  refine (whisker_eq _ h3).trans ?_
  simp only [Category.assoc]
  exact assoc7 _ _ _ _ _ _ _

end Eps

end NatCmp

end Naturality

section AnalyticAssemble

open CategoryTheory.Limits TopologicalSpace
open MMP.Analytic.Analytification MMP.Analytic.ComplexPoints
open scoped Manifold ContDiff

namespace Assemble

open DRCmp SingCmp MMP

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] globalSections_additive
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

/-- The auxiliary data of the comparison on one smooth projective variety. -/
structure CData {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) where
  /-- The relative dimension of `X`. -/
  d : ℕ
  /-- `X` is smooth of relative dimension `d` over `ℂ`. -/
  smooth : SmoothOfRelativeDimension d sX
  /-- The complex dimension of the manifold of complex points. -/
  n : ℕ
  /-- The charted-space structure on the complex points. -/
  cs : ChartedSpace (EuclideanSpace ℂ (Fin n)) (ComplexPoints sX)
  /-- The complex points form a complex manifold. -/
  hmfd : (letI := cs; IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ (ComplexPoints sX))
  /-- An identification of the analytic structure sheaf with the sheaf of holomorphic functions. -/
  Θ : (letI := cs; structureSheaf sX ≅ 𝒪[n, ComplexPoints sX])
  hΘ : ∀ (V : X.Opens) (g : Γ(X, V)) (y : (Opens.map (toSchemeHom sX)).obj V),
    Θ.hom.hom.app (op _) ((analytificationHom sX).hom.c.app (op V) g) y =
      evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g
  /-- Chart data at every complex point. -/
  C : ∀ y, (letI := cs; ChartData sX n Θ y)

/-- A smooth projective complex variety admits the data `CData` of the comparison. -/
theorem nonempty_cData {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sX]
    (hX : MMP.Mori.IsSmoothScheme sX) : Nonempty (CData sX) := by
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).1 hX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_eq_natCast sX
  obtain ⟨n, cs, hmfd, Θ, hΘ, hC⟩ := exists_chartData sX hX
  exact ⟨⟨d, MMP.Intersection.smoothOfRelativeDimension_of_isVariety sX d hd, n, cs, hmfd, Θ, hΘ,
    fun y => (hC y).some⟩⟩

/-- The additive comparison attached to the data. -/
noncomputable def ΦD {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsProjectiveVariety ℂ sX]
    (D : CData sX) (m : ℤ) :=
  letI := D.cs; haveI := D.hmfd; haveI := D.smooth
  Φ sX D.d D.hΘ D.C m

/-- The comparison `ΦD` is natural in morphisms of smooth projective varieties over `ℂ`. -/
theorem ΦD_natural {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    [IsProjectiveVariety ℂ sX] [IsProjectiveVariety ℂ sY] (DX : CData sX) (DY : CData sY)
    (g : X ⟶ Y) (hg : g ≫ sY = sX) (m : ℤ) (y : Scheme.Hom.deRhamCohomology sY m) :
    (ΦD DX m).hom (Scheme.Hom.deRhamCohomologyPullback g sY sX (𝟙 _)
        (by rw [hg, Category.comp_id]) m y) =
      (sheafCohomologyPullback (ComplexPoints.analyticMap g hg) (constSh (analyticSpace sY)) m ≫
        (sheafCohomology (analyticSpace sX) m).map (toConst (ComplexPoints.analyticMap g hg)))
        ((ΦD DY m).hom y) := by
  letI := DX.cs; haveI := DX.hmfd; haveI := DX.smooth
  letI := DY.cs; haveI := DY.hmfd; haveI := DY.smooth
  exact ConcreteCategory.congr_hom
    (NatCmp.Φ_natural sX sY DX.hΘ DX.C DY.hΘ DY.C g hg DX.d DY.d m) y

/-- Relative singular cohomology relative to `∅` and to `univᶜ`. -/
noncomputable def jIso (M : TopCat.{0}) (m : ℤ) :
    relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) M ∅ m ≅
      relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) M (Set.univ : Set M)ᶜ m where
  hom := relativeSingularCohomology.map ℂ _ (𝟙 M)
    (show (Set.univ : Set M)ᶜ ⊆ (𝟙 M : M ⟶ M) ⁻¹' ∅ from fun x hx => absurd (Set.mem_univ x) hx) m
  inv := relativeSingularCohomology.map ℂ _ (𝟙 M)
    (show (∅ : Set M) ⊆ (𝟙 M : M ⟶ M) ⁻¹' (Set.univ : Set M)ᶜ from fun _ hx => hx.elim) m
  hom_inv_id := (relativeSingularCohomology.map_comp ℂ _ (𝟙 M) (𝟙 M) _ _ m).symm.trans
    (relativeSingularCohomology.map_id ℂ _ M ∅ m)
  inv_hom_id := (relativeSingularCohomology.map_comp ℂ _ (𝟙 M) (𝟙 M) _ _ m).symm.trans
    (relativeSingularCohomology.map_id ℂ _ M _ m)

/-- The isomorphism `jIso` is natural in continuous maps. -/
lemma jIso_naturality {M N : TopCat.{0}} (f : N ⟶ M) (m : ℤ) :
    (jIso M m).hom ≫ relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) f
        (show (Set.univ : Set N)ᶜ ⊆ f ⁻¹' (Set.univ : Set M)ᶜ from
          fun _ hx => absurd (Set.mem_univ _) hx) m =
      relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) f (Set.empty_subset _) m ≫
        (jIso N m).hom :=
  (relativeSingularCohomology.map_comp ℂ _ f (𝟙 M) _ _ m).symm.trans
    (relativeSingularCohomology.map_comp ℂ _ (𝟙 N) f _ _ m)

/-- The analytic space of a complex projective variety is metrizable and locally
contractible. -/
theorem metrizable_lc {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sX] :
    MetrizableSpace (analyticSpace sX) ∧ LocallyContractibleSpace (analyticSpace sX) := by
  have h := ComplexPoints.metrizableSpace_and_stronglyLocallyContractibleSpace sX
  exact ⟨h.1, haveI := h.2; StronglyLocallyContractibleSpace.locallyContractible⟩

/-- The comparison isomorphisms, natural in morphisms over `ℂ`. -/
theorem exists_natural_comparison :
    ∃ e : ∀ (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sX],
        MMP.Mori.IsSmoothScheme sX → ∀ n : ℕ,
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of ℂ)).inv.hom).obj
            (sX.deRhamCohomologyBaseModule n) ≃ₗ[ℂ]
          cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) (ComplexPoints.analyticSpace sX)
            Set.univ n,
      (∀ (X Y : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
        [IsProjectiveVariety ℂ sX] [IsProjectiveVariety ℂ sY] (hX : MMP.Mori.IsSmoothScheme sX)
        (hY : MMP.Mori.IsSmoothScheme sY) (g : X ⟶ Y) (hg : g ≫ sY = sX) (n : ℕ)
        (y : sY.deRhamCohomology n),
        e X sX hX n ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ n).hom
            (Scheme.Hom.deRhamCohomologyPullback g sY sX (𝟙 _)
              (by rw [hg, Category.comp_id]) n y)) =
          relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) (ComplexPoints.analyticMap g hg)
            (fun _ hx ↦ absurd (Set.mem_univ _) hx) n
            (e Y sY hY n
              ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ n).hom y))) := by
  choose Λ hΛs hΛn using exists_singular
  let eA : ∀ (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sX],
      MMP.Mori.IsSmoothScheme sX → ∀ n : ℕ,
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of ℂ)).inv.hom).obj
          (sX.deRhamCohomologyBaseModule n) ≃+
        cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) (ComplexPoints.analyticSpace sX)
          Set.univ n := fun X sX _ hX n =>
    haveI := (metrizable_lc sX).1
    (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).symm.addCommGroupIsoToAddEquiv.trans
      ((ΦD (nonempty_cData sX hX).some n).addCommGroupIsoToAddEquiv.trans
        ((Λ n (analyticSpace sX) (metrizable_lc sX).2).trans
          ((jIso (analyticSpace sX) n).toLinearEquiv.toAddEquiv)))
  refine ⟨fun X sX _ hX n => { eA X sX hX n with map_smul' := ?_ }, ?_⟩
  · intro c x
    set D := (nonempty_cData sX hX).some
    letI := D.cs
    haveI := D.hmfd
    haveI := D.smooth
    haveI := (metrizable_lc sX).1
    have h1 := abIso_hom_ψdR (Scheme.Hom.deRhamAlgebras sX)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))
      (tC sX c) n ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv x)
    have h1' : (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv (c • x) =
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} n).map
          ((Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map (ψdR (Scheme.Hom.deRhamAlgebras sX)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))
                (tC sX c)))))
          ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv x) := by
      have h2 := congrArg (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv h1
      erw [Iso.hom_inv_id_apply, Iso.inv_hom_id_apply] at h2
      exact h2.symm
    have h3 := ConcreteCategory.congr_hom (Φ_linear sX D.d D.hΘ D.C n c)
      ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv x)
    have h4 := hΛs n (analyticSpace sX) (metrizable_lc sX).2 c
      ((ΦD D n).hom ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv x))
    change (jIso _ n).hom (Λ n _ _ ((ΦD D n).hom
        ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv (c • x)))) =
      c • (jIso _ n).hom (Λ n _ _ ((ΦD D n).hom
        ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv x)))
    rw [h1']
    have h5 : (ΦD D n).hom (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} n).map
          ((Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map (ψdR (Scheme.Hom.deRhamAlgebras sX)
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX))
                (tC sX c))))) ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv x)) =
        (MMP.Analytic.sheafCohomology (analyticSpace sX) n).map
          ((constantSheaf (Opens.grothendieckTopology (analyticSpace sX)) AddCommGrpCat.{0}).map
            (AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)))
          ((ΦD D n).hom ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv x)) := h3
    rw [h5, h4]
    exact (jIso _ n).hom.hom.map_smul c _
  · intro X Y sX sY _ _ hX hY g hg n y
    haveI := (metrizable_lc sX).1
    haveI := (metrizable_lc sY).1
    change (jIso _ n).hom (Λ n _ _ ((ΦD (nonempty_cData sX hX).some n).hom ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).inv ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sX) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sX)) n).hom
        (Scheme.Hom.deRhamCohomologyPullback g sY sX (𝟙 _) (by rw [hg, Category.comp_id]) n y))))) =
      relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) (ComplexPoints.analyticMap g hg)
        (fun _ hx ↦ absurd (Set.mem_univ _) hx) n
        ((jIso _ n).hom (Λ n _ _ ((ΦD (nonempty_cData sY hY).some n).hom ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sY) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sY)) n).inv ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras sY) (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras sY)) n).hom y)))))
    erw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
    rw [ΦD_natural (nonempty_cData sX hX).some (nonempty_cData sY hY).some g hg n y, hΛn n (analyticSpace sY) (analyticSpace sX)
      (metrizable_lc sY).2 (metrizable_lc sX).2 (ComplexPoints.analyticMap g hg)]
    exact (ConcreteCategory.congr_hom (jIso_naturality (ComplexPoints.analyticMap g hg) n)
      (Λ n _ (metrizable_lc sY).2 ((ΦD (nonempty_cData sY hY).some n).hom y))).symm

end Assemble

end AnalyticAssemble

end DeRhamComparison

end MMP.DeRhamBetti

@[expose] public section

namespace MMP.Analytic

/-- **Algebraic de Rham cohomology of a smooth projective complex variety is singular
cohomology.** There are `ℂ`-linear isomorphisms `H^n_{dR}(V/ℂ) ≃ H^n(V^an; ℂ)` for every smooth
projective complex variety `V` and every `n`, natural with respect to every morphism `g : V ⟶ W`
over `ℂ` (de Rham pullback on the left, singular pullback along `g^an` on the right). Moreover,
for every such `V`, `b₁(V) = h⁰(V, Ω¹_V) + h¹(V, 𝒪_V)`, and the exterior derivative of every
global one-form vanishes. -/
@[mmp "lem_mmp_conductor_projective_de_rham_betti"]
public theorem exists_deRhamCohomology_linearEquiv_singularCohomology :
    ∃ e : ∀ (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sX],
        MMP.Mori.IsSmoothScheme sX → ∀ n : ℕ,
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of ℂ)).inv.hom).obj
            (sX.deRhamCohomologyBaseModule n) ≃ₗ[ℂ]
          cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ) (ComplexPoints.analyticSpace sX)
            Set.univ n,
      (∀ (X Y : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
        [IsProjectiveVariety ℂ sX] [IsProjectiveVariety ℂ sY] (hX : MMP.Mori.IsSmoothScheme sX)
        (hY : MMP.Mori.IsSmoothScheme sY) (g : X ⟶ Y) (hg : g ≫ sY = sX) (n : ℕ)
        (y : sY.deRhamCohomology n),
        e X sX hX n ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ n).hom
            (Scheme.Hom.deRhamCohomologyPullback g sY sX (𝟙 _)
              (by rw [hg, Category.comp_id]) n y)) =
          relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) (ComplexPoints.analyticMap g hg)
            (fun _ hx ↦ absurd (Set.mem_univ _) hx) n
            (e Y sY hY n
              ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology _ _ n).hom y))) ∧
      ∀ (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sX],
        MMP.Mori.IsSmoothScheme sX →
        Module.finrank ℂ (cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ)
            (ComplexPoints.analyticSpace sX) Set.univ 1) =
          Module.finrank ℂ (cohomologyOverField ℂ sX (Scheme.Hom.relativeDifferentials sX) 0) +
            Module.finrank ℂ (cohomologyOverField ℂ sX (SheafOfModules.unit X.ringCatSheaf) 1) ∧
        ∀ ω : ((sX.deRhamComplex).X 1).val.obj (op ⊤),
          ((sX.deRhamComplex).d 1 2).val.app (op ⊤) ω = 0 := by
  obtain ⟨e, he⟩ := MMP.DeRhamBetti.Assemble.exists_natural_comparison
  refine ⟨e, he, fun X sX _ hX => ?_⟩
  exact ⟨(e X sX hX 1).finrank_eq.symm.trans (MMP.DeRhamBetti.finrank_deRham_one X sX hX),
    MMP.DeRhamBetti.deRhamComplex_d_one_eq_zero X sX hX⟩

end MMP.Analytic

end
