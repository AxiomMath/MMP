module

public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.KodairaRestriction
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.PreimageDimension
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.ExpUniformisation
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.ZariskiClosureDimension
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.RationalSubspace
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.AlgebraicGermSubgroup
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.TrivialOnAmpleDivisor
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.IntegralCohomologyRank
public import MMP.AlgebraicGeometry.DeRham.BettiComparison
public import MMP.Analysis.Complex.WeierstrassDivision
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.RestrictionGAGA
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.RestrictionTranslates
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.AnalytifyPullback
public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChangeGeneral
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.ZeroSchemeAmple
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Hodge symmetry in degree one for smooth projective surfaces

Let `X` be a smooth projective surface over `ℂ`. Then `h¹(X, 𝒪_X) ≤ h⁰(X, Ω¹_X)`.

Choose a very ample divisor `A` and, by Bertini, a section of `𝒪_X(A)` whose zero scheme `Z` is a
smooth projective connected curve; `Z` is a prime divisor `P`. Kodaira vanishing makes the
restriction `H¹(X, 𝒪_X) → H¹(Z, 𝒪_Z)` injective, and by GAGA so is its analytic counterpart. Let
`φ : ℂⁿ ≃ H¹(Z^an, 𝒪)` be the logarithmic coordinates of the Jacobian `J` of `Z`, `Λ` its period
lattice and `Φ : ℂⁿ → J(ℂ)` its exponential uniformisation, and let `V ⊆ ℂⁿ` be the preimage of the
image of `H¹(X^an, 𝒪)`, a complex subspace of dimension `h¹(𝒪_X)`. Every point of `Φ(V)` is the
restriction of a line bundle on `X`, so `Φ(V)` lies in countably many closed subsets of `J` of
dimension at most `dim V`; Baire's theorem and the identity principle then show that `V` is
spanned over `ℝ` by `V ∩ Λ`. A class `w` restricting into `Λ` has exponential `[L^an]` with
`L|_Z` trivial, so (as `P ± D` is ample for every numerically trivial `D`) `L` is trivial and `w`
comes from `H¹(X^an, ℤ)`. Hence the image of `H¹(X^an, ℤ)` spans `H¹(X, 𝒪_X)` over `ℝ`, so
`2 h¹(𝒪_X) ≤ b₁ = h⁰(Ω¹_X) + h¹(𝒪_X)`.

## Main definitions

* `MMP.Analytic.SurfaceHodge.expPicOf`: the exponential map `H¹(X^an, 𝒪) → Pic(X^an)`.

## Main results

* `MMP.Analytic.SurfaceHodge.span_inter_eq_of_forall_mem_iUnion`: rationality of `V` from a
  countable closed cover of `Φ(V)`.
* `MMP.Analytic.SurfaceHodge.mem_range_of_expPicOf_analyticRestrictionH1_eq_zero`: the period
  kernel on the curve.
* `MMP.Analytic.SurfaceHodge.span_real_range_sheafH_map_eq_top`: the image of `H¹(X^an, ℤ)` spans
  `H¹(X, 𝒪_X)` over `ℝ`.
* `MMP.Analytic.SurfaceHodge.two_mul_finrank_cohomologyOverField_unit_one_le_of_curve`:
  `2 h¹(𝒪_X) ≤ b₁`.
* `MMP.Analytic.SurfaceHodge.isAmple_sub_and_add_of_isNumericallyTrivial`: `A ± D` is ample for
  `A` ample and `D` numerically trivial.
* `MMP.Analytic.SurfaceHodge.finrank_cohomologyOverField_unit_one_le_of_surface_of`:
  `h¹(𝒪_X) ≤ h⁰(Ω¹_X)`, given `MMP.Analytic.SurfaceHodge.ZeroSchemePrimeDivisorAmple`.
* `MMP.Analytic.finrank_cohomologyOverField_unit_one_le_of_surface`: `h¹(𝒪_X) ≤ h⁰(Ω¹_X)`.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 2 §6.
* [D. Mumford, *Lectures on curves on an algebraic surface*], Lecture 19.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints MMP.Intersection
open MMP.JacobianLogarithm

namespace MMP.Analytic.SurfaceHodge

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf

section Defs

/-- The exponential map `H¹(X^an, 𝒪) → Pic(X^an)` of a map `e : 𝒪 ⟶ 𝒪^×`, read in the model
`Stacks.SheafOfModules.Picard.PicardGroup` through `H¹(X^an, 𝒪^×) ≅ Pic(X^an)`. -/
noncomputable abbrev expPicOf {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    (e : analyticO sX ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification sX)) :
    letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sX)
    Sheaf.H (analyticO sX) 1 →+ Stacks.SheafOfModules.Picard.PicardGroup
      (analytification sX : RingedSpace).sheaf.obj
      (structureSheaf (analytification sX : RingedSpace).sheaf).property :=
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification sX)
  (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification sX)).toAddMonoidHom.comp
    ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv (space sX)
      (Stacks.Cohomology.Generators.unitsSheaf (analytification sX)))).symm.toAddMonoidHom.comp
      (Sheaf.H.map e 1))

/-- `e : 𝒪 ⟶ 𝒪^×` is `u ↦ exp (2πi u)`, read on germs in every chart. -/
abbrev IsExpFormula {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (e : analyticO sX ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification sX)) : Prop :=
  ∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
    (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
    (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
    (γ : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
    (γ' : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
      (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
    s.1 x c = Chart.StalkRing.mk c.1 _ γ →
    ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
      (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ'

end Defs

section Curve

/-- A smooth projective connected curve `C` over `ℂ` has a `ℂ`-point, and its fibre over the
point of `Spec ℂ` has dimension at most one. -/
theorem fiber_dim_le_one_and_exists_section {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ))
    (hproj : IsProjective f) [SmoothOfRelativeDimension 1 f] [ConnectedSpace C] :
    (∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1) ∧
      ∃ σ : Spec (.of ℂ) ⟶ C, σ ≫ f = 𝟙 _ := by
  haveI := hproj.isProper
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  haveI : IsIntegral C := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth f
  have hC : topologicalKrullDim C = 1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1
  refine ⟨fun s => ?_, ?_⟩
  · rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo s).isHomeomorph]
    exact (topologicalKrullDim_subspace_le C _).trans hC.le
  · haveI : Nonempty C := inferInstance
    obtain ⟨σ, hσ, -⟩ := exists_section_of_isSepClosed f
    exact ⟨σ, hσ⟩

/-- The classifying map of a Jacobian on `ℂ`-points is injective. -/
theorem injective_cls {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) [IsProper f]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥(f.fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ f = 𝟙 _) {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero f hdim σ hσ) :
    Function.Injective (fun x : ComplexPoints JX.X.hom =>
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)) := by
  intro x y hxy
  have h := congrArg (eJ.inv.app (op (Over.mk (𝟙 _)))).hom hxy
  have hi : ∀ z, (eJ.inv.app (op (Over.mk (𝟙 _)))).hom
      ((eJ.hom.app (op (Over.mk (𝟙 (Spec (.of ℂ)))))).hom z) = z := fun z => by
    have := ConcreteCategory.congr_hom (eJ.hom_inv_id_app (op (Over.mk (𝟙 (Spec (.of ℂ)))))) z
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using this
  erw [hi, hi] at h
  have h2 := congrArg CommaMorphism.left h
  exact Subtype.ext (by simpa using h2)

end Curve

section PicardZero

universe v' u' w'

variable {Cc : Type u'} [Category.{v'} Cc] {J : GrothendieckTopology Cc}
  (O : Ccᵒᵖ ⥤ CommRingCat.{w'})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify J AddCommGrpCat.{w'}]

/-- The Picard class of a trivial invertible sheaf is zero: `[ℳ] + [ℳ] = [ℳ ⊗ ℳ] = [ℳ]`. -/
private theorem classOf_eq_zero_of_iso_unit'
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hM : Stacks.SheafOfModules.IsInvertible O hO M)
    (e : M ≅ SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.Picard.classOf O hO M hM = 0 := by
  have := hM
  have hMM := Stacks.SheafOfModules.isInvertible_tensorSheaf O hO M M
  have he := (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff O hO _ _ hMM hM).2
    ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w', w', w'}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).mapIso e).app M ≪≫
      Stacks.SheafOfModules.tensorSheafLeftUnitor O hO M⟩
  exact add_eq_left.mp ((Stacks.SheafOfModules.Picard.classOf_tensor O hO M M hM hM hMM).trans he)

end PicardZero

/-- **GAGA on a projective scheme: an invertible module with trivial analytification is
trivial.** -/
theorem nonempty_iso_unit_of_classOf_analytifyModule_eq_zero {C : Scheme.{0}}
    (f : C ⟶ Spec (.of ℂ)) (hproj : IsProjective f) (M : C.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C) M)
    (hMan : Stacks.SheafOfModules.IsInvertible (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property
      ((analytifyModule f).obj M))
    (h0 : letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
      Stacks.SheafOfModules.Picard.classOf _ _ _ hMan = 0) :
    Nonempty (M ≅ SheafOfModules.unit C.ringCatSheaf) := by
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup (analytification f)
  have hU : Stacks.SheafOfModules.IsInvertible C.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf C)
      (SheafOfModules.unit C.ringCatSheaf) :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  have hUan := @Stacks.RingedSpace.isInvertible_modulePullback _ _ (analytificationHom f) _ hU
  have hUan0 : Stacks.SheafOfModules.Picard.classOf _ _ _ hUan = 0 :=
    classOf_eq_zero_of_iso_unit' _ _ _ hUan (analytifyUnitIso f)
  have h1 := h0.trans hUan0.symm
  obtain ⟨hinvG, eG, heG, -⟩ := exists_mulEquiv_picardGroup_analytification_of_isProjective f hproj
  have h2 := ((picardToSheafPicard_classOf (analytification f : RingedSpace).sheaf.obj
    (structureSheaf (analytification f : RingedSpace).sheaf).property _ hMan).symm.trans
      (congrArg (picardToSheafPicard _ _) h1)).trans
    (picardToSheafPicard_classOf (analytification f : RingedSpace).sheaf.obj
      (structureSheaf (analytification f : RingedSpace).sheaf).property _ hUan)
  haveI : Stacks.Ample.IsInvertibleModule C M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).1 hM
  haveI : Stacks.Ample.IsInvertibleModule C (SheafOfModules.unit C.ringCatSheaf) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 hU
  have h3 : eG (Stacks.SheafPicardGroup.schemeClassOf C M) =
      eG (Stacks.SheafPicardGroup.schemeClassOf C (SheafOfModules.unit C.ringCatSheaf)) :=
    (heG M).trans ((Additive.ofMul.injective h2).trans (heG _).symm)
  exact (Stacks.SheafPicardGroup.schemeClassOf_eq_schemeClassOf_iff C M _).1 (eG.injective h3)

/-- The zero scheme of a nonzero section of an invertible module on an integral locally
Noetherian scheme, when integral, is a prime divisor. -/
theorem exists_primeDivisor_idealSheaf_eq_zeroScheme {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤))
    (hs : s ≠ 0) [IsIntegral (zeroScheme X L s).subscheme] :
    ∃ P : Mori.PrimeDivisor X, P.idealSheaf = zeroScheme X L s := by
  refine ⟨⟨zeroScheme X L s, inferInstance, ?_⟩, rfl⟩
  rw [Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
  have hcart := isEffectiveCartierDivisor_zeroScheme_of_ne_zero L s hs
  have hξ : closure ({genericPoint (zeroScheme X L s).subscheme} :
      Set (zeroScheme X L s).subscheme) = Set.univ := genericPoint_spec _
  have hdim1 := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor _ hcart
    (genericPoint (zeroScheme X L s).subscheme)
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩, hξ⟩
  rw [ringKrullDim_stalk_eq_coheight] at hdim1
  exact_mod_cast hdim1

/-- **Restriction points from the analytic restriction**: for the pinned uniformisation `Φ`,
every `v` with `φ v` in the range of the analytic restriction is a restriction point. -/
theorem isRestrictionPoint_of_mem_range_analyticRestrictionH1
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] {C : Scheme.{0}} (ι : C ⟶ X)
    [IsClosedImmersion ι] (hproj : IsProjective (ι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
    (e : analyticO (ι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ)))))
    (he : IsExpFormula (ι ≫ (X ↘ Spec (.of ℂ))) e) {JX : Grp (Over (Spec (.of ℂ)))}
    (eJ : haveI := hproj.isProper
      yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ)
    {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H (analyticO (ι ≫ (X ↘ Spec (.of ℂ)))) 1)
    (Φ : (Fin n → ℂ) → space JX.X.hom)
    (hΦ : haveI := hproj.isProper
      IsExpUniformisation _ hdim σ hσ eJ (expPicOf (ι ≫ (X ↘ Spec (.of ℂ))) e) φ Φ)
    (v : Fin n → ℂ)
    (hv : φ v ∈ Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl)) :
    haveI := hproj.isProper
    IsRestrictionPoint ι _ hdim σ hσ eJ (Φ v) := by
  haveI := hproj.isProper
  exact exists_schemePullbackClass_eq_of_mem_range ι _ hdim σ hσ eJ (expPicOf _ e) φ Φ hproj hΦ
    (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl)
    (fun w => exists_classOf_analytify_pullback_eq_expPic_analyticRestrictionH1 ι hproj e he w) v hv

section Rationality

/-- **Rationality from a countable closed cover.** Let `Φ : ℂⁿ → Y(ℂ)` be `Λ`-periodic for a full
lattice `Λ`, continuous, holomorphic in charts and biholomorphic near `0`. If `Φ` maps the complex
subspace `V` into countably many closed subsets of `Y` of dimension at most `dim V`, then `V` is
spanned over `ℝ` by the lattice points it contains. -/
theorem span_inter_eq_of_forall_mem_iUnion {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] {n : ℕ} {Φ : (Fin n → ℂ) → ComplexPoints sY}
    (Λ : Submodule ℤ (Fin n → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hcont : Continuous Φ)
    (hhol : ∀ (v : Fin n → ℂ) (c : Chart sY) (_ : Φ v ∈ chart c.U),
      ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
        ∀ᶠ v' in nhds v, ∃ h' : Φ v' ∈ chart c.U, c.coords ⟨Φ v', h'⟩ = F v')
    (hloc : ∃ U : Set (Fin n → ℂ), IsOpen U ∧ 0 ∈ U ∧
      ∃ W : Opens (space sY), Set.BijOn Φ U W ∧
        ∃ Ψ : space sY → (Fin n → ℂ), Set.LeftInvOn Ψ Φ U ∧
          ∀ (y : space sY) (_ : y ∈ W) (c : Chart sY) (hy : y ∈ ComplexPoints.chart c.U),
            ∃ G : (Fin c.n → ℂ) → (Fin n → ℂ), DifferentiableAt ℂ G (c.coords ⟨y, hy⟩) ∧
              ∀ᶠ y' in nhds y, ∀ hy' : y' ∈ ComplexPoints.chart c.U, y' ∈ W →
                Ψ y' = G (c.coords ⟨y', hy'⟩))
    (hper : ∀ x, ∀ μ ∈ Λ, Φ (x + μ) = Φ x) (V : Submodule ℂ (Fin n → ℂ)) {κ : Type}
    [Countable κ] (T : κ → Set Y) (hT : ∀ k, IsClosed (T k))
    (hTd : ∀ k, topologicalKrullDim (T k) ≤ Module.finrank ℂ V)
    (hcov : ∀ v ∈ V, (Φ v).toScheme ∈ ⋃ k, T k) :
    Submodule.span ℝ ((V : Set (Fin n → ℂ)) ∩ Λ) = V.restrictScalars ℝ := by
  have hcontV : Continuous fun v : V => Φ v := hcont.comp continuous_subtype_val
  obtain ⟨k, hk⟩ := exists_forall_mem_of_forall_mem_iUnion (N := V) hcontV
    (fun v c hv => by
      obtain ⟨F, hF, hev⟩ := hhol v c hv
      refine ⟨F ∘ V.subtype, hF.comp v (V.subtypeL.differentiableAt), ?_⟩
      exact (continuous_subtype_val.tendsto v).eventually hev)
    hT (fun v => hcov v v.2)
  obtain ⟨G, hVG, hΛG, ε, hε, hG⟩ := exists_addSubgroup_of_subset_isClosed_of_periodic Λ hcont
    hhol hloc hper V (hT k) (hTd k) (fun v hv => hk ⟨v, hv⟩)
  exact span_inter_eq_of_addSubgroup (W := V.restrictScalars ℝ) G hVG hΛG hε hG

/-- **Spanning through an injective linear map.** If `G : W → ℂⁿ` is `ℂ`-linear and injective
with range `V`, and `V` is spanned over `ℝ` by points of `V ∩ Λ` lying in `G(S)`, then `S` spans
`W` over `ℝ`. -/
theorem span_real_eq_top_of_injective {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (G : W →ₗ[ℂ] (Fin n → ℂ)) (hG : Function.Injective G) (S : Set W)
    (V : Submodule ℂ (Fin n → ℂ)) (hrange : LinearMap.range G = V) (Λ : Set (Fin n → ℂ))
    (hspan : Submodule.span ℝ ((V : Set (Fin n → ℂ)) ∩ Λ) = V.restrictScalars ℝ)
    (hsub : (V : Set (Fin n → ℂ)) ∩ Λ ⊆ G '' S) : Submodule.span ℝ S = ⊤ := by
  let Gr := G.restrictScalars ℝ
  have hGr : Function.Injective Gr := hG
  have hR : LinearMap.range Gr = V.restrictScalars ℝ := by
    ext v
    rw [← hrange]
    simp [Gr]
  refine Submodule.map_injective_of_injective hGr ?_
  rw [Submodule.map_top]
  refine le_antisymm LinearMap.map_le_range ?_
  rw [hR, ← hspan, Submodule.map_span]
  exact Submodule.span_mono hsub

end Rationality

/-- **The cover of `Φ(V)`.** For the pinned uniformisation `Φ` of the Jacobian of a curve
`ι : C ⟶ X` and the preimage `V` of the image of the analytic restriction, `Φ(V)` is covered by
countably many closed subsets of the Jacobian of dimension at most `dim V`. -/
theorem exists_cover_of_isExpUniformisation
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] {C : Scheme.{0}} (ι : C ⟶ X)
    [IsClosedImmersion ι] (hproj : IsProjective (ι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
    (e : analyticO (ι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ)))))
    (he : IsExpFormula (ι ≫ (X ↘ Spec (.of ℂ))) e) {JX : Grp (Over (Spec (.of ℂ)))}
    [LocallyOfFiniteType JX.X.hom]
    (eJ : haveI := hproj.isProper
      yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ)
    {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H (analyticO (ι ≫ (X ↘ Spec (.of ℂ)))) 1)
    (Φ : (Fin n → ℂ) → space JX.X.hom)
    (hΦ : haveI := hproj.isProper
      IsExpUniformisation _ hdim σ hσ eJ (expPicOf (ι ≫ (X ↘ Spec (.of ℂ))) e) φ Φ)
    (hadd : ∀ v v' : Fin n → ℂ,
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ (v + v')).1 (Φ (v + v')).2) =
        (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2) *
          (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v').1 (Φ v').2))
    (hsurj : Function.Surjective ((fun x : ComplexPoints JX.X.hom =>
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)) ∘ Φ))
    (hhol : ∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (_ : Φ v ∈ chart c.U),
      ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
        ∀ᶠ v' in nhds v, ∃ h' : Φ v' ∈ chart c.U, c.coords ⟨Φ v', h'⟩ = F v')
    (V : Submodule ℂ (Fin n → ℂ))
    (hV : (V : Set (Fin n → ℂ)) =
      φ ⁻¹' Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl)) :
    haveI := hproj.isProper
    ∃ (κ' : Type) (_ : Countable κ') (T' : κ' → Set JX.X.left), (∀ k, IsClosed (T' k)) ∧
      (∀ k, topologicalKrullDim (T' k) ≤ Module.finrank ℂ V) ∧
      ∀ v ∈ V, (Φ v).toScheme ∈ ⋃ k, T' k := by
  haveI := hproj.isProper
  have hsurjΦ : Function.Surjective Φ := fun x => by
    obtain ⟨v, hv⟩ := hsurj ((fun x : ComplexPoints JX.X.hom =>
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)) x)
    exact ⟨v, injective_cls _ hdim σ hσ eJ hv⟩
  have hR : ∀ v ∈ V, IsRestrictionPoint ι _ hdim σ hσ eJ (Φ v) := fun v hv =>
    isRestrictionPoint_of_mem_range_analyticRestrictionH1 ι hproj hdim σ hσ e he eJ φ Φ hΦ v
      (by
        have h : v ∈ (V : Set (Fin n → ℂ)) := hv
        rwa [hV] at h)
  exact exists_countable_isClosed_cover_of_restriction_pinned ι hproj hdim σ hσ e he
    (isExpNaturalRestriction ι e he) eJ φ Φ hΦ hadd hsurjΦ hhol V hV hR

/-- **The period kernel on the curve.** If the exponential of the restriction of
`w ∈ H¹(X^an, 𝒪)` to the curve `Z = P` vanishes, then `w` comes from `H¹(X^an, ℤ)`. -/
theorem mem_range_of_expPicOf_analyticRestrictionH1_eq_zero
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (Z : X.IdealSheafData)
    (hproj : IsProjective (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))]
    (P : Mori.PrimeDivisor X) (hP : P.idealSheaf = Z)
    (hC : ∀ D : Mori.Divisor X,
      (Mori.Divisor.toQDivisor D).IsNumericallyTrivial ℂ (X ↘ Spec (.of ℂ)) →
      (∃ h : (Finsupp.single P 1 - D : Mori.Divisor X).IsCartier,
        (Finsupp.single P 1 - D : Mori.Divisor X).IsAmple h) ∧
      (∃ h : (Finsupp.single P 1 + D : Mori.Divisor X).IsCartier,
        (Finsupp.single P 1 + D : Mori.Divisor X).IsAmple h))
    (e : analyticO (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf
        (analytification (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))))
    (he : IsExpFormula (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) e)
    (w : Sheaf.H (analyticO (X ↘ Spec (.of ℂ))) 1)
    (h0 : expPicOf (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) e
      (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) Z.subschemeι rfl w) =
        expPicOf (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) e 0) :
    w ∈ Set.range (Sheaf.H.map
      (MMP.Analytic.exists_shortExact_exponentialSequence (X ↘ Spec (.of ℂ))).choose 1) := by
  have hX : IsProjective (X ↘ Spec (.of ℂ)) :=
    (isProjectiveVariety_iff_isProjective ℂ _).mp inferInstance
  have heX := (MMP.Analytic.exists_shortExact_exponentialSequence
    (X ↘ Spec (.of ℂ))).choose_spec.choose_spec.choose_spec.2.2
  obtain ⟨LX, hLX, hLXan, hcl⟩ := exists_classOf_analytifyModule_eq _ hX
    (expPicOf (X ↘ Spec (.of ℂ))
      (MMP.Analytic.exists_shortExact_exponentialSequence (X ↘ Spec (.of ℂ))).choose_spec.choose w)
  have hM := Stacks.RingedSpace.modulePullback_isInvertible_of Z.subschemeι.toLRSHom.toShHom LX hLX
  have hLan := @Stacks.RingedSpace.isInvertible_modulePullback _ _
    (analytificationHom (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))) _ hM
  haveI := hproj.isProper
  have hres := isExpNaturalRestriction Z.subschemeι e he _ heX w LX hLX hLXan hLan hcl
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
    (analytification (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))))
  have htriv := nonempty_iso_unit_of_classOf_analytifyModule_eq_zero _ hproj _ hM hLan
    (hres.trans (h0.trans (map_zero _)))
  have hL : Nonempty ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj LX ≅
      SheafOfModules.unit P.idealSheaf.subscheme.ringCatSheaf) := by
    rwa [hP]
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 LX := hLX
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  have hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of ℂ)) := MMP.Flips.isSmoothScheme_of_smooth _
  have hn : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 2
  have hcl' : Stacks.SheafOfModules.Picard.classOf _ _ _ hLXan =
      Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup (analytification (X ↘ Spec (.of ℂ)))
        ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
          (space (X ↘ Spec (.of ℂ)))
          (Stacks.Cohomology.Generators.unitsSheaf (analytification (X ↘ Spec (.of ℂ)))))).symm
          (Sheaf.H.map (MMP.Analytic.exists_shortExact_exponentialSequence
            (X ↘ Spec (.of ℂ))).choose_spec.choose 1 w)) := hcl
  rw [← sheafCohomologyOneExtEquiv_analytification] at hcl'
  exact mem_range_map_one_of_pullback_iso_unit (X ↘ Spec (.of ℂ)) hsm hn le_rfl P hC LX hL hLXan w
    hcl'.symm

/-- **The image of `H¹(X^an, ℤ)` spans `H¹(X, 𝒪_X)` over `ℝ`**, from the rationality of `V`
(`span_ℝ (V ∩ Λ) = V`), the period kernel and injectivity of the restriction to the curve. -/
theorem span_real_range_sheafH_map_eq_top
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (Z : X.IdealSheafData)
    (hproj : IsProjective (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))]
    (hinj : Function.Injective
      (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) Z.subschemeι rfl))
    (P : Mori.PrimeDivisor X) (hP : P.idealSheaf = Z)
    (hC : ∀ D : Mori.Divisor X,
      (Mori.Divisor.toQDivisor D).IsNumericallyTrivial ℂ (X ↘ Spec (.of ℂ)) →
      (∃ h : (Finsupp.single P 1 - D : Mori.Divisor X).IsCartier,
        (Finsupp.single P 1 - D : Mori.Divisor X).IsAmple h) ∧
      (∃ h : (Finsupp.single P 1 + D : Mori.Divisor X).IsCartier,
        (Finsupp.single P 1 + D : Mori.Divisor X).IsAmple h))
    (e : analyticO (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf
        (analytification (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))))
    (he : IsExpFormula (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) e) {n : ℕ}
    (φ : (Fin n → ℂ) ≃+ Sheaf.H (analyticO (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))) 1)
    (hφ : ∀ (a : ℂ) (v : Fin n → ℂ),
      φ (a • v) = Sheaf.H.map (smulConst (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) a) 1 (φ v))
    (Λ : Set (Fin n → ℂ))
    (hΛ : ∀ v ∈ Λ, expPicOf (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) e (φ v) =
      expPicOf (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) e 0)
    (V : Submodule ℂ (Fin n → ℂ))
    (hV : (V : Set (Fin n → ℂ)) =
      φ ⁻¹' Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) Z.subschemeι rfl))
    (hspanV : Submodule.span ℝ ((V : Set (Fin n → ℂ)) ∩ Λ) = V.restrictScalars ℝ)
    (E : Sheaf.H (analyticO (X ↘ Spec (.of ℂ))) 1 ≃+
      cohomologyOverField ℂ (X ↘ Spec (.of ℂ)) (SheafOfModules.unit X.ringCatSheaf) 1)
    (hE : ∀ a x, E (Sheaf.H.map (smulConst (X ↘ Spec (.of ℂ)) a) 1 x) = a • E x) :
    Submodule.span ℝ (Set.range fun x => E (Sheaf.H.map
      (MMP.Analytic.exists_shortExact_exponentialSequence (X ↘ Spec (.of ℂ))).choose 1 x)) = ⊤ := by
  set res := analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) Z.subschemeι rfl with hres
  let G : cohomologyOverField ℂ (X ↘ Spec (.of ℂ)) (SheafOfModules.unit X.ringCatSheaf) 1 →ₗ[ℂ]
      (Fin n → ℂ) :=
    { toFun := fun y => φ.symm (res (E.symm y))
      map_add' := fun y y' => by simp only [map_add]
      map_smul' := fun a y => by
        have h1 : E.symm (a • y) = Sheaf.H.map (smulConst (X ↘ Spec (.of ℂ)) a) 1 (E.symm y) := by
          apply E.injective
          rw [hE, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
        simp only [RingHom.id_apply]
        rw [h1, hres, analyticRestrictionH1_smulConst Z.subschemeι rfl _ (isSmulConst_smulConst _)
          _ (isSmulConst_smulConst _), ← hres]
        apply φ.injective
        rw [AddEquiv.apply_symm_apply, hφ, AddEquiv.apply_symm_apply] }
  have hG : Function.Injective G := fun y y' h => E.symm.injective (hinj (φ.symm.injective h))
  have hrange : LinearMap.range G = V := by
    ext v
    rw [LinearMap.mem_range, ← SetLike.mem_coe, hV, Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨E.symm y, (AddEquiv.apply_symm_apply φ _).symm⟩
    · rintro ⟨w, hw⟩
      refine ⟨E w, ?_⟩
      change φ.symm (res (E.symm (E w))) = v
      rw [AddEquiv.symm_apply_apply, hw, AddEquiv.symm_apply_apply]
  refine span_real_eq_top_of_injective G hG _ V hrange Λ hspanV ?_
  rintro v ⟨hvV, hvΛ⟩
  have hvV' : v ∈ (V : Set (Fin n → ℂ)) := hvV
  rw [hV] at hvV'
  obtain ⟨w, hw⟩ := hvV'
  obtain ⟨x, hx⟩ := mem_range_of_expPicOf_analyticRestrictionH1_eq_zero Z hproj P hP hC e he w
    (by
      rw [← hres, hw]
      exact hΛ v hvΛ)
  refine ⟨E (Sheaf.H.map _ 1 x), ⟨x, rfl⟩, ?_⟩
  change φ.symm (res (E.symm (E _))) = v
  rw [AddEquiv.symm_apply_apply, hx, hw, AddEquiv.symm_apply_apply]

/-- **The subspace `V` and its rationality.** For the pinned uniformisation `Φ` of the Jacobian
of a curve `ι : C ⟶ X` on a smooth projective surface, with period lattice `Λ`, the preimage `V`
under `φ` of the image of `H¹(X^an, 𝒪)` is a complex subspace spanned over `ℝ` by `V ∩ Λ`. -/
theorem exists_submodule_span_inter_eq
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] {C : Scheme.{0}} (ι : C ⟶ X)
    [IsClosedImmersion ι] (hproj : IsProjective (ι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _)
    (e : analyticO (ι ≫ (X ↘ Spec (.of ℂ))) ⟶
      Stacks.Cohomology.Generators.unitsSheaf (analytification (ι ≫ (X ↘ Spec (.of ℂ)))))
    (he : IsExpFormula (ι ≫ (X ↘ Spec (.of ℂ))) e) {JX : Grp (Over (Spec (.of ℂ)))}
    [LocallyOfFiniteType JX.X.hom]
    (eJ : haveI := hproj.isProper
      yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ)
    {n : ℕ} (φ : (Fin n → ℂ) ≃+ Sheaf.H (analyticO (ι ≫ (X ↘ Spec (.of ℂ)))) 1)
    (hφ : ∀ (a : ℂ) (v : Fin n → ℂ),
      φ (a • v) = Sheaf.H.map (smulConst (ι ≫ (X ↘ Spec (.of ℂ))) a) 1 (φ v))
    (Λ : Submodule ℤ (Fin n → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (Φ : (Fin n → ℂ) → space JX.X.hom) (hcont : Continuous Φ)
    (hhol : ∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (_ : Φ v ∈ chart c.U),
      ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
        ∀ᶠ v' in nhds v, ∃ h' : Φ v' ∈ chart c.U, c.coords ⟨Φ v', h'⟩ = F v')
    (hloc : ∃ U : Set (Fin n → ℂ), IsOpen U ∧ 0 ∈ U ∧
      ∃ W : Opens (space JX.X.hom), Set.BijOn Φ U W ∧
        ∃ Ψ : space JX.X.hom → (Fin n → ℂ), Set.LeftInvOn Ψ Φ U ∧
          ∀ (y : space JX.X.hom) (_ : y ∈ W) (c : Chart JX.X.hom)
            (hy : y ∈ ComplexPoints.chart c.U),
            ∃ G : (Fin c.n → ℂ) → (Fin n → ℂ), DifferentiableAt ℂ G (c.coords ⟨y, hy⟩) ∧
              ∀ᶠ y' in nhds y, ∀ hy' : y' ∈ ComplexPoints.chart c.U, y' ∈ W →
                Ψ y' = G (c.coords ⟨y', hy'⟩))
    (hadd : ∀ v v' : Fin n → ℂ,
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ (v + v')).1 (Φ (v + v')).2) =
        (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2) *
          (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v').1 (Φ v').2))
    (hker : ∀ v : Fin n → ℂ,
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk (Φ v).1 (Φ v).2) = 1 ↔ v ∈ Λ)
    (hsurj : Function.Surjective ((fun x : ComplexPoints JX.X.hom =>
      (eJ.hom.app (op (Over.mk (𝟙 _)))).hom (Over.homMk x.1 x.2)) ∘ Φ))
    (hΦ : haveI := hproj.isProper
      IsExpUniformisation _ hdim σ hσ eJ (expPicOf (ι ≫ (X ↘ Spec (.of ℂ))) e) φ Φ) :
    ∃ V : Submodule ℂ (Fin n → ℂ), (V : Set (Fin n → ℂ)) =
        φ ⁻¹' Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl) ∧
      Submodule.span ℝ ((V : Set (Fin n → ℂ)) ∩ Λ) = V.restrictScalars ℝ := by
  haveI := hproj.isProper
  obtain ⟨V, hV⟩ : ∃ V : Submodule ℂ (Fin n → ℂ), (V : Set (Fin n → ℂ)) =
      φ ⁻¹' Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl) :=
    ⟨{ carrier := φ ⁻¹' Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) ι rfl)
       add_mem' := fun {a b} ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by rw [map_add, hx, hy, map_add]⟩
       zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
       smul_mem' := fun c {v} ⟨w, hw⟩ => ⟨Sheaf.H.map (smulConst (X ↘ Spec (.of ℂ)) c) 1 w, by
         rw [analyticRestrictionH1_smulConst ι rfl _ (isSmulConst_smulConst _)
           _ (isSmulConst_smulConst _), hw]
         exact (hφ c v).symm⟩ }, rfl⟩
  obtain ⟨κ', hκ', T', hT', hdT', hcov⟩ := exists_cover_of_isExpUniformisation ι
    hproj hdim σ hσ e he eJ φ Φ hΦ hadd hsurj hhol V hV
  haveI := hκ'
  exact ⟨V, hV, span_inter_eq_of_forall_mem_iUnion Λ hcont hhol hloc
    (fun x μ hμ => map_add_eq_of_mem (injective_cls _ hdim σ hσ eJ) hadd hker x hμ) V T' hT'
    hdT' hcov⟩

/-- **Rationality of the restricted `H¹(𝒪)`.** For a smooth projective connected curve `Z` on a
smooth projective surface `X`, there are the exponential `e` of `Z^an`, `ℂ`-linear coordinates
`φ : ℂⁿ ≃ H¹(Z^an, 𝒪)`, a set `Λ ⊆ ℂⁿ` of periods (`exp ∘ φ` vanishes on `Λ`) and the preimage
`V` of the image of `H¹(X^an, 𝒪)`, with `V` spanned over `ℝ` by `V ∩ Λ`. -/
theorem exists_span_inter_eq_of_curve
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] (Z : X.IdealSheafData)
    [ConnectedSpace Z.subscheme] (hproj : IsProjective (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))] :
    ∃ (e : analyticO (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) ⟶
        Stacks.Cohomology.Generators.unitsSheaf
          (analytification (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))))
      (_ : IsExpFormula (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) e) (n : ℕ)
      (φ : (Fin n → ℂ) ≃+ Sheaf.H (analyticO (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))) 1),
      (∀ (a : ℂ) (v : Fin n → ℂ),
        φ (a • v) = Sheaf.H.map (smulConst (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) a) 1 (φ v)) ∧
      ∃ Λ : Set (Fin n → ℂ), (∀ v ∈ Λ, expPicOf (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) e (φ v) =
          expPicOf (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) e 0) ∧
        ∃ V : Submodule ℂ (Fin n → ℂ), (V : Set (Fin n → ℂ)) =
            φ ⁻¹' Set.range (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) Z.subschemeι rfl) ∧
          Submodule.span ℝ ((V : Set (Fin n → ℂ)) ∩ Λ) = V.restrictScalars ℝ := by
  haveI := hproj.isProper
  obtain ⟨hdim, σ, hσ⟩ := fiber_dim_le_one_and_exists_section _ hproj
  obtain ⟨iC, eC, wC, -, hiC, heC⟩ :=
    MMP.Analytic.exists_shortExact_exponentialSequence (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))
  obtain ⟨hSC, n, φ, hφ, hdisc, hlat, hker, -, hJ⟩ :=
    exists_isZLattice_exponential_pinned_of_isProjective _ hproj hdim
      σ hσ iC eC wC hiC heC (smulConst _) (isSmulConst_smulConst _)
  obtain ⟨J0, e0, hab, -⟩ := MMP.Conductor.exists_jacobian_of_isProjective _ hproj hdim σ hσ
  haveI : IsProper J0.X.hom := hab.toIsProperVariety.toIsProper
  obtain ⟨Φ, hcont, hhol, hloc, hadd, hker', hsurj, hexp⟩ := hJ J0 e0
  haveI : LocallyOfFiniteType J0.X.hom := inferInstance
  haveI := hdisc
  haveI := hlat
  obtain ⟨V, hV, hspanV⟩ := exists_submodule_span_inter_eq Z.subschemeι hproj hdim σ hσ eC heC
    e0 φ hφ ((Sheaf.H.map iC 1).range.comap φ.toAddMonoidHom).toIntSubmodule Φ hcont hhol hloc
    hadd hker' hsurj hexp
  refine ⟨eC, heC, n, φ, hφ, _, fun v hv => ?_, V, hV, hspanV⟩
  letI := Stacks.Cohomology.Generators.picardGroupAddCommGroup
    (analytification (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))))
  have h : v ∈ ((expPicOf (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) eC).comp
      φ.toAddMonoidHom).ker := by
    rw [hker]
    exact hv
  exact h.trans (map_zero _).symm

/-- **`b₁ = h⁰(Ω¹) + h¹(𝒪)`** for a smooth projective complex variety. -/
theorem finrank_analyticSingularCohomology_one_eq {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsProjectiveVariety ℂ sX] [Smooth sX] :
    Module.finrank ℂ (analyticSingularCohomology ℂ sX 1) =
      Module.finrank ℂ (cohomologyOverField ℂ sX (Scheme.Hom.relativeDifferentials sX) 0) +
        Module.finrank ℂ (cohomologyOverField ℂ sX (SheafOfModules.unit X.ringCatSheaf) 1) := by
  obtain ⟨-, -, h⟩ := exists_deRhamCohomology_linearEquiv_singularCohomology
  exact (h X sX (MMP.Flips.isSmoothScheme_of_smooth sX)).1

/-- **`2 h¹(𝒪_X) ≤ b₁` from a curve.** Let `X` be a smooth projective surface over `ℂ` and
`Z ⊂ X` a smooth projective connected curve, which is the prime divisor `P`, such that the
restriction `H¹(X^an, 𝒪) → H¹(Z^an, 𝒪)` is injective and `P ± D` is ample for every numerically
trivial divisor `D`. Then `2 h¹(𝒪_X) ≤ b₁(X)`. -/
theorem two_mul_finrank_cohomologyOverField_unit_one_le_of_curve
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (Z : X.IdealSheafData) [ConnectedSpace Z.subscheme]
    (hproj : IsProjective (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (Z.subschemeι ≫ (X ↘ Spec (.of ℂ)))]
    (hinj : Function.Injective
      (analyticRestrictionH1 (sX := X ↘ Spec (.of ℂ)) Z.subschemeι rfl))
    (P : Mori.PrimeDivisor X) (hP : P.idealSheaf = Z)
    (hC : ∀ D : Mori.Divisor X,
      (Mori.Divisor.toQDivisor D).IsNumericallyTrivial ℂ (X ↘ Spec (.of ℂ)) →
      (∃ h : (Finsupp.single P 1 - D : Mori.Divisor X).IsCartier,
        (Finsupp.single P 1 - D : Mori.Divisor X).IsAmple h) ∧
      (∃ h : (Finsupp.single P 1 + D : Mori.Divisor X).IsCartier,
        (Finsupp.single P 1 + D : Mori.Divisor X).IsAmple h)) :
    2 * Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (SheafOfModules.unit X.ringCatSheaf) 1) ≤
      Module.finrank ℂ (analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1) := by
  obtain ⟨e, he, n, φ, hφ, Λ, hΛ, V, hV, hspanV⟩ := exists_span_inter_eq_of_curve Z hproj
  have hX : IsProjective (X ↘ Spec (.of ℂ)) :=
    (isProjectiveVariety_iff_isProjective ℂ _).mp inferInstance
  obtain ⟨E, hE⟩ := MMP.JacobianLogarithm.exists_addEquiv_H1 _ hX (smulConst _)
    (isSmulConst_smulConst _)
  exact two_mul_finrank_cohomologyOverField_unit_one_le _ E.toAddMonoidHom
    (span_real_range_sheafH_map_eq_top Z hproj hinj P hP hC e he φ hφ Λ hΛ V hV hspanV E hE)

section Numerical

variable
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
  [Smooth (X ↘ Spec (.of ℂ))] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- On a smooth projective variety the negative of a numerically trivial divisor is numerically
trivial. -/
theorem isNumericallyTrivial_toQDivisor_neg (D : Mori.Divisor X)
    (hD : (Mori.Divisor.toQDivisor D).IsNumericallyTrivial ℂ (X ↘ Spec (.of ℂ))) :
    (Mori.Divisor.toQDivisor (-D)).IsNumericallyTrivial ℂ (X ↘ Spec (.of ℂ)) := by
  have hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of ℂ)) := MMP.Flips.isSmoothScheme_of_smooth _
  obtain ⟨hDq, h0⟩ := (Mori.QDivisor.isNumericallyTrivial_iff _).1 hD
  have hnq := Mori.QDivisor.isQCartier_toQDivisor
    (MMP.Fourfold.isCartier_of_isSmoothScheme hsm (-D))
  refine (Mori.QDivisor.isNumericallyTrivial_iff _).2 ⟨hnq, fun C i _ _ _ hC => ?_⟩
  have hsum := hnq.add hDq
  have h1 := Mori.QDivisor.intersectionNumber_add' ℂ (X ↘ Spec (.of ℂ)) i hC.le _ _ hnq hDq hsum
  have h2 : ∀ (Q : Mori.QDivisor X) (hQ : Q.IsQCartier), Q = 0 →
      Q.intersectionNumber ℂ (X ↘ Spec (.of ℂ)) i hC.le hQ = 0 := by
    rintro Q hQ rfl
    exact ((Mori.QDivisor.isNumericallyTrivial_iff 0).1
      (Mori.QDivisor.NumericallyEquivalent.refl Mori.QDivisor.isQCartier_zero)).2 C i hC
  rw [h2 _ hsum (by rw [← map_add, neg_add_cancel, map_zero]), h0 C i hC, add_zero] at h1
  exact h1.symm

/-- **Ampleness is numerical**: an ample divisor plus a numerically trivial one is ample. -/
theorem isAmple_add_of_isNumericallyTrivial (A D : Mori.Divisor X) (hA : A.IsCartier)
    (hAamp : A.IsAmple hA)
    (hD : (Mori.Divisor.toQDivisor D).IsNumericallyTrivial ℂ (X ↘ Spec (.of ℂ))) :
    ∃ h : (A + D).IsCartier, (A + D).IsAmple h := by
  have hsm : MMP.Mori.IsSmoothScheme (X ↘ Spec (.of ℂ)) := MMP.Flips.isSmoothScheme_of_smooth _
  have hDc := MMP.Fourfold.isCartier_of_isSmoothScheme hsm D
  obtain ⟨hDq, h0⟩ := (Mori.QDivisor.isNumericallyTrivial_iff _).1 hD
  exact ⟨hA.add hDc, Mori.QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef
    (X ↘ Spec (.of ℂ)) ⟨1, one_pos, A, by rw [Nat.cast_one, one_smul], hA, hAamp⟩
    ⟨hDq, fun C i _ _ _ hC => (h0 C i hC).ge⟩
    (Mori.QDivisor.NumericallyEquivalent.refl
      ((Mori.QDivisor.isQCartier_toQDivisor hA).add hDq))
    1 one_pos (A + D) (by rw [Nat.cast_one, one_smul, map_add]) _⟩

/-- If `A` is ample, `A - D` and `A + D` are ample for every numerically trivial `D`. -/
theorem isAmple_sub_and_add_of_isNumericallyTrivial (A : Mori.Divisor X) (hA : A.IsCartier)
    (hAamp : A.IsAmple hA) (D : Mori.Divisor X)
    (hD : (Mori.Divisor.toQDivisor D).IsNumericallyTrivial ℂ (X ↘ Spec (.of ℂ))) :
    (∃ h : (A - D).IsCartier, (A - D).IsAmple h) ∧ (∃ h : (A + D).IsCartier, (A + D).IsAmple h) :=
  ⟨sub_eq_add_neg A D ▸ isAmple_add_of_isNumericallyTrivial A (-D) hA hAamp
    (isNumericallyTrivial_toQDivisor_neg D hD),
    isAmple_add_of_isNumericallyTrivial A D hA hAamp hD⟩

end Numerical

/-- **Hodge symmetry in degree one for surfaces, given (B).** For a smooth projective surface `X`
over `ℂ`, `h¹(X, 𝒪_X) ≤ h⁰(X, Ω¹_X)`, given that the smooth zero scheme of a section of a very
ample line bundle is an ample prime divisor (`ZeroSchemePrimeDivisorAmple`). -/
theorem finrank_cohomologyOverField_unit_one_le_of_surface_of (HB : ZeroSchemePrimeDivisorAmple)
    {n : ℕ}
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))] (h2 : n = 2) :
    Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (SheafOfModules.unit X.ringCatSheaf) 1) ≤
      Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (Scheme.Hom.relativeDifferentials (X ↘ Spec (.of ℂ))) 0) := by
  subst h2
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  have hVar : IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hVar.toIsIntegral
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  haveI : IsNormal X := isNormal_of_smooth_over_field (X ↘ Spec (.of ℂ))
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  obtain ⟨A, hA⟩ := exists_isVeryAmpleDivisor_of_isProjectiveVariety (k := ℂ) (X := X)
  obtain ⟨s, hs0, hconn, hint, hsm, hpm, hinjalg, -⟩ :=
    exists_smooth_connected_zeroScheme_of_isVeryAmpleDivisor (k := ℂ) (n := 2) le_rfl A hA
  letI := MMP.CartierDivisor.isInvertibleModule_sheaf A
  haveI := hconn
  haveI := hint
  haveI : SmoothOfRelativeDimension 1
      ((zeroScheme X (MMP.CartierDivisor.sheaf A) s).subschemeι ≫ (X ↘ Spec (.of ℂ))) := hsm
  have hinj := injective_analyticRestrictionH1_zeroScheme_of_injective (X ↘ Spec (.of ℂ))
    (nX := 2) (nZ := 1) (MMP.CartierDivisor.sheaf A) s hinjalg
  have hproj : IsProjective
      ((zeroScheme X (MMP.CartierDivisor.sheaf A) s).subschemeι ≫ (X ↘ Spec (.of ℂ))) :=
    (isProjective_iff_isProjectiveMorphism_of_isAffine _).2 hpm
  obtain ⟨P, hP⟩ := exists_primeDivisor_idealSheaf_eq_zeroScheme (MMP.CartierDivisor.sheaf A) s hs0
  obtain ⟨hPc, hPamp⟩ := HB A hA s P hP
  have h := two_mul_finrank_cohomologyOverField_unit_one_le_of_curve _ hproj hinj P hP
    (isAmple_sub_and_add_of_isNumericallyTrivial _ hPc hPamp)
  have hb := finrank_analyticSingularCohomology_one_eq (X ↘ Spec (.of ℂ))
  omega

end MMP.Analytic.SurfaceHodge

namespace MMP.Analytic

/-- **Hodge symmetry in degree one for surfaces.** For a smooth projective surface `X` over `ℂ`,
`h¹(X, 𝒪_X) ≤ h⁰(X, Ω¹_X)`. -/
theorem finrank_cohomologyOverField_unit_one_le_of_surface
    {n : ℕ} {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))] (h2 : n = 2) :
    Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (SheafOfModules.unit X.ringCatSheaf) 1) ≤
      Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (Scheme.Hom.relativeDifferentials (X ↘ Spec (.of ℂ))) 0) :=
  SurfaceHodge.finrank_cohomologyOverField_unit_one_le_of_surface_of
    SurfaceHodge.zeroSchemePrimeDivisorAmple h2

end MMP.Analytic
