module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
public import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import MMP.AlgebraicGeometry.Intersection.ChowFormCurveFamily
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
public import StacksFrontier.AlgebraicGeometry.Curves.SingularGenusZero
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.UnitBranchGlobalEquation

/-!
# The Chow variety of curves of fixed degree

Existence of the reduced projective parameter scheme `𝒞_d(X)` of effective degree-`d` curve
cycles on a projective `X ⊆ ℙᴺ_k`, with its family, incidence and degree properties.

The scheme is the closed locus of Chow forms in the projective space of bihomogeneous forms of
bidegree `(d, d)`: a form is the Chow form of an effective cycle `∑ n_C C` exactly when it is
associated to `∏ Ch_C^{n_C}`, where `Ch_C` is the incidence form of the curve `C`.

## Main results

* `MMP.Chow.exists_chowVariety`: the Chow variety of degree-`d` curve cycles on `X` exists.

## Implementation notes

The locus of Chow forms is shown to be closed directly, without a Hilbert scheme: a form whose
zeros all come from hyperplane pairs meeting its vertex locus on `X` is a Chow form, and failing
this is an open condition at closed points.

The degree of a Cartier divisor on the Chow cycle is shown to be constant on each connected
component through normal curves `Γ` mapping to the locus. Near a closed point the form over the
discrete valuation ring of `Γ` factors as a unit times `∏ⱼ Pⱼ^{nⱼ}` with `Pⱼ` prime, and the
cycle splits accordingly as `∑ⱼ nⱼ Z⁽ʲ⁾`. For each prime factor an irreducible component of the
support incidence is flat over `Γ`, and its fibre cycles are a fixed multiple of `Z⁽ʲ⁾`; their
degrees are constant because they are differences of Euler characteristics of the fibres.

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3–I.4
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart MMP

universe u

namespace MMP.Chow.FixedDegreeCurveCyclesProof

section IncidenceFormBidegree

open MMP.Chow.DeterminantCurveForm MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {N : ℕ}

/-- Every proper curve `C ⊆ ℙᴺ_k` has an irreducible incidence form, whose monomials all have
bidegree `(deg C, deg C)`. -/
private theorem exists_incForm_bidegree (C : Mori.ProperCurve (projToSpecCoeff k N)) :
    ∃ (G : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) (n : ℕ), IncForm C G ∧
      (n : ℤ) = curveDeg C ∧
      ∀ e ∈ G.support, (∑ j, e (Sum.inl j)) = n ∧ (∑ j, e (Sum.inr j)) = n := by
  classical
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  obtain ⟨G, hG⟩ := exists_incForm C
  let sS : Spec (.of k) ⟶ Spec (.of k) := 𝟙 _
  let sY := projToSpecCoeff k N
  let g₀ : AlgebraicGeometry.Proj (polyGrading k N) ⟶ AlgebraicGeometry.Proj (polyGrading k N) :=
    𝟙 _
  let π : C.scheme ⟶ Spec (.of k) := C.ι ≫ sY
  let q : C.scheme ⟶ AlgebraicGeometry.Proj (polyGrading k N) := C.ι
  have hS : Mori.IsNormalVariety k sS := isNormalVariety_id_spec
  have hY : IsProjectiveMorphism sY := isProjectiveMorphism_projToSpecCoeff
  have hg : IsProjectiveMorphism g₀ := isProjectiveMorphism_id _
  have hgY : g₀ ≫ projToSpecCoeff k N = sY := Category.id_comp _
  have hπq : π ≫ sS = q ≫ sY := Category.comp_id _
  haveI : IsClosedImmersion (pullback.lift π q hπq) := by
    have : pullback.lift π q hπq = q ≫ inv (pullback.snd sS sY) := by
      rw [IsIso.eq_comp_inv, pullback.lift_snd]
    rw [this]
    infer_instance
  haveI : IsProper π := C.isProper_ι_comp
  haveI : Flat π := inferInstance
  have hfib : ∀ t, IsIso (π.fiberι t) := fun t => isIso_fiberι_spec π t
  have hdim : ∀ t : Spec (.of k), IsClosed ({t} : Set _) → topologicalKrullDim (π.fiber t) = 1 := by
    intro t _
    haveI := hfib t
    rw [← C.dim_eq]
    exact IsHomeomorph.topologicalKrullDim_eq _ (π.fiberι t).homeomorph.isHomeomorph
  have hcyc : ∀ t : Spec (.of k), cyc g₀ sS π q t = Finsupp.single C 1 := by
    intro t
    haveI := hfib t
    have h1 := cycleOf_iso (asIso (π.fiberι t)) (π.fiberι t ≫ π ≫ sS) π (projToSpecCoeff k N)
      (C.ι ≫ g₀) (by rw [asIso_hom]; exact (Category.comp_id _).symm)
    have h2 : cyc g₀ sS π q t = cycleOf (π.fiberι t ≫ π ≫ sS) (projToSpecCoeff k N)
        ((asIso (π.fiberι t)).hom ≫ C.ι ≫ g₀) := rfl
    rw [h2, h1, show C.ι ≫ g₀ = C.ι from Category.comp_id _]
    exact finsum_cyclePushforwardOfPoint_self C
  set d := (curveDeg C).toNat with hd_def
  have hdC : (d : ℤ) = curveDeg C := Int.toNat_of_nonneg (curveDeg_pos C).le
  have hd : 0 < d := by have := curveDeg_pos C; omega
  have hdeg : ∀ t : Spec (.of k), IsClosed ({t} : Set _) →
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (cyc g₀ sS π q t) = d := by
    intro t _
    rw [hcyc]
    refine (Mori.OneCycle.degree_apply ℤ _ _ _).trans ?_
    rw [Finsupp.sum_single_index (by simp), one_mul, hdC]
    rfl
  obtain ⟨φ, hφ, -⟩ := MMP.Chow.exists_chowFormMorphism sS sY hS hY g₀ hg hgY π q hπq hdim d hd
    hdeg
  obtain ⟨-, hP⟩ := (hφ φ).mpr rfl
  let s₀ : Spec (.of k) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hP' := (hP s₀ (isClosed_singleton_spec s₀) (fun _ => G) (fun C' hC' => by
    have hC'' : C' ∈ (Finsupp.single C (1 : ℤ)).support := by
      have := hcyc s₀
      change C' ∈ (cyc g₀ sS π q s₀).support at hC'
      rwa [this] at hC'
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hC''
    subst hC''
    exact hG)).1
  refine ⟨G, d, hG, hdC, fun e he => hP' e ?_⟩
  change e ∈ (∏ C' ∈ (cyc g₀ sS π q s₀).support, G ^ (cyc g₀ sS π q s₀ C').toNat).support
  rw [hcyc s₀, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.prod_singleton,
    Finsupp.single_eq_same]
  simpa using he

end IncidenceFormBidegree

section ProjSpaceReindex

open MMP.Intersection

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem renameGradedHom_comp_symm (R : Type u) [CommRing R] {σ τ : Type u} (e : σ ≃ τ) :
    (renameGradedHom R e).comp (renameGradedHom R e.symm) = GradedRingHom.id _ := by
  rw [renameGradedHom_comp]
  simpa using renameGradedHom_id R

/-- Projective space `ℙ^σ_R ≅ ℙ^τ_R` for a bijection `e : σ ≃ τ` of the coordinate indices,
induced by renaming the variables. -/
private noncomputable def projSpaceCongr (R : Type u) [CommRing R] {σ τ : Type u} (e : σ ≃ τ) :
    ProjSpace R σ ≅ ProjSpace R τ where
  hom := Proj.map (renameGradedHom R e.symm)
    (Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse _ _
      (renameGradedHom_comp_symm R e.symm))
  inv := Proj.map (renameGradedHom R e)
    (Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse _ _
      (renameGradedHom_comp_symm R e))
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact (projMap_congr _ _ _ _
      (by simpa using renameGradedHom_comp_symm R e.symm)).trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact (projMap_congr _ _ _ _ (renameGradedHom_comp_symm R e)).trans Proj.map_id

/-- The renaming isomorphism `projSpaceCongr` lies over `Spec k`. -/
private theorem projSpaceCongr_hom_toSpec (k : Type u) [Field k] {σ τ : Type u} (e : σ ≃ τ) :
    (projSpaceCongr k e).hom ≫ ProjSpace.toSpec k τ = ProjSpace.toSpec k σ := by
  simp only [projSpaceCongr, ProjSpace.toSpec, Proj.map_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 3
  refine RingHom.ext fun a => Subtype.ext ?_
  simp [GradedRingHom.gradedZeroRingHom, MvPolynomial.rename_C]

/-- A closed subscheme of a projective space `ℙ^ι_k` with finitely many coordinates is
projective over `k`. -/
private theorem isProjectiveMorphism_comp_toSpec (k : Type u) [Field k] {ι : Type u} [Finite ι]
    [Nonempty ι] {Z : Scheme.{u}} (j : Z ⟶ ProjSpace k ι) [IsClosedImmersion j] :
    IsProjectiveMorphism (j ≫ ProjSpace.toSpec k ι) := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card ι = n + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Nat.card_pos.ne'
  let e : ι ≃ ULift.{u} (Fin (n + 1)) := (Finite.equivFinOfCardEq hn).trans Equiv.ulift.symm
  refine ⟨n, j ≫ (projSpaceCongr k e).hom ≫ (ProjSpace.isoProjectiveSpaceOver k n).hom,
    inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, ProjSpace.isoProjectiveSpaceOver_hom_over,
    projSpaceCongr_hom_toSpec]

/-- The renaming isomorphism `ℙ^{ULift (Fin (n + 1))}_k ≅ Proj k[T₀, …, Tₙ]` lies over
`Spec k`. -/
public theorem isoPolyGrading_inv_comp_toSpec (k : Type u) [Field k] (n : ℕ) :
    (ProjSpace.isoPolyGrading k n).inv ≫ ProjSpace.toSpec k (ULift.{u} (Fin (n + 1))) =
      projToSpecCoeff k n := by
  change AlgebraicGeometry.Proj.map _ _ ≫ _ = _
  unfold ProjSpace.toSpec projToSpecCoeff
  rw [AlgebraicGeometry.Proj.map_toSpecZero_assoc, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  apply Subtype.ext
  have h : (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) k) ∈ polyGrading k n 0 :=
    MvPolynomial.isHomogeneous_C _ r
  simp [renameGradedHom_apply, DirectSum.decompose_of_mem_same _ h]

/-- A closed subscheme of `ℙᴺ_k = Proj k[T₀, …, T_N]` is projective over `k`. -/
private theorem isProjectiveMorphism_comp_projToSpecCoeff (k : Type u) [Field k] {N : ℕ}
    {Z : Scheme.{u}} (j : Z ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion j] :
    IsProjectiveMorphism (j ≫ projToSpecCoeff k N) := by
  have := isProjectiveMorphism_comp_toSpec k (j ≫ (ProjSpace.isoPolyGrading k N).inv)
  rwa [Category.assoc, isoPolyGrading_inv_comp_toSpec] at this

end ProjSpaceReindex

/-- The kernel of a quasi-compact morphism `f : X ⟶ Y` from a reduced scheme is the vanishing
ideal of the closure of its image. -/
private theorem ker_eq_vanishingIdeal_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X]
    [QuasiCompact f] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range f), isClosed_closure⟩ := by
  have hrad : f.ker.radical = f.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.mpr (IsReduced.eq_zero _ ⟨n, hn⟩)
  rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  exact TopologicalSpace.Closeds.ext (Scheme.Hom.support_ker f)

/-- For a quasi-compact morphism `f : X ⟶ Y` from a reduced scheme, the vanishing ideal of any
closed set containing the image of `f` lies in the kernel of `f`. -/
public theorem vanishingIdeal_le_ker_of_isReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X]
    [QuasiCompact f] (Z : TopologicalSpace.Closeds Y) (h : Set.range f ⊆ Z) :
    Scheme.IdealSheafData.vanishingIdeal Z ≤ f.ker := by
  rw [ker_eq_vanishingIdeal_closure_range]
  exact Scheme.IdealSheafData.vanishingIdeal_antimono (Z.isClosed.closure_subset_iff.mpr h)

/-- A quasi-compact morphism from a reduced scheme whose underlying space is Jacobson (for
instance a reduced scheme of finite type over a field), sending every closed point into a closed
set `Z`, factors through the reduced induced closed subscheme on `Z`. -/
private theorem exists_comp_subschemeι_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X]
    [QuasiCompact f] [JacobsonSpace X] (Z : TopologicalSpace.Closeds Y)
    (h : ∀ x : X, IsClosed ({x} : Set X) → f x ∈ Z) :
    ∃ g : X ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      g ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = f := by
  have hrange : Set.range f ⊆ Z := by
    rintro _ ⟨x, rfl⟩
    have hsub : closure (closedPoints X) ⊆ f ⁻¹' (Z : Set Y) :=
      (Z.isClosed.preimage f.continuous).closure_subset_iff.mpr fun y hy => h y hy
    rw [closure_closedPoints] at hsub
    exact hsub (Set.mem_univ x)
  refine ⟨IsClosedImmersion.lift _ f ?_, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact vanishingIdeal_le_ker_of_isReduced f Z hrange

/-- The intersection number of a real 1-cycle with a `ℚ`-Cartier divisor `∑ⱼ qⱼ Eⱼ`, viewed as an
`ℝ`-Cartier divisor, is `∑ⱼ qⱼ deg_Z 𝒪_X(Eⱼ)`. -/
private theorem intersectionNumber_toReal {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (Z : Mori.OneCycle ℝ sX) (L : Mori.KCartierDivisor ℚ X) :
    Z.intersectionNumber (Fourfold.KCartierDivisor.toReal L) =
      L.sum fun E q => (q : ℝ) * Mori.OneCycle.cartierDegree E Z := by
  simp only [Mori.OneCycle.intersectionNumber, Mori.OneCycle.intersectionPairing,
    Fourfold.KCartierDivisor.toReal, Finsupp.mapRange.addMonoidHom_apply,
    Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp [Finsupp.sum, LinearMap.sum_apply]

section ClosedImmersionPushforward

variable {k : Type u} [Field k]

/-- The residue field maps of a closed immersion are isomorphisms. -/
private theorem bijective_residueFieldMap {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (y : X) : Function.Bijective (i.residueFieldMap y) := by
  refine ⟨(i.residueFieldMap y).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := X.residue_surjective y a
  obtain ⟨c, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective i y b
  exact ⟨Y.residue _ c, by
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩

public theorem residueFieldDegree_eq_one {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (y : X) : Mori.residueFieldDegree i y = 1 := by
  unfold Mori.residueFieldDegree
  letI := (i.residueFieldMap y).hom.toAlgebra
  rw [← (AlgEquiv.ofBijective (Algebra.ofId _ _)
    (bijective_residueFieldMap i y)).toLinearEquiv.finrank_eq, Module.finrank_self]

/-- Composing with a closed immersion does not change residue field degrees. -/
private theorem residueFieldDegree_comp {Z X Y : Scheme.{u}} (f : Z ⟶ X) (i : X ⟶ Y)
    [IsClosedImmersion i] (x : Z) :
    Mori.residueFieldDegree (f ≫ i) x = Mori.residueFieldDegree f x := by
  unfold Mori.residueFieldDegree
  letI := ((f ≫ i).residueFieldMap x).hom.toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.ofBijective _ (bijective_residueFieldMap i (f x))) (RingEquiv.refl _) ?_
  ext a
  change (f.residueFieldMap x).hom (i.residueFieldMap (f x) a) = ((f ≫ i).residueFieldMap x).hom a
  rw [Scheme.residueFieldMap_comp]
  rfl

/-- A point of `X` is the generic point of a proper curve exactly when its image under a closed
immersion `X ⟶ Y` is. -/
public theorem isProperCurve_comp_iff {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (sY : Y ⟶ Spec (.of k)) (y : X) :
    Mori.IsProperCurve (i ≫ sY) y ↔ Mori.IsProperCurve sY (i y) := by
  have hrange : closure (Set.range (Mori.curveSubschemeAtι y ≫ i)) = closure {i y} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change closure (i '' closure {y}) = _
    rw [i.isClosedEmbedding.closure_image_eq, closure_closure, ← Set.image_singleton,
      i.isClosedEmbedding.closure_image_eq]
  have hker : (Mori.curveSubschemeAtι y ≫ i).ker = (Mori.curveSubschemeAtι (i y)).ker := by
    rw [ker_eq_vanishingIdeal_closure_range, Scheme.IdealSheafData.ker_subschemeι]
    congr 1
    exact TopologicalSpace.Closeds.ext hrange
  haveI := IsClosedImmersion.isIso_of_ker_eq (Mori.curveSubschemeAtι y ≫ i)
    (Mori.curveSubschemeAtι (i y)) _ (IsClosedImmersion.lift_fac _ _ hker.ge) hker
  set e := IsClosedImmersion.lift (Mori.curveSubschemeAtι (i y))
    (Mori.curveSubschemeAtι y ≫ i) hker.ge
  have hfac : e ≫ Mori.curveSubschemeAtι (i y) = Mori.curveSubschemeAtι y ≫ i :=
    IsClosedImmersion.lift_fac _ _ _
  have hdim : topologicalKrullDim (Mori.curveSubschemeAt y) =
      topologicalKrullDim (Mori.curveSubschemeAt (i y)) :=
    IsHomeomorph.topologicalKrullDim_eq _
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso e))).isHomeomorph
  have hprop : IsProper (Mori.curveSubschemeAtι y ≫ i ≫ sY) ↔
      IsProper (Mori.curveSubschemeAtι (i y) ≫ sY) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    exact MorphismProperty.cancel_left_of_respectsIso @IsProper e _
  exact ⟨fun h => ⟨hdim ▸ h.dim_eq, hprop.mp h.isProper⟩,
    fun h => ⟨hdim ▸ h.dim_eq, hprop.mpr h.isProper⟩⟩

/-- Push-forward of 1-cycles is functorial for a closed immersion `i`: `i_* f_*[x] = (f ≫ i)_*[x]`. -/
private theorem pushforward_cyclePushforwardOfPoint {Z X Y : Scheme.{u}} (f : Z ⟶ X) (i : X ⟶ Y)
    [IsClosedImmersion i] (sY : Y ⟶ Spec (.of k)) (x : Z) :
    Mori.OneCycle.pushforward ℤ (i ≫ sY) sY i (Mori.cyclePushforwardOfPoint ℤ (i ≫ sY) f x) =
      Mori.cyclePushforwardOfPoint ℤ sY (f ≫ i) x := by
  unfold Mori.cyclePushforwardOfPoint
  by_cases h : Mori.IsProperCurve (i ≫ sY) (f x)
  · have h' : Mori.IsProperCurve sY ((f ≫ i) x) := (isProperCurve_comp_iff i sY (f x)).mp h
    rw [dif_pos h, dif_pos h']
    simp only [Mori.OneCycle.pushforward, Finsupp.linearCombination_single,
      Mori.cyclePushforwardOfPoint, dif_pos ((isProperCurve_comp_iff i sY (f x)).mp h),
      Finsupp.smul_single, residueFieldDegree_comp]
    simp [residueFieldDegree_eq_one]
  · have h' : ¬ Mori.IsProperCurve sY ((f ≫ i) x) := fun h' =>
      h ((isProperCurve_comp_iff i sY (f x)).mpr h')
    rw [dif_neg h, dif_neg h', map_zero]

private theorem cyclePushforwardOfPoint_eq_zero_iff {Z X Y : Scheme.{u}} (f : Z ⟶ X)
    (i : X ⟶ Y) [IsClosedImmersion i] (sY : Y ⟶ Spec (.of k)) (x : Z) :
    Mori.cyclePushforwardOfPoint ℤ (i ≫ sY) f x = 0 ↔
      Mori.cyclePushforwardOfPoint ℤ sY (f ≫ i) x = 0 := by
  unfold Mori.cyclePushforwardOfPoint
  by_cases h : Mori.IsProperCurve (i ≫ sY) (f x)
  · have h' : Mori.IsProperCurve sY ((f ≫ i) x) := (isProperCurve_comp_iff i sY (f x)).mp h
    rw [dif_pos h, dif_pos h', Finsupp.single_eq_zero, Finsupp.single_eq_zero,
      residueFieldDegree_comp]
  · have h' : ¬ Mori.IsProperCurve sY ((f ≫ i) x) := fun h' =>
      h ((isProperCurve_comp_iff i sY (f x)).mpr h')
    rw [dif_neg h, dif_neg h']
    simp

/-- Push-forward along a closed immersion commutes with a (possibly infinite) weighted sum of
point push-forwards. -/
private theorem pushforward_finsum_smul_cyclePushforwardOfPoint {ι : Type*} {Z X Y : Scheme.{u}}
    (f : Z ⟶ X) (i : X ⟶ Y) [IsClosedImmersion i] (sY : Y ⟶ Spec (.of k)) (n : ι → ℤ)
    (x : ι → Z) :
    Mori.OneCycle.pushforward ℤ (i ≫ sY) sY i
        (∑ᶠ c, n c • Mori.cyclePushforwardOfPoint ℤ (i ≫ sY) f (x c)) =
      ∑ᶠ c, n c • Mori.cyclePushforwardOfPoint ℤ sY (f ≫ i) (x c) := by
  have hpt : ∀ c, Mori.OneCycle.pushforward ℤ (i ≫ sY) sY i
      (n c • Mori.cyclePushforwardOfPoint ℤ (i ≫ sY) f (x c)) =
        n c • Mori.cyclePushforwardOfPoint ℤ sY (f ≫ i) (x c) := fun c => by
    rw [map_zsmul, pushforward_cyclePushforwardOfPoint]
  by_cases hfin : (Function.support fun c =>
      n c • Mori.cyclePushforwardOfPoint ℤ (i ≫ sY) f (x c)).Finite
  · rw [map_finsum _ hfin]
    exact finsum_congr hpt
  · have hsupp : (Function.support fun c =>
        n c • Mori.cyclePushforwardOfPoint ℤ sY (f ≫ i) (x c)) =
        Function.support fun c => n c • Mori.cyclePushforwardOfPoint ℤ (i ≫ sY) f (x c) := by
      ext c
      simp only [Function.mem_support, ne_eq, smul_eq_zero,
        cyclePushforwardOfPoint_eq_zero_iff f i sY]
    rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (hsupp ▸ hfin), map_zero]

/-- The proper curve `i(C)` of `Y` given by a proper curve `C` of `X` and a closed immersion
`i : X ⟶ Y`. -/
public def ProperCurve.mapClosedImmersion {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (sY : Y ⟶ Spec (.of k)) (C : Mori.ProperCurve (i ≫ sY)) : Mori.ProperCurve sY :=
  ⟨i C.point, (isProperCurve_comp_iff i sY C.point).mp C.isProperCurve⟩

private theorem ProperCurve.mapClosedImmersion_injective {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (sY : Y ⟶ Spec (.of k)) :
    Function.Injective (ProperCurve.mapClosedImmersion i sY) := fun C C' h =>
  Mori.ProperCurve.ext (i.isClosedEmbedding.injective (congrArg Mori.ProperCurve.point h))

/-- Push-forward of 1-cycles along a closed immersion relabels each curve by its image. -/
public theorem pushforward_eq_mapDomain {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (sY : Y ⟶ Spec (.of k)) (Z : Mori.OneCycle ℤ (i ≫ sY)) :
    Mori.OneCycle.pushforward ℤ (i ≫ sY) sY i Z =
      Finsupp.mapDomain (ProperCurve.mapClosedImmersion i sY) Z := by
  induction Z using Finsupp.induction_linear with
  | zero => simp
  | add Z Z' hZ hZ' => rw [map_add, hZ, hZ', Finsupp.mapDomain_add]
  | single C a =>
    rw [Finsupp.mapDomain_single, Mori.OneCycle.pushforward, Finsupp.linearCombination_single,
      Mori.cyclePushforwardOfPoint, dif_pos ((isProperCurve_comp_iff i sY C.point).mp
        C.isProperCurve), residueFieldDegree_eq_one, Finsupp.smul_single]
    simp [ProperCurve.mapClosedImmersion]

public theorem pushforward_injective {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (sY : Y ⟶ Spec (.of k)) :
    Function.Injective (Mori.OneCycle.pushforward ℤ (i ≫ sY) sY i) := fun Z Z' h => by
  rw [pushforward_eq_mapDomain, pushforward_eq_mapDomain] at h
  exact Finsupp.mapDomain_injective (ProperCurve.mapClosedImmersion_injective i sY) h

public theorem pushforward_nonneg {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (sY : Y ⟶ Spec (.of k)) {Z : Mori.OneCycle ℤ (i ≫ sY)} (hZ : 0 ≤ Z) (C : Mori.ProperCurve sY) :
    0 ≤ Mori.OneCycle.pushforward ℤ (i ≫ sY) sY i Z C := by
  classical
  rw [pushforward_eq_mapDomain]
  by_cases hC : C ∈ Set.range (ProperCurve.mapClosedImmersion i sY)
  · obtain ⟨C', rfl⟩ := hC
    rw [Finsupp.mapDomain_apply_of_injective (ProperCurve.mapClosedImmersion_injective i sY)]
    exact hZ C'
  · rw [Finsupp.mapDomain_notin_range _ _ hC]

end ClosedImmersionPushforward

section CurvePoints

/-- A space of dimension at most one has no chain `a ⤳ b ⤳ c` of three distinct points. -/
private theorem false_of_specializes_of_topologicalKrullDim_le_one {Y : Type*} [TopologicalSpace Y] [T0Space Y]
    (hY : topologicalKrullDim Y ≤ 1) {a b c : Y} (hab : a ⤳ b) (hbc : b ⤳ c) (hab' : a ≠ b)
    (hbc' : b ≠ c) : False := by
  let f : Fin 3 → TopologicalSpace.IrreducibleCloseds Y := fun i =>
    ⟨closure {![c, b, a] i}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : ∀ {x y : Y}, x ⤳ y → x ≠ y →
      (⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds Y) <
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    intro x y hxy hne
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp hxy) fun h => hne ?_
    have : y ⤳ x := specializes_iff_closure_subset.mpr
      (le_of_eq (congrArg TopologicalSpace.IrreducibleCloseds.carrier h).symm)
    exact (hxy.antisymm this).eq
  have hmono : StrictMono f := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · exact hlt hbc hbc'
    · exact hlt hab hab'
  have : ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim Y :=
    Order.le_krullDim_iff.mpr ⟨LTSeries.mk 2 f hmono, rfl⟩
  have := this.trans hY
  norm_num at this

/-- In a Noetherian quasi-sober space, a closed set all of whose points are closed is finite. -/
private theorem finite_of_isClosed_of_forall_isClosed_singleton {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {S : Set X} (hS : IsClosed S)
    (h : ∀ x ∈ S, IsClosed ({x} : Set X)) : S.Finite := by
  obtain ⟨T, hTf, hTc, hTi, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  refine hTf.sUnion fun t ht => ?_
  obtain ⟨g, hg⟩ := QuasiSober.sober (hTi t ht) (hTc t ht)
  have : t = {g} := by rw [← hg.def, (h g (Set.mem_sUnion_of_mem hg.mem ht)).closure_eq]
  exact this ▸ Set.finite_singleton g

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A proper curve contains no chain `C ⤳ p ⤳ q` of three distinct points. -/
private theorem ProperCurve.false_of_specializes_chain (C : Mori.ProperCurve sX) {p q : X}
    (hp : C.point ⤳ p) (hq : p ⤳ q) (hpC : C.point ≠ p) (hqp : p ≠ q) : False := by
  have hrange : Set.range C.ι = closure {C.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨y0, hy0⟩ : C.point ∈ Set.range C.ι := hrange ▸ subset_closure rfl
  obtain ⟨y1, hy1⟩ : p ∈ Set.range C.ι := hrange ▸ specializes_iff_mem_closure.mp hp
  obtain ⟨y2, hy2⟩ : q ∈ Set.range C.ι :=
    hrange ▸ specializes_iff_mem_closure.mp (hp.trans hq)
  have hind := C.ι.isClosedEmbedding.isInducing
  refine false_of_specializes_of_topologicalKrullDim_le_one C.dim_eq.le (a := y0) (b := y1) (c := y2) ?_ ?_ ?_ ?_
  · rwa [← hind.specializes_iff, hy0, hy1]
  · rwa [← hind.specializes_iff, hy1, hy2]
  · rintro rfl
    exact hpC (hy0.symm.trans hy1)
  · rintro rfl
    exact hqp (hy1.symm.trans hy2)

/-- On a Jacobson scheme, every specialization of the generic point of a proper curve other than
the generic point itself is a closed point. -/
public theorem ProperCurve.isClosed_singleton_of_specializes [JacobsonSpace X]
    (C : Mori.ProperCurve sX) {p : X} (hp : C.point ⤳ p) (hpC : C.point ≠ p) :
    IsClosed ({p} : Set X) := by
  have hcl := JacobsonSpace.closure_inter_closedPoints (isClosed_closure (s := ({p} : Set X)))
  obtain ⟨q, hq, hqc⟩ : (closure {p} ∩ closedPoints X).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hcl
    exact (hcl ▸ subset_closure rfl : p ∈ (∅ : Set X))
  by_cases hqp : p = q
  · exact hqp ▸ hqc
  · exact (ProperCurve.false_of_specializes_chain C hp
      (specializes_iff_mem_closure.mpr hq) hpC hqp).elim

end CurvePoints

section ProjectivePoints

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Substituting `xᵦ ↦ cᵦ x_{b₀}` in a form `f` of degree `n` gives `f(c) x_{b₀}ⁿ`. -/
private theorem aeval_C_mul_X {ι k : Type*} [Fintype ι] [Field k] (c : ι → k) (b₀ : ι)
    {f : MvPolynomial ι k} {n : ℕ} (hf : f.IsHomogeneous n) :
    aeval (fun b => C (c b) * (X b₀ : MvPolynomial ι k)) f = C (eval c f) * X b₀ ^ n := by
  rw [aeval_def, eval₂_eq', eval_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have := hf (mem_support_iff.mp hd)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod,
    map_pow, algebraMap_eq]
  ring

/-- Some coordinate `x_j` does not vanish at a point of `ℙ^ι_k`. -/
private theorem exists_X_notMem {k ι : Type*} [Field k]
    (p : ProjectiveSpectrum (homogeneousSubmodule ι k)) :
    ∃ j, (X j : MvPolynomial ι k) ∉ p.asHomogeneousIdeal := by
  by_contra hX
  push Not at hX
  apply p.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant _).toIdeal ≤ p.asHomogeneousIdeal.toIdeal
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn f hf
  have hspan : f ∈ Ideal.span (X '' Set.univ : Set (MvPolynomial ι k)) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    have hdeg := (mem_homogeneousSubmodule n f).mp hf (Finsupp.mem_support_iff.mp hm)
    by_contra hcon
    push Not at hcon
    have : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ _)
    subst this
    simp at hdeg
    omega
  refine (Ideal.span_le.mpr ?_) hspan
  rintro _ ⟨b, -, rfl⟩
  exact hX b

/-- If a point `p` of `ℙ^ι_k` satisfies the relations `c_{b'} xᵦ - cᵦ x_{b'} ∈ p` of the point
`[c]`, and `c_{b₀} ≠ 0`, then `x_{b₀} ∉ p`. -/
private theorem X_notMem_of_relations {k ι : Type*} [Field k] (c : ι → k) {b₀ : ι}
    (hc : c b₀ ≠ 0) (p : ProjectiveSpectrum (homogeneousSubmodule ι k))
    (hp : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal) :
    (X b₀ : MvPolynomial ι k) ∉ p.asHomogeneousIdeal := by
  intro h0
  obtain ⟨b, hb⟩ := exists_X_notMem p
  apply hb
  have h2 : c b • (X b₀ : MvPolynomial ι k) ∈ p.asHomogeneousIdeal := by
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ h0
  have h3 : c b₀ • (X b : MvPolynomial ι k) ∈ p.asHomogeneousIdeal := by
    simpa using Ideal.add_mem _ (hp b b₀) h2
  have := Ideal.mul_mem_left (p.asHomogeneousIdeal.toIdeal) (C (c b₀)⁻¹) h3
  rwa [smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at this

/-- A point `p` of `ℙ^ι_k` satisfying the relations of the point `[c]` contains a form `f` exactly
when `f` vanishes at `c`. -/
private theorem mem_iff_eval_of_relations {k ι : Type*} [Fintype ι] [Field k] (c : ι → k)
    {b₀ : ι} (hc : c b₀ ≠ 0) (p : ProjectiveSpectrum (homogeneousSubmodule ι k))
    (hp : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal)
    {f : MvPolynomial ι k} {n : ℕ} (hf : f.IsHomogeneous n) :
    f ∈ p.asHomogeneousIdeal ↔ eval (fun b => c b / c b₀) f = 0 := by
  let I := p.asHomogeneousIdeal.toIdeal
  let g : ι → MvPolynomial ι k := fun b => C (c b / c b₀) * X b₀
  have hg : ∀ b, X b - g b ∈ I := by
    intro b
    have := Ideal.mul_mem_left I (C (c b₀)⁻¹) (hp b b₀)
    convert this using 1
    simp only [g, smul_eq_C_mul, mul_sub, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul,
      div_eq_inv_mul, mul_comm (c b₀)⁻¹]
  have hπ : (Ideal.Quotient.mkₐ k I).comp (aeval g) = Ideal.Quotient.mkₐ k I := by
    refine MvPolynomial.algHom_ext fun b => ?_
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    exact (Ideal.Quotient.eq.mpr (hg b)).symm
  have hdiff : f - aeval g f ∈ I := by
    rw [← Ideal.Quotient.eq]
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using
      (congrArg (fun φ => φ f) hπ).symm
  have hval : aeval g f = C (eval (fun b => c b / c b₀) f) * X b₀ ^ n :=
    aeval_C_mul_X (fun b => c b / c b₀) b₀ hf
  have hX : X b₀ ^ n ∉ I := fun h =>
    X_notMem_of_relations c hc p hp (p.isPrime.mem_of_pow_mem n h)
  constructor
  · intro hfI
    by_contra he
    have h1 : C (eval (fun b => c b / c b₀) f) * X b₀ ^ n ∈ I := by
      rw [← hval]
      have := I.sub_mem hfI hdiff
      rwa [sub_sub_cancel] at this
    have := Ideal.mul_mem_left I (C (eval (fun b => c b / c b₀) f)⁻¹) h1
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ he, C_1, one_mul] at this
    exact hX this
  · intro he
    rwa [hval, he, C_0, zero_mul, sub_zero] at hdiff

/-- A point of `ℙ^ι_k` is determined by the relations of a point `[c]`, `c ≠ 0`, that it
satisfies. -/
private theorem eq_of_relations {k ι : Type*} [Fintype ι] [Field k] (c : ι → k) {b₀ : ι}
    (hc : c b₀ ≠ 0) (p p' : ProjectiveSpectrum (homogeneousSubmodule ι k))
    (hp : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal)
    (hp' : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p'.asHomogeneousIdeal) :
    p = p' := by
  ext f
  change f ∈ p.asHomogeneousIdeal.toIdeal ↔ f ∈ p'.asHomogeneousIdeal.toIdeal
  rw [p.asHomogeneousIdeal.isHomogeneous.mem_iff, p'.asHomogeneousIdeal.isHomogeneous.mem_iff]
  refine forall_congr' fun i => ?_
  have hi : ((DirectSum.decompose (homogeneousSubmodule ι k) f i :
      MvPolynomial ι k)).IsHomogeneous i :=
    (mem_homogeneousSubmodule i _).mp (DirectSum.decompose (homogeneousSubmodule ι k) f i).2
  exact (mem_iff_eval_of_relations c hc p hp hi).trans
    (mem_iff_eval_of_relations c hc p' hp' hi).symm

/-- For `c ≠ 0` the point `[c]` of `ℙ^ι_k` exists: a closed point satisfying the relations
`c_{b'} xᵦ - cᵦ x_{b'}`. It is the homogeneous core of the kernel of `xᵦ ↦ cᵦ t`. -/
private theorem exists_isClosed_relations {k ι : Type*} [Fintype ι] [Field k] (c : ι → k)
    {b₀ : ι} (hc : c b₀ ≠ 0) :
    ∃ p : ProjectiveSpectrum (homogeneousSubmodule ι k), IsClosed ({p} : Set _) ∧
      ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal := by
  classical
  let φ : MvPolynomial ι k →ₐ[k] Polynomial k :=
    aeval fun b => Polynomial.C (c b) * Polynomial.X
  have hprime : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  let I := (RingHom.ker φ).homogeneousCore (homogeneousSubmodule ι k)
  have hrel : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ I := by
    intro b b'
    refine Ideal.mem_homogeneousCore_of_homogeneous_of_mem ?_ ?_
    · refine ⟨1, ?_⟩
      rw [mem_homogeneousSubmodule, smul_eq_C_mul, smul_eq_C_mul]
      exact ((isHomogeneous_C _ _).mul (isHomogeneous_X k b)).sub
        ((isHomogeneous_C _ _).mul (isHomogeneous_X k b'))
    · rw [RingHom.mem_ker]
      simp only [φ, AlgHom.coe_toRingHom, map_sub, map_smul, aeval_X]
      rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
      ring
  let p : ProjectiveSpectrum (homogeneousSubmodule ι k) :=
    ⟨I, hprime.homogeneousCore, fun hle => by
      have hX : (X b₀ : MvPolynomial ι k) ∈ I := hle (by
        rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
          DirectSum.decompose_of_mem_ne _ (isHomogeneous_X k b₀) one_ne_zero])
      have := Ideal.toIdeal_homogeneousCore_le _ _ hX
      rw [RingHom.mem_ker] at this
      simp [φ, hc] at this⟩
  refine ⟨p, ?_, hrel⟩
  have : ({p} : Set _) =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule ι k) (I : Set _) := by
    ext q
    simp only [Set.mem_singleton_iff, ProjectiveSpectrum.mem_zeroLocus]
    exact ⟨fun h => h ▸ le_rfl,
      fun hq => eq_of_relations c hc q p (fun b b' => hq (hrel b b')) hrel⟩
  rw [this]
  exact ProjectiveSpectrum.isClosed_zeroLocus _ _

/-- Dehomogenization: if `x_j ∉ p`, then `p + (x_j - 1)` is a proper ideal. -/
private theorem one_notMem_sup_span_X_sub_one {k ι : Type*} [Field k]
    (p : ProjectiveSpectrum (homogeneousSubmodule ι k)) {j : ι}
    (hj : (X j : MvPolynomial ι k) ∉ p.asHomogeneousIdeal) :
    (1 : MvPolynomial ι k) ∉ p.asHomogeneousIdeal.toIdeal ⊔ Ideal.span {X j - 1} := by
  set q := p.asHomogeneousIdeal.toIdeal
  have hcomp : ∀ f ∈ q, ∀ n, homogeneousComponent n f ∈ q := fun f hf n => by
    rw [← decomposition.decompose'_apply]
    exact (p.asHomogeneousIdeal.isHomogeneous.mem_iff.mp hf) n
  intro h
  obtain ⟨f, hf, r, hr, hfr⟩ := Submodule.mem_sup.mp h
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have key : ∀ n, homogeneousComponent (n + 1) g ∈ q → homogeneousComponent n g ∈ q := by
    intro n hn
    have h1 := congrArg (homogeneousComponent (n + 1)) hfr
    rw [map_add, mul_sub, mul_one, map_sub] at h1
    have hX : homogeneousComponent (n + 1) (g * X j) = X j * homogeneousComponent n g := by
      rw [mul_comm, ← decomposition.decompose'_apply, ← decomposition.decompose'_apply,
        add_comm]
      exact DirectSum.coe_decompose_mul_add_of_left_mem (homogeneousSubmodule ι k)
        ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X k j))
    have h0 : homogeneousComponent (n + 1) (1 : MvPolynomial ι k) = 0 := by
      rw [homogeneousComponent_eq_zero]
      simp
    rw [hX, h0] at h1
    have hmem : X j * homogeneousComponent n g ∈ q := by
      have : X j * homogeneousComponent n g =
          homogeneousComponent (n + 1) g - homogeneousComponent (n + 1) f := by
        linear_combination h1
      rw [this]
      exact q.sub_mem hn (hcomp f hf _)
    exact (p.isPrime.mem_or_mem hmem).resolve_left hj
  have hall : ∀ n, homogeneousComponent n g ∈ q := by
    have hm : ∀ m, homogeneousComponent (g.totalDegree + 1 - m) g ∈ q := by
      intro m
      induction m with
      | zero =>
        rw [homogeneousComponent_eq_zero _ _ (by omega)]
        exact q.zero_mem
      | succ m ih =>
        by_cases hmd : m ≤ g.totalDegree
        · have := key (g.totalDegree - m) (by
            rw [show g.totalDegree - m + 1 = g.totalDegree + 1 - m by omega]
            exact ih)
          rwa [show g.totalDegree - m = g.totalDegree + 1 - (m + 1) by omega] at this
        · rwa [show g.totalDegree + 1 - (m + 1) = g.totalDegree + 1 - m by omega]
    intro n
    by_cases hn : n ≤ g.totalDegree + 1
    · have := hm (g.totalDegree + 1 - n)
      rwa [show g.totalDegree + 1 - (g.totalDegree + 1 - n) = n by omega] at this
    · rw [homogeneousComponent_eq_zero _ _ (by omega)]
      exact q.zero_mem
  have hg : g ∈ q := by
    rw [← sum_homogeneousComponent g]
    exact q.sum_mem fun n _ => hall n
  apply p.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hfr]
  exact q.add_mem hf (q.mul_mem_right _ hg)

/-- **Projective Nullstellensatz.** Over an algebraically closed field every closed point of
`ℙ^ι_k` is a point `[a]`, normalized by `a_j = 1`. -/
private theorem exists_relations_of_isClosed {k ι : Type*} [Fintype ι] [Field k] [IsAlgClosed k]
    (p : ProjectiveSpectrum (homogeneousSubmodule ι k)) (hp : IsClosed ({p} : Set _)) :
    ∃ (a : ι → k) (j : ι), a j = 1 ∧
      ∀ b b', a b' • (X b : MvPolynomial ι k) - a b • X b' ∈ p.asHomogeneousIdeal := by
  obtain ⟨j, hj⟩ := exists_X_notMem p
  set J := p.asHomogeneousIdeal.toIdeal ⊔ Ideal.span {X j - 1}
  have hJ : (zeroLocus k J).Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    have := vanishingIdeal_zeroLocus_eq_radical (K := k) J
    rw [hem, vanishingIdeal_empty, eq_comm, Ideal.radical_eq_top] at this
    exact one_notMem_sup_span_X_sub_one p hj (J.eq_top_iff_one.mp this)
  obtain ⟨a, ha⟩ := hJ
  rw [mem_zeroLocus_iff] at ha
  have haJ : ∀ f ∈ p.asHomogeneousIdeal.toIdeal, eval a f = 0 := fun f hf => by
    simpa [aeval_eq_eval] using ha f (Ideal.mem_sup_left hf)
  have haj : a j = 1 := by
    simpa [sub_eq_zero] using ha (X j - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨p', -, hrel⟩ := exists_isClosed_relations a (b₀ := j) (by simp [haj])
  have hle : p ≤ p' := by
    intro f hf
    change f ∈ p'.asHomogeneousIdeal.toIdeal
    rw [p'.asHomogeneousIdeal.isHomogeneous.mem_iff]
    intro n
    have hfn : ((DirectSum.decompose (homogeneousSubmodule ι k) f n : MvPolynomial ι k)) ∈
        p.asHomogeneousIdeal.toIdeal := p.asHomogeneousIdeal.isHomogeneous.mem_iff.mp hf n
    have hhom : ((DirectSum.decompose (homogeneousSubmodule ι k) f n :
        MvPolynomial ι k)).IsHomogeneous n :=
      (mem_homogeneousSubmodule n _).mp (DirectSum.decompose (homogeneousSubmodule ι k) f n).2
    refine (mem_iff_eval_of_relations a (b₀ := j) (by simp [haj]) p' hrel
      hhom).mpr ?_
    simpa [haj] using haJ _ hfn
  have hmem : p' ∈ closure ({p} : Set _) :=
    (ProjectiveSpectrum.le_iff_mem_closure _ p p').mp hle
  rw [hp.closure_eq, Set.mem_singleton_iff] at hmem
  exact ⟨a, j, haj, fun b b' => hmem ▸ hrel b b'⟩

/-- A linear form `∑ vⱼ xⱼ` lies in the point `[a]` (normalized by `a_j = 1`) exactly when
`v · a = 0`. -/
private theorem linearForm_mem_iff {k ι : Type*} [Fintype ι] [Field k] (a : ι → k) {j : ι}
    (haj : a j = 1) (p : ProjectiveSpectrum (homogeneousSubmodule ι k))
    (hp : ∀ b b', a b' • (X b : MvPolynomial ι k) - a b • X b' ∈ p.asHomogeneousIdeal)
    (v : ι → k) :
    (∑ i, C (v i) * X i : MvPolynomial ι k) ∈ p.asHomogeneousIdeal ↔ v ⬝ᵥ a = 0 := by
  have hhom : (∑ i, C (v i) * X i : MvPolynomial ι k).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ i
  rw [mem_iff_eval_of_relations a (b₀ := j) (by simp [haj]) p hp hhom]
  simp [haj, dotProduct]

/-- The relation `α xᵦ - β x_{b'}` as a linear form. -/
private theorem linearForm_single_sub_single {k ι : Type*} [Fintype ι] [DecidableEq ι] [Field k]
    (b b' : ι) (α β : k) :
    (∑ i, C ((Pi.single b α - Pi.single b' β : ι → k) i) * X i : MvPolynomial ι k) =
      α • X b - β • X b' := by
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib, smul_eq_C_mul]
  congr 1
  · rw [Finset.sum_eq_single b (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
    simp
  · rw [Finset.sum_eq_single b' (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
    simp

/-- Over an infinite field, given vectors `wₛ, cₛ` with `wₛ · cₛ ≠ 0`, some combination
`v = ∑ₛ tₛ wₛ` has `v · cₛ ≠ 0` for every `s`. -/
private theorem exists_dotProduct_ne_zero {k ι σ : Type*} [Fintype ι] [Fintype σ] [Field k]
    [Infinite k] (w c : σ → ι → k) (h : ∀ s, w s ⬝ᵥ c s ≠ 0) :
    ∃ t : σ → k, ∀ s, (∑ r, t r • w r) ⬝ᵥ c s ≠ 0 := by
  classical
  let P : MvPolynomial σ k := ∏ s, ∑ r, X r * C (w r ⬝ᵥ c s)
  have hfac : ∀ s, (∑ r, X r * C (w r ⬝ᵥ c s) : MvPolynomial σ k) ≠ 0 := by
    intro s h0
    have := congrArg (fun p : MvPolynomial _ _ => p.coeff (Finsupp.single s 1)) h0
    simp [coeff_sum, coeff_X_mul', Finsupp.single_apply, h s] at this
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hfac s
  obtain ⟨t, ht⟩ : ∃ t, eval t P ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hP (MvPolynomial.funext fun t => by simpa using hall t)
  refine ⟨t, fun s => ?_⟩
  have := Finset.prod_ne_zero_iff.mp (by simpa [P, map_prod] using ht) s (Finset.mem_univ s)
  simpa [map_sum, sum_dotProduct, smul_dotProduct, mul_comm] using this

/-- Two points of coefficients `c`, `c'` whose relations hold at the same point of projective
space are proportional. -/
private theorem mul_eq_mul_of_relations {k ι : Type*} [Fintype ι] [Field k] (c c' : ι → k)
    {b₀ : ι} (hc : c b₀ ≠ 0) (p : ProjectiveSpectrum (homogeneousSubmodule ι k))
    (hp : ∀ b b', c b' • (X b : MvPolynomial ι k) - c b • X b' ∈ p.asHomogeneousIdeal)
    (hp' : ∀ b b', c' b' • (X b : MvPolynomial ι k) - c' b • X b' ∈ p.asHomogeneousIdeal)
    (b : ι) : c' b * c b₀ = c b * c' b₀ := by
  have hX : ∀ b, (X b : MvPolynomial ι k).IsHomogeneous 1 := isHomogeneous_X k
  have hhom : (c' b₀ • (X b : MvPolynomial ι k) - c' b • X b₀).IsHomogeneous 1 := by
    rw [smul_eq_C_mul, smul_eq_C_mul]
    exact ((isHomogeneous_C _ _).mul (hX b)).sub ((isHomogeneous_C _ _).mul (hX b₀))
  have := (mem_iff_eval_of_relations c hc p hp hhom).mp (hp' b b₀)
  simp only [map_sub, smul_eval, eval_X, div_self hc] at this
  field_simp at this
  linear_combination -this

end ProjectivePoints

section Factorization

open UniqueFactorizationMonoid MvPolynomial

private theorem normalizedFactors_finset_prod {R α : Type*} [CommRing R] [IsDomain R]
    [NormalizationMonoid R] [UniqueFactorizationMonoid R] (s : Finset α) (f : α → R)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    normalizedFactors (∏ a ∈ s, f a) = ∑ a ∈ s, normalizedFactors (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, normalizedFactors_mul (hf a (by simp))
      (Finset.prod_ne_zero_iff.mpr fun b hb => hf b (by simp [hb])),
      ih fun b hb => hf b (by simp [hb])]

/-- In a product `∏ G_b ^ m_b` of pairwise non-associated irreducibles, the exponent of `G_a` is
recovered as the multiplicity of `G_a` among the normalized factors. -/
private theorem count_normalizedFactors_prod_pow {R α : Type*} [CommRing R] [IsDomain R]
    [NormalizationMonoid R] [UniqueFactorizationMonoid R] [DecidableEq R] (s : Finset α)
    (G : α → R) (m : α → ℕ) (hG : ∀ a ∈ s, Irreducible (G a))
    (hinj : ∀ a ∈ s, ∀ b ∈ s, Associated (G a) (G b) → a = b) {a : α} (ha : a ∈ s) :
    (normalizedFactors (∏ b ∈ s, G b ^ m b)).count (normalize (G a)) = m a := by
  classical
  rw [normalizedFactors_finset_prod _ _ fun b hb => pow_ne_zero _ (hG b hb).ne_zero,
    Multiset.count_sum', Finset.sum_eq_single a]
  · rw [normalizedFactors_pow, normalizedFactors_irreducible (hG a ha), Multiset.count_nsmul,
      Multiset.count_singleton_self, mul_one]
  · intro b hb hba
    rw [normalizedFactors_pow, normalizedFactors_irreducible (hG b hb), Multiset.count_nsmul,
      Multiset.count_singleton, if_neg, mul_zero]
    intro h
    exact hba (hinj b hb a ha (normalize_eq_normalize_iff_associated.mp h.symm))
  · intro h
    exact absurd ha h

/-- **Nullstellensatz.** Over an algebraically closed field, an irreducible polynomial divides
every polynomial vanishing on its zero set. -/
private theorem dvd_of_forall_eval {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ]
    {G G' : MvPolynomial σ k} (hG : Irreducible G) (h : ∀ x, eval x G = 0 → eval x G' = 0) :
    G ∣ G' := by
  have hprime : (Ideal.span {G}).IsPrime :=
    (Ideal.span_singleton_prime hG.ne_zero).mpr hG.prime
  have hmem : G' ∈ vanishingIdeal k (zeroLocus k (Ideal.span {G})) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    simpa [aeval_eq_eval] using
      h x (by simpa [aeval_eq_eval] using hx G (Ideal.mem_span_singleton_self G))
  rw [vanishingIdeal_zeroLocus_eq_radical, hprime.radical] at hmem
  exact Ideal.mem_span_singleton.mp hmem

/-- Over an algebraically closed field, irreducible polynomials with the same zero set are
associated. -/
private theorem associated_of_forall_eval {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ]
    {G G' : MvPolynomial σ k} (hG : Irreducible G) (hG' : Irreducible G')
    (h : ∀ x, eval x G = 0 ↔ eval x G' = 0) : Associated G G' :=
  associated_of_dvd_dvd (dvd_of_forall_eval hG fun x => (h x).mp)
    (dvd_of_forall_eval hG' fun x => (h x).mpr)

end Factorization

section LocalAlgebra

open MvPolynomial

variable {B : Type*} [CommRing B] [IsDomain B] (𝔪 : Ideal B) [𝔪.IsPrime]

/-- The map `B_h → B_𝔪` for `h ∉ 𝔪`. -/
private noncomputable def awayToAtPrime {h : B} (hh : h ∉ 𝔪) :
    Localization.Away h →+* Localization.AtPrime 𝔪 :=
  IsLocalization.Away.lift h
    (IsLocalization.map_units (M := 𝔪.primeCompl) (Localization.AtPrime 𝔪) ⟨h, hh⟩)

private theorem awayToAtPrime_algebraMap {h : B} (hh : h ∉ 𝔪) (b : B) :
    awayToAtPrime 𝔪 hh (algebraMap B _ b) = algebraMap B _ b :=
  IsLocalization.Away.lift_eq h _ b

private theorem isDomain_away {h : B} (hh : h ∉ 𝔪) : IsDomain (Localization.Away h) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (fun h0 => hh (h0 ▸ 𝔪.zero_mem)))

private theorem awayToAtPrime_injective {h : B} (hh : h ∉ 𝔪) :
    Function.Injective (awayToAtPrime 𝔪 hh) := by
  haveI := isDomain_away 𝔪 hh
  have hR : Function.Injective (algebraMap B (Localization.AtPrime 𝔪)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔪)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) x
  have h1 := congrArg (awayToAtPrime 𝔪 hh) hs
  rw [map_mul, hx, zero_mul, awayToAtPrime_algebraMap, eq_comm] at h1
  have ha : a = 0 := hR (by rw [h1, map_zero])
  rw [ha, map_zero] at hs
  exact (mul_eq_zero.mp hs).resolve_right
    ((IsLocalization.map_units (Localization.Away h) s).ne_zero)

private theorem exists_away_lift {ι : Type*} [Fintype ι] (r : ι → Localization.AtPrime 𝔪) :
    ∃ (h : B) (hh : h ∉ 𝔪) (b : ι → Localization.Away h),
      ∀ i, awayToAtPrime 𝔪 hh (b i) = r i := by
  classical
  choose p hp using fun i => IsLocalization.surj 𝔪.primeCompl (r i)
  set h := ∏ i, ((p i).2 : B)
  have hh : h ∉ 𝔪 := Submonoid.prod_mem 𝔪.primeCompl fun i _ => (p i).2.2
  have hunit : ∀ i, IsUnit (algebraMap B (Localization.Away h) (p i).2) := fun i =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun j => ((p j).2 : B))
      (Finset.mem_univ i))) (IsLocalization.Away.algebraMap_isUnit _)
  refine ⟨h, hh, fun i => algebraMap B _ (p i).1 * ((hunit i).unit⁻¹ : _), fun i => ?_⟩
  have hsu : awayToAtPrime 𝔪 hh ((hunit i).unit⁻¹ : (Localization.Away h)ˣ) *
      algebraMap B (Localization.AtPrime 𝔪) (p i).2 = 1 := by
    rw [← awayToAtPrime_algebraMap 𝔪 hh, ← map_mul, IsUnit.val_inv_mul, map_one]
  rw [map_mul, awayToAtPrime_algebraMap, ← hp i, mul_assoc, mul_comm (algebraMap B _ _),
    hsu, mul_one]

/-- Lifting finitely many polynomials over `B_𝔪` to some `B_h`. -/
private theorem exists_away_lift_poly {σ ι : Type*} [Fintype ι] (p : ι → MvPolynomial σ (Localization.AtPrime 𝔪)) :
    ∃ (h : B) (hh : h ∉ 𝔪) (P : ι → MvPolynomial σ (Localization.Away h)),
      ∀ i, MvPolynomial.map (awayToAtPrime 𝔪 hh) (P i) = p i := by
  classical
  obtain ⟨h, hh, b, hb⟩ := exists_away_lift 𝔪 (ι := Σ i, (p i).support)
    (fun ie => (p ie.1).coeff ie.2)
  refine ⟨h, hh, fun i => ∑ e : (p i).support, MvPolynomial.monomial e.1 (b ⟨i, e⟩), fun i => ?_⟩
  rw [map_sum]
  conv_rhs => rw [(p i).as_sum, ← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, hb]

private theorem awayToAtPrime_comp_algebraMap {h : B} (hh : h ∉ 𝔪) :
    (awayToAtPrime 𝔪 hh).comp (algebraMap B (Localization.Away h)) =
      algebraMap B (Localization.AtPrime 𝔪) :=
  RingHom.ext (awayToAtPrime_algebraMap 𝔪 hh)

/-- **Local factorization.** A polynomial over `B` with a coefficient `1` factors, over some
`B_h` with `h ∉ 𝔪`, as a unit times a product of powers of polynomials, each with a unit
coefficient and prime over `B_𝔪`. -/
private theorem exists_away_factorization {σ : Type*}
    [UniqueFactorizationMonoid (MvPolynomial σ (Localization.AtPrime 𝔪))]
    (F : MvPolynomial σ B) {e₀ : σ →₀ ℕ} (hF : F.coeff e₀ = 1) :
    ∃ (h : B) (hh : h ∉ 𝔪) (r : ℕ) (P : Fin r → MvPolynomial σ (Localization.Away h))
      (n : Fin r → ℕ) (c : Localization.Away h),
      IsUnit c ∧ MvPolynomial.map (algebraMap B _) F = C c * ∏ j, P j ^ n j ∧
      ∀ j, 0 < n j ∧ Prime (MvPolynomial.map (awayToAtPrime 𝔪 hh) (P j)) ∧
        ∃ e, IsUnit ((P j).coeff e) := by
  classical
  letI := UniqueFactorizationMonoid.normalizationMonoid
    (α := MvPolynomial σ (Localization.AtPrime 𝔪))
  set R := Localization.AtPrime 𝔪
  set FR := MvPolynomial.map (algebraMap B R) F
  have hFR : FR.coeff e₀ = 1 := by rw [coeff_map, hF, map_one]
  have hFR0 : FR ≠ 0 := fun h0 => by
    rw [h0, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hFR
    exact zero_ne_one hFR
  set s := UniqueFactorizationMonoid.normalizedFactors FR
  set r := s.toFinset.card
  let eq := s.toFinset.equivFin
  let q : Fin r → MvPolynomial σ R := fun j => (eq.symm j : MvPolynomial σ R)
  let n : Fin r → ℕ := fun j => s.count (q j)
  have hqs : ∀ j, q j ∈ s := fun j => Multiset.mem_toFinset.mp (eq.symm j).2
  have hprod : s.prod = ∏ j, q j ^ n j := by
    rw [Finset.prod_multiset_count, ← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv eq.symm _ _ fun j => rfl).symm
  obtain ⟨w, hw⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hFR0
  obtain ⟨u₀, hu₀, hwu⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp w.isUnit
  have hFRe : FR = C u₀ * ∏ j, q j ^ n j := by rw [← hw, hwu, hprod, mul_comm]
  -- each factor has a unit coefficient
  have hunitc : ∀ j, ∃ e, IsUnit ((q j).coeff e) := by
    intro j
    by_contra hall
    push Not at hall
    let ρ := MvPolynomial.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) (σ := σ)
    have hρq : ρ (q j) = 0 := by
      ext e
      rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
        Ideal.Quotient.eq_zero_iff_mem]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (hall e)
    have hρF : ρ FR = 0 := by
      rw [hFRe, map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ j)]
      · rw [mul_zero]
      · rw [map_pow, hρq, zero_pow (Multiset.count_ne_zero.mpr (hqs j))]
    have := congrArg (fun p : MvPolynomial _ _ => p.coeff e₀) hρF
    rw [coeff_map, hFR, map_one, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply] at this
    exact one_ne_zero this
  choose ej hej using hunitc
  -- lift everything to some `B_h`
  let fam : Fin r ⊕ (Fin 2 ⊕ Fin r) → MvPolynomial σ R := fun x =>
    match x with
    | .inl j => q j
    | .inr (.inl 0) => C (hu₀.unit : R)
    | .inr (.inl 1) => C ((hu₀.unit⁻¹ : Rˣ) : R)
    | .inr (.inr j) => C (((hej j).unit⁻¹ : Rˣ) : R)
  obtain ⟨h, hh, Ps, hPs⟩ := exists_away_lift_poly 𝔪 fam
  haveI := isDomain_away 𝔪 hh
  have hinj := MvPolynomial.map_injective _ (awayToAtPrime_injective 𝔪 hh) (σ := σ)
  have hcoeff0 : ∀ x, awayToAtPrime 𝔪 hh ((Ps x).coeff 0) = (fam x).coeff 0 := fun x => by
    rw [← coeff_map, hPs]
  set c := (Ps (.inr (.inl 0))).coeff 0
  set c' := (Ps (.inr (.inl 1))).coeff 0
  have hcc' : c * c' = 1 := by
    apply awayToAtPrime_injective 𝔪 hh
    rw [map_mul, map_one, hcoeff0, hcoeff0]
    simp [fam]
  refine ⟨h, hh, r, fun j => Ps (.inl j), n, c, IsUnit.of_mul_eq_one c' hcc', ?_, fun j => ?_⟩
  · apply hinj
    rw [MvPolynomial.map_map, awayToAtPrime_comp_algebraMap, map_mul, map_prod, MvPolynomial.map_C]
    change FR = _
    rw [hFRe]
    congr 1
    · congr 1
      rw [hcoeff0]
      simp [fam]
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [map_pow, hPs]
  · refine ⟨Multiset.count_pos.mpr (hqs j), ?_, ej j, ?_⟩
    · rw [hPs]
      exact UniqueFactorizationMonoid.prime_of_normalized_factor _ (hqs j)
    · refine IsUnit.of_mul_eq_one ((Ps (.inr (.inr j))).coeff 0) ?_
      apply awayToAtPrime_injective 𝔪 hh
      rw [map_mul, map_one, ← coeff_map, hPs, hcoeff0]
      simp [fam]

private theorem exists_dvd_pow_of_forall_algHom {k B' σ : Type*} [Field k] [IsAlgClosed k] [CommRing B']
    [Algebra k B'] [Algebra.FiniteType k B'] [Finite σ] (p q : MvPolynomial σ B')
    (h : ∀ (e : B' →ₐ[k] k) (x : σ → k),
      eval x (map e.toRingHom q) = 0 → eval x (map e.toRingHom p) = 0) :
    ∃ M, q ∣ p ^ M := by
  classical
  haveI : Algebra.FiniteType k (MvPolynomial σ B') := Algebra.FiniteType.trans (S := B')
    inferInstance inferInstance
  haveI : IsJacobsonRing (MvPolynomial σ B') := isJacobsonRing_of_finiteType (A := k)
  have hrad : p ∈ (Ideal.span {q}).radical := by
    rw [← IsJacobsonRing.out' _ (Ideal.radical_isRadical _), Ideal.jacobson, Ideal.mem_sInf]
    rintro J ⟨hJq, hJ⟩
    have hqJ : q ∈ J := hJq (Ideal.le_radical (Ideal.mem_span_singleton_self q))
    letI : Field (MvPolynomial σ B' ⧸ J) := Ideal.Quotient.field J
    haveI : Module.Finite k (MvPolynomial σ B' ⧸ J) :=
      finite_of_finite_type_of_isJacobsonRing k _
    haveI : Algebra.IsIntegral k (MvPolynomial σ B' ⧸ J) := Algebra.IsIntegral.of_finite k _
    have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
      (K := MvPolynomial σ B' ⧸ J)
    let ε : MvPolynomial σ B' →ₐ[k] k :=
      ((AlgEquiv.ofBijective (Algebra.ofId k _) hbij).symm.toAlgHom).comp
        (Ideal.Quotient.mkₐ k J)
    have hεJ : ∀ f, ε f = 0 ↔ f ∈ J := fun f => by
      change (AlgEquiv.ofBijective (Algebra.ofId k _) hbij).symm (Ideal.Quotient.mk J f) = 0 ↔ _
      rw [EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    let e : B' →ₐ[k] k := ε.comp (IsScalarTower.toAlgHom k B' (MvPolynomial σ B'))
    have hεeval : ∀ f, ε f = eval (fun i => ε (X i)) (map e.toRingHom f) := fun f => by
      rw [MvPolynomial.eval_map]
      have hext : ε.toRingHom = eval₂Hom e.toRingHom (fun i => ε (X i)) :=
        MvPolynomial.ringHom_ext (fun r => by simp [e, MvPolynomial.algebraMap_eq])
          (fun i => by simp)
      exact (RingHom.congr_fun hext f).trans (by rw [coe_eval₂Hom])
    rw [← hεJ, hεeval]
    rw [← hεJ, hεeval] at hqJ
    exact h e _ hqJ
  obtain ⟨M, hM⟩ := hrad
  exact ⟨M, Ideal.mem_span_singleton.mp hM⟩

private theorem finiteType_away {k : Type*} [Field k] [Algebra k B] [Algebra.FiniteType k B] (h : B) :
    Algebra.FiniteType k (Localization.Away h) := by
  haveI := IsLocalization.Away.finitePresentation (S := Localization.Away h) h
  exact Algebra.FiniteType.trans (S := B) inferInstance inferInstance

/-- **Comparison with a prime.** Let `P, Ψ` be polynomials over a finitely generated `k`-domain
`B`, `P` prime over the local ring `B_𝔪` and `Ψ` nonzero there. If at every `k`-point of `B` the
zero set of `Ψ` lies in that of `P`, then over some `B_g`, `g ∉ 𝔪`, `Ψ` is a unit times a power
of `P`. -/
private theorem exists_eq_C_mul_pow {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ] [Algebra k B]
    [Algebra.FiniteType k B] [UniqueFactorizationMonoid (MvPolynomial σ (Localization.AtPrime 𝔪))]
    (P Ψ : MvPolynomial σ B) (hP : Prime (MvPolynomial.map (algebraMap B (Localization.AtPrime 𝔪)) P))
    (hΨ : MvPolynomial.map (algebraMap B (Localization.AtPrime 𝔪)) Ψ ≠ 0)
    (h : ∀ (e : B →ₐ[k] k) (x : σ → k),
      eval x (MvPolynomial.map e.toRingHom Ψ) = 0 → eval x (MvPolynomial.map e.toRingHom P) = 0) :
    ∃ (g : B) (hg : g ∉ 𝔪) (s : ℕ) (c : Localization.Away g), IsUnit c ∧
      MvPolynomial.map (algebraMap B _) Ψ = C c * (MvPolynomial.map (algebraMap B _) P) ^ s := by
  classical
  letI := UniqueFactorizationMonoid.normalizationMonoid
    (α := MvPolynomial σ (Localization.AtPrime 𝔪))
  set R := Localization.AtPrime 𝔪
  set ΨR := MvPolynomial.map (algebraMap B R) Ψ
  set PR := MvPolynomial.map (algebraMap B R) P
  have hfactor : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors ΨR, Associated Q PR := by
    intro Q hQ
    have hQirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
    have hQprime := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    obtain ⟨H, hH⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ
    obtain ⟨h₁, hh₁, L, hL⟩ := exists_away_lift_poly 𝔪 (fun b : Bool => if b then Q else H)
    haveI := isDomain_away 𝔪 hh₁
    haveI : Algebra.FiniteType k (Localization.Away h₁) := finiteType_away h₁
    have hinj := MvPolynomial.map_injective _ (awayToAtPrime_injective 𝔪 hh₁) (σ := σ)
    have hcomp : ∀ f : MvPolynomial σ B, MvPolynomial.map (awayToAtPrime 𝔪 hh₁)
        (MvPolynomial.map (algebraMap B _) f) = MvPolynomial.map (algebraMap B R) f := fun f => by
      rw [MvPolynomial.map_map, awayToAtPrime_comp_algebraMap]
    have hΨL : MvPolynomial.map (algebraMap B (Localization.Away h₁)) Ψ = L true * L false := by
      apply hinj
      rw [hcomp, map_mul, hL, hL]
      simpa using hH
    have key : ∀ (e : Localization.Away h₁ →ₐ[k] k) (f : MvPolynomial σ B),
        MvPolynomial.map e.toRingHom (MvPolynomial.map (algebraMap B _) f) =
          MvPolynomial.map (e.comp (IsScalarTower.toAlgHom k B (Localization.Away h₁))).toRingHom f :=
      fun e f => by rw [MvPolynomial.map_map]; rfl
    obtain ⟨M, hM⟩ := exists_dvd_pow_of_forall_algHom (k := k)
      (MvPolynomial.map (algebraMap B (Localization.Away h₁)) P) (L true) (fun e x hx => by
        rw [key]
        refine h _ x ?_
        rw [← key, hΨL, map_mul, eval_mul, hx, zero_mul])
    have hQP : Q ∣ PR ^ M := by
      have := map_dvd (MvPolynomial.map (awayToAtPrime 𝔪 hh₁)) hM
      rwa [hL, map_pow, hcomp] at this
    exact hQirr.associated_of_dvd hP.irreducible (hQprime.dvd_of_dvd_pow hQP)
  set m := (UniqueFactorizationMonoid.normalizedFactors ΨR).card
  have hs : UniqueFactorizationMonoid.normalizedFactors ΨR = Multiset.replicate m (normalize PR) :=
    Multiset.eq_replicate.mpr ⟨rfl, fun Q hQ =>
      (UniqueFactorizationMonoid.normalize_normalized_factor Q hQ).symm.trans
        (normalize_eq_normalize_iff_associated.mpr (hfactor Q hQ))⟩
  obtain ⟨w, hw⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hΨ
  rw [hs, Multiset.prod_replicate, normalize_apply, mul_pow] at hw
  have hunit : IsUnit ((↑(normUnit PR) : MvPolynomial σ R) ^ m * w) :=
    ((Units.isUnit _).pow m).mul w.isUnit
  obtain ⟨u₀, hu₀, hwu⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit
  have hΨe : ΨR = C u₀ * PR ^ m := by rw [← hw, mul_assoc, hwu, mul_comm]
  obtain ⟨g, hg, b, hb⟩ := exists_away_lift 𝔪 (fun t : Bool => if t then (hu₀.unit : R)
    else ((hu₀.unit⁻¹ : Rˣ) : R))
  haveI := isDomain_away 𝔪 hg
  refine ⟨g, hg, m, b true, IsUnit.of_mul_eq_one (b false) ?_, ?_⟩
  · apply awayToAtPrime_injective 𝔪 hg
    rw [map_mul, map_one, hb, hb]
    simp
  · apply MvPolynomial.map_injective _ (awayToAtPrime_injective 𝔪 hg)
    rw [MvPolynomial.map_map, awayToAtPrime_comp_algebraMap, map_mul, map_pow,
      MvPolynomial.map_map, awayToAtPrime_comp_algebraMap, MvPolynomial.map_C, hb]
    simpa using hΨe

/-- The maximal ideal `𝔪 B_g` of a localization `B_g`, `g ∉ 𝔪`. -/
private theorem isPrime_map_away {g : B} (hg : g ∉ 𝔪) :
    (Ideal.map (algebraMap B (Localization.Away g)) 𝔪).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) _ 𝔪 ‹_›
    ((Ideal.disjoint_powers_iff_notMem g (Ideal.IsPrime.isRadical ‹_›)).mpr hg)

private theorem comap_map_away {g : B} (hg : g ∉ 𝔪) :
    Ideal.comap (algebraMap B (Localization.Away g))
      (Ideal.map (algebraMap B (Localization.Away g)) 𝔪) = 𝔪 :=
  IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers g) _ ‹_›
    ((Ideal.disjoint_powers_iff_notMem g (Ideal.IsPrime.isRadical ‹_›)).mpr hg)

/-- Primality over the local ring is unchanged by passing to a localization `B_g`, `g ∉ 𝔪`. -/
private theorem prime_map_atPrime_away {σ : Type*} {g : B} (hg : g ∉ 𝔪) (P : MvPolynomial σ B)
    (hP : Prime (MvPolynomial.map (algebraMap B (Localization.AtPrime 𝔪)) P)) :
    haveI := isPrime_map_away 𝔪 hg
    Prime (MvPolynomial.map (algebraMap (Localization.Away g)
      (Localization.AtPrime (Ideal.map (algebraMap B (Localization.Away g)) 𝔪)))
        (MvPolynomial.map (algebraMap B (Localization.Away g)) P)) := by
  haveI := isPrime_map_away 𝔪 hg
  set 𝔪' := Ideal.map (algebraMap B (Localization.Away g)) 𝔪
  haveI : IsLocalization 𝔪.primeCompl (Localization.AtPrime 𝔪') := by
    have h1 := IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers g) 𝔪'
    have hc : (Ideal.comap (algebraMap B (Localization (Submonoid.powers g))) 𝔪').primeCompl =
        𝔪.primeCompl := by
      ext x
      rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff]
      exact not_congr (by rw [comap_map_away 𝔪 hg])
    unfold IsLocalization.AtPrime at h1
    rwa [hc] at h1
  let e : Localization.AtPrime 𝔪 ≃ₐ[B] Localization.AtPrime 𝔪' :=
    IsLocalization.algEquiv 𝔪.primeCompl _ _
  have he : (e : Localization.AtPrime 𝔪 →+* Localization.AtPrime 𝔪').comp
      (algebraMap B _) = (algebraMap (Localization.Away g) (Localization.AtPrime 𝔪')).comp
        (algebraMap B _) := by
    ext b
    simp [IsScalarTower.algebraMap_apply B (Localization.Away g) (Localization.AtPrime 𝔪')]
  rw [MvPolynomial.map_map, ← he, ← MvPolynomial.map_map]
  exact (MulEquiv.prime_iff (MvPolynomial.mapAlgEquiv σ e).toMulEquiv).mpr hP

end LocalAlgebra

section SchemeBases

private theorem isDedekindDomain_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) [IsDedekindDomain R] : IsDedekindDomain S :=
  haveI : IsDomain S := e.symm.toMulEquiv.isDomain
  haveI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  haveI : Ring.DimensionLEOne S := Ring.DimensionLEOne.of_ringEquiv (id e.symm)
  haveI : IsIntegrallyClosed S := IsIntegrallyClosed.of_equiv e
  {}

private theorem isDedekindDomain_of_isIntegrallyClosed {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.DimensionLEOne R] [IsIntegrallyClosed R] : IsDedekindDomain R :=
  {}

private theorem dimensionLEOne_of_ringKrullDim_le {R : Type*} [CommRing R] [IsDomain R]
    (h : ringKrullDim R ≤ 1) : Ring.DimensionLEOne R := by
  haveI : Ring.KrullDimLE 1 R := ⟨by exact_mod_cast h⟩
  refine ⟨fun {p} hp hpp => ?_⟩
  rcases Ring.krullDimLE_one_iff.mp inferInstance p hpp with h1 | h1
  · exfalso
    rw [IsDomain.minimalPrimes_eq_singleton_bot R] at h1
    exact hp h1
  · exact h1

private theorem isNormal_of_isOpenImmersion {U X' : Scheme.{u}} (f : U ⟶ X') [IsOpenImmersion f]
    [IsNormal X'] : IsNormal U := by
  have hiso : ∀ x, IsIso (f.stalkMap x) := fun x =>
    inferInstanceAs (IsIso (f.toLRSHom.stalkMap x))
  constructor
  · intro x
    haveI := IsNormal.stalk_isDomain (X := X') (f x)
    haveI := hiso x
    exact (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain
  · intro x
    haveI := IsNormal.stalk_normal (X := X') (f x)
    haveI := hiso x
    exact IsIntegrallyClosed.of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

private theorem isIntegrallyClosed_of_isNormal_spec (R : Type u) [CommRing R] [IsDomain R]
    [IsNormal (Spec (.of R))] : IsIntegrallyClosed R := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ _ => ?_
  have h := IsNormal.stalk_normal (X := Spec (.of R)) ⟨p, inferInstance⟩
  exact @IsIntegrallyClosed.of_equiv _ _ _ _
    (StructureSheaf.stalkIso R ⟨p, inferInstance⟩).toRingEquiv.symm h

end SchemeBases

section VertexLocus

/-! ### The vertex locus

For a form `F = ∑_b c_b (u, v)^{m_b}` on pairs of hyperplanes of `ℙᴺ_k`, with coefficient vector
`c` a point of `ℙ^ι_k`, the *vertex locus* is the set of pairs `([c], x) ∈ ℙ^ι_k ×ₖ ℙᴺ_k` such that
`F(u, v) = 0` for all hyperplanes `u, v` through `x`. It is closed: on the chart
`D₊(x_{b₀}) ×ₖ D₊(x_l) = Spec (k[xᵦ]⁰_{x_{b₀}} ⊗ₖ k[x_j]⁰_{x_l})` it is cut out by the values
`F(P w, P w')`, where `P w = w - (w · x / x_l) e_l` is the projection onto the hyperplanes
through `x`. -/

open HomogeneousLocalization MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {ι : Type*}

/-- The `k`-algebra structure on the degree-zero localization `k[xᵢ]⁰_f`. -/
private noncomputable abbrev awayAlgebra (f : MvPolynomial ι k) :
    Algebra k (Away (homogeneousSubmodule ι k) f) :=
  ((fromZeroRingHom (homogeneousSubmodule ι k) (Submonoid.powers f)).comp
    (algebraMap k (homogeneousSubmodule ι k 0))).toAlgebra

attribute [local instance] awayAlgebra

/-- Evaluation `k[xᵢ]⁰_f → k` at a vector `c` with `f(c) ≠ 0`. -/
private noncomputable def awayEval (f : MvPolynomial ι k) (c : ι → k) (hc : eval c f ≠ 0) :
    Away (homogeneousSubmodule ι k) f →ₐ[k] k :=
  { ((IsLocalization.Away.lift f (g := MvPolynomial.eval c) hc.isUnit).comp
      (algebraMap (Away (homogeneousSubmodule ι k) f) (Localization.Away f))) with
    commutes' := fun r => by
      change IsLocalization.Away.lift f (g := MvPolynomial.eval c) hc.isUnit (Localization.mk
        ((algebraMap k (homogeneousSubmodule ι k 0) r : homogeneousSubmodule ι k 0) :
          MvPolynomial ι k) 1) = r
      rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift, IsLocalization.lift_eq]
      simp [SetLike.GradeZero.coe_algebraMap] }

private theorem awayEval_mk (f : MvPolynomial ι k) (c : ι → k) (hc : eval c f ≠ 0)
    (z : NumDenSameDeg (homogeneousSubmodule ι k) (Submonoid.powers f)) :
    awayEval f c hc (HomogeneousLocalization.mk z) = eval c z.num * (eval c z.den)⁻¹ := by
  change IsLocalization.Away.lift f (g := MvPolynomial.eval c) hc.isUnit
    (Localization.mk (z.num : MvPolynomial ι k)
    ⟨z.den, z.den_mem⟩) = _
  rw [Localization.mk_eq_mk', IsLocalization.Away.lift, IsLocalization.lift_mk']
  simp only [Units.val_inv_eq_inv_val]
  rfl

private theorem X_mem_one' (b : ι) : (X b : MvPolynomial ι k) ∈ homogeneousSubmodule ι k 1 :=
  isHomogeneous_X k b

/-- At a point `𝔮` of a chart `D₊(f)`, `f` of degree one, whose homogeneous prime is the point
`[c]`, the prime `𝔮` is the kernel of evaluation at `c`. -/
private theorem mem_iff_awayEval_eq_zero {f : MvPolynomial ι k}
    (hf : f ∈ homogeneousSubmodule ι k 1) (c : ι → k) (hc : eval c f ≠ 0)
    (𝔮 : Spec (.of (Away (homogeneousSubmodule ι k) f)))
    (h : ∀ (n : ℕ) (g : MvPolynomial ι k), g.IsHomogeneous n →
      (g ∈ ((Proj.awayι (homogeneousSubmodule ι k) f hf one_pos) 𝔮).asHomogeneousIdeal ↔
        eval c g = 0))
    (α : Away (homogeneousSubmodule ι k) f) :
    α ∈ 𝔮.asIdeal ↔ awayEval f c hc α = 0 := by
  obtain ⟨z, rfl⟩ := mk_surjective α
  rw [MMP.Chow.mk_mem_iff_num_mem_awayι _ hf one_pos, h _ _ z.num.2, awayEval_mk]
  obtain ⟨n, hn⟩ := z.den_mem
  rw [← hn]
  simp [hc]

/-- A prime of `A ⊗ₖ B` containing the kernels of two `k`-points `e_A`, `e_B` is the kernel of
`e_A ⊗ e_B`. -/
private theorem mem_iff_lift_eq_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra k A]
    [Algebra k B] (eA : A →ₐ[k] k) (eB : B →ₐ[k] k) (𝔭 : Ideal (TensorProduct k A B))
    [𝔭.IsPrime] (hA : ∀ a, eA a = 0 → Algebra.TensorProduct.includeLeft (S := k) a ∈ 𝔭)
    (hB : ∀ b, eB b = 0 → Algebra.TensorProduct.includeRight b ∈ 𝔭) (t : TensorProduct k A B) :
    t ∈ 𝔭 ↔ Algebra.TensorProduct.lift eA eB (fun _ _ => .all _ _) t = 0 := by
  set e := Algebra.TensorProduct.lift eA eB (fun _ _ => .all _ _)
  have key : ∀ t, t - algebraMap k _ (e t) ∈ 𝔭 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have h1 := hA (a - algebraMap k A (eA a)) (by simp)
      have h2 := hB (b - algebraMap k B (eB b)) (by simp)
      have : a ⊗ₜ[k] b - algebraMap k _ (e (a ⊗ₜ[k] b)) =
          Algebra.TensorProduct.includeLeft (S := k) (a - algebraMap k A (eA a)) *
            Algebra.TensorProduct.includeRight b +
          algebraMap k _ (eA a) * Algebra.TensorProduct.includeRight
            (b - algebraMap k B (eB b)) := by
        simp only [map_sub, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, e,
          Algebra.TensorProduct.tmul_mul_tmul, AlgHom.commutes, sub_mul, mul_sub, one_mul,
          mul_one, Algebra.TensorProduct.algebraMap_apply, map_mul]
        abel
      rw [this]
      exact 𝔭.add_mem (𝔭.mul_mem_right _ h1) (𝔭.mul_mem_left _ h2)
    | add t t' ht ht' =>
      have := 𝔭.add_mem ht ht'
      rwa [map_add, map_add, add_sub_add_comm]
  constructor
  · intro ht
    by_contra hne
    have := 𝔭.sub_mem ht (key t)
    rw [sub_sub_cancel] at this
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ this
      ((IsUnit.mk0 _ hne).map (algebraMap k _)))
  · intro ht
    simpa [ht] using key t

section Charts

variable {ι : Type u} {N : ℕ}

/-- The chart `D₊(f) = Spec A⁰_f` of `ℙ^ι_k` lies over `Spec k`. -/
private theorem awayι_comp_toSpec {f : MvPolynomial ι k} {n : ℕ}
    (hf : f ∈ homogeneousSubmodule ι k n) (hn : 0 < n) :
    Proj.awayι (homogeneousSubmodule ι k) f hf hn ≫ Intersection.ProjSpace.toSpec k ι =
      Spec.map (CommRingCat.ofHom (algebraMap k (Away (homogeneousSubmodule ι k) f))) := by
  rw [Intersection.ProjSpace.toSpec, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

private theorem awayι_projToSpecCoeff (l : Fin (N + 1)) :
    Proj.awayι (polyGrading k N) (X l) (X_mem_one' l) one_pos ≫ projToSpecCoeff k N =
      Spec.map (CommRingCat.ofHom (algebraMap k (Away (polyGrading k N) (X l)))) := by
  rw [projToSpecCoeff, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  apply Subtype.ext
  have h : (MvPolynomial.C r : MvPolynomial (Fin (N + 1)) k) ∈ polyGrading k N 0 :=
    MvPolynomial.isHomogeneous_C _ r
  simp [DirectSum.decompose_of_mem_same _ h, SetLike.GradeZero.coe_algebraMap]
  rfl

/-- The chart `Spec (k[xᵦ]⁰_{x_{b₀}} ⊗ₖ k[x_j]⁰_{x_l})` of `ℙ^ι_k ×ₖ ℙᴺ_k`. -/
private noncomputable def chartι (b₀ : ι) (l : Fin (N + 1)) :
    Spec (.of (TensorProduct k (Away (homogeneousSubmodule ι k) (X b₀))
      (Away (polyGrading k N) (X l)))) ⟶
      pullback (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) :=
  (pullbackSpecIso k _ _).inv ≫
    pullback.map _ _ _ _ (Proj.awayι _ _ (X_mem_one' b₀) one_pos)
      (Proj.awayι _ _ (X_mem_one' l) one_pos) (𝟙 _)
      (by rw [Category.comp_id, awayι_comp_toSpec]) (by rw [Category.comp_id, awayι_projToSpecCoeff])

private theorem isOpenEmbedding_chartι (b₀ : ι) (l : Fin (N + 1)) :
    Topology.IsOpenEmbedding (chartι (k := k) b₀ l) := by
  have : IsOpenImmersion (chartι (k := k) b₀ l) := by unfold chartι; infer_instance
  exact (chartι (k := k) b₀ l).isOpenEmbedding

private theorem chartι_fst (b₀ : ι) (l : Fin (N + 1)) :
    chartι (k := k) b₀ l ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        Proj.awayι _ _ (X_mem_one' b₀) one_pos := by
  rw [chartι, Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]

private theorem chartι_snd (b₀ : ι) (l : Fin (N + 1)) :
    chartι (k := k) b₀ l ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        Proj.awayι (polyGrading k N) _ (X_mem_one' l) one_pos := by
  rw [chartι, Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd]
  rfl

/-- The chart coordinate `x_b / x_{b₀}` of `D₊(x_{b₀})`. -/
private noncomputable def chartCoord {ι : Type*} (b₀ b : ι) : Away (homogeneousSubmodule ι k) (X b₀) :=
  HomogeneousLocalization.mk ⟨1, ⟨X b, X_mem_one' b⟩, ⟨X b₀, X_mem_one' b₀⟩,
    Submonoid.mem_powers _⟩

private theorem awayEval_chartCoord {ι : Type*} (b₀ b : ι) (c : ι → k) (hc : eval c (X b₀) ≠ 0) :
    awayEval (X b₀) c hc (chartCoord b₀ b) = c b * (c b₀)⁻¹ := by
  rw [chartCoord, awayEval_mk]
  simp

variable [Fintype ι] (m : ι → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ)

/-- The projection `w ↦ w - (w · x / x_l) e_l` onto the hyperplane orthogonal to the point `x` of
the chart `D₊(x_l)`, with coefficients in `k[x_j]⁰_{x_l}`. -/
private noncomputable def projPerp (l : Fin (N + 1)) (w : Fin (N + 1) → k) :
    Fin (N + 1) → Away (polyGrading k N) (X l) := fun j =>
  algebraMap k _ (w j) - if j = l then ∑ i, algebraMap k _ (w i) * chartCoord l i else 0

/-- The form `G = ∑_b c_b ∏ⱼ (v, v')^{m_b}` with coefficients `c`, evaluated at `(v, v')`. -/
private def formEval (c : ι → k) (v v' : Fin (N + 1) → k) : k :=
  ∑ b, c b * ∏ j, (Sum.elim v v' j) ^ (m b j)

/-- The elements of the chart ring whose common zeros are the pairs `(F, x)` with `F` vanishing
on all pairs of hyperplanes through `x`. -/
private noncomputable def vertexElem (b₀ : ι) (l : Fin (N + 1)) (w w' : Fin (N + 1) → k) :
    TensorProduct k (Away (homogeneousSubmodule ι k) (X b₀)) (Away (polyGrading k N) (X l)) :=
  ∑ b, Algebra.TensorProduct.includeLeft (S := k) (chartCoord b₀ b) *
    Algebra.TensorProduct.includeRight
      (∏ j, (Sum.elim (projPerp l w) (projPerp l w') j) ^ (m b j))

/-- The vertex locus in the chart `(b₀, l)`. -/
private def vertexChart (b₀ : ι) (l : Fin (N + 1)) :
    Set (Spec (.of (TensorProduct k (Away (homogeneousSubmodule ι k) (X b₀))
      (Away (polyGrading k N) (X l))))) :=
  PrimeSpectrum.zeroLocus (Set.range fun ww : (Fin (N + 1) → k) × (Fin (N + 1) → k) =>
    vertexElem m b₀ l ww.1 ww.2)

/-- The vertex locus `{(F, x) | F(u, v) = 0 whenever u(x) = v(x) = 0}` in `ℙ^ι_k ×ₖ ℙᴺ_k`. -/
private def vertexLocus :
    Set (pullback (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) : Scheme.{u}) :=
  {z | ∀ b₀ l, z ∈ Set.range (chartι (k := k) b₀ l) → z ∈ chartι b₀ l '' vertexChart m b₀ l}

private theorem isClosed_vertexLocus : IsClosed (vertexLocus (k := k) m) := by
  have : (vertexLocus (k := k) m)ᶜ = ⋃ b₀, ⋃ l, chartι b₀ l '' (vertexChart m b₀ l)ᶜ := by
    ext z
    simp only [vertexLocus, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, Set.mem_iUnion,
      Set.mem_image, Set.mem_range]
    refine exists_congr fun b₀ => exists_congr fun l => ⟨?_, ?_⟩
    · rintro ⟨⟨𝔭, rfl⟩, h⟩
      exact ⟨𝔭, fun h' => h ⟨𝔭, h', rfl⟩, rfl⟩
    · rintro ⟨𝔭, h, rfl⟩
      refine ⟨⟨𝔭, rfl⟩, ?_⟩
      rintro ⟨𝔭', h', e⟩
      exact h ((isOpenEmbedding_chartι (k := k) b₀ l).injective e ▸ h')
  rw [← isOpen_compl_iff, this]
  exact isOpen_iUnion fun b₀ => isOpen_iUnion fun l =>
    (isOpenEmbedding_chartι (k := k) b₀ l).isOpenMap _
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

/-- The projection `w ↦ w - ((w · c') / c'_l) e_l` onto the hyperplane `c'^⊥`. -/
private def perpProj (c' : Fin (N + 1) → k) (l : Fin (N + 1)) (w : Fin (N + 1) → k) : Fin (N + 1) → k :=
  fun j => w j - if j = l then (∑ i, w i * c' i) * (c' l)⁻¹ else 0

private theorem perpProj_dotProduct {c' : Fin (N + 1) → k} {l : Fin (N + 1)} (hc' : c' l ≠ 0)
    (w : Fin (N + 1) → k) : perpProj c' l w ⬝ᵥ c' = 0 := by
  simp only [perpProj, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp
  simp

private theorem perpProj_of_dotProduct {c' : Fin (N + 1) → k} {l : Fin (N + 1)} {w : Fin (N + 1) → k}
    (hw : w ⬝ᵥ c' = 0) : perpProj c' l w = w := by
  funext j
  have : ∑ i, w i * c' i = 0 := hw
  simp [perpProj, this]

private theorem awayEval_projPerp (l : Fin (N + 1)) (c' : Fin (N + 1) → k) (hc' : eval c' (X l) ≠ 0)
    (w : Fin (N + 1) → k) (j : Fin (N + 1)) :
    awayEval (X l) c' hc' (projPerp l w j) = perpProj c' l w j := by
  simp only [projPerp, perpProj, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]
  split_ifs <;> simp_all [map_sum, map_mul, awayEval_chartCoord, Finset.sum_mul, mul_assoc]

private theorem mem_vertexChart_iff {b₀ : ι} {l : Fin (N + 1)}
    (𝔭 : Spec (.of (TensorProduct k (Away (homogeneousSubmodule ι k) (X b₀))
      (Away (polyGrading k N) (X l))))) (c : ι → k) (c' : Fin (N + 1) → k) (hc : c b₀ ≠ 0)
    (hc' : c' l ≠ 0)
    (h1 : ∀ (n : ℕ) (g : MvPolynomial ι k), g.IsHomogeneous n →
      (g ∈ ((Proj.awayι (homogeneousSubmodule ι k) (X b₀) (X_mem_one' b₀) one_pos)
        ((Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) 𝔭)
          ).asHomogeneousIdeal ↔ eval c g = 0))
    (h2 : ∀ (n : ℕ) (g : MvPolynomial (Fin (N + 1)) k), g.IsHomogeneous n →
      (g ∈ ((Proj.awayι (polyGrading k N) (X l) (X_mem_one' l) one_pos)
        ((Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)) 𝔭)
          ).asHomogeneousIdeal ↔ eval c' g = 0)) :
    𝔭 ∈ vertexChart m b₀ l ↔
      ∀ v v' : Fin (N + 1) → k, v ⬝ᵥ c' = 0 → v' ⬝ᵥ c' = 0 → formEval m c v v' = 0 := by
  have hcX : eval c (X b₀) ≠ 0 := by simpa using hc
  have hcX' : eval c' (X l) ≠ 0 := by simpa using hc'
  set eA := awayEval (X b₀) c hcX
  set eB := awayEval (X l) c' hcX'
  have hA : ∀ a, eA a = 0 → Algebra.TensorProduct.includeLeft (S := k) a ∈ 𝔭.asIdeal :=
    fun a ha => (mem_iff_awayEval_eq_zero (X_mem_one' b₀) c hcX _ h1 a).mpr ha
  have hB : ∀ b, eB b = 0 → Algebra.TensorProduct.includeRight b ∈ 𝔭.asIdeal :=
    fun b hb => (mem_iff_awayEval_eq_zero (X_mem_one' l) c' hcX' _ h2 b).mpr hb
  have he : ∀ w w', Algebra.TensorProduct.lift eA eB (fun _ _ => .all _ _)
      (vertexElem m b₀ l w w') = (c b₀)⁻¹ * formEval m c (perpProj c' l w) (perpProj c' l w') := by
    intro w w'
    simp only [vertexElem, formEval, map_sum, map_mul, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one,
      mul_one, one_mul, map_prod, map_pow, Finset.mul_sum, Fintype.prod_sum_type, Sum.elim_inl,
      Sum.elim_inr]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show eA (chartCoord b₀ b) = c b * (c b₀)⁻¹ from awayEval_chartCoord _ _ _ _]
    simp only [eB, awayEval_projPerp]
    ring
  change Set.range _ ⊆ SetLike.coe 𝔭.asIdeal ↔ _
  rw [Set.range_subset_iff]
  simp only [SetLike.mem_coe, Prod.forall]
  have key : ∀ t, t ∈ 𝔭.asIdeal ↔ Algebra.TensorProduct.lift eA eB (fun _ _ => .all _ _) t = 0 :=
    fun t => @mem_iff_lift_eq_zero k _ _ _ _ _ _ _ eA eB 𝔭.asIdeal 𝔭.isPrime hA hB t
  simp_rw [key, he]
  constructor
  · intro h v v' hv hv'
    have := h v v'
    rw [perpProj_of_dotProduct hv, perpProj_of_dotProduct hv'] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero hc)
  · intro h w w'
    rw [h _ _ (perpProj_dotProduct hc' w) (perpProj_dotProduct hc' w'), mul_zero]

private theorem mem_range_chartι_iff (b₀ : ι) (l : Fin (N + 1))
    (z : (pullback (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) : Scheme.{u})) :
    z ∈ Set.range (chartι (k := k) b₀ l) ↔
      (X b₀ : MvPolynomial ι k) ∉ (pullback.fst (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) z).asHomogeneousIdeal ∧
        (X l : MvPolynomial (Fin (N + 1)) k) ∉ (pullback.snd (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) z).asHomogeneousIdeal := by
  have hr : Set.range (chartι (k := k) b₀ l) = Set.range (pullback.map _ _ _ _
      (Proj.awayι _ _ (X_mem_one' b₀) one_pos) (Proj.awayι (polyGrading k N) _ (X_mem_one' l)
        one_pos) (𝟙 _) (by rw [Category.comp_id, awayι_comp_toSpec])
        (by rw [Category.comp_id, awayι_projToSpecCoeff])) := by
    have hsurj : Function.Surjective (pullbackSpecIso k (Away (homogeneousSubmodule ι k) (X b₀))
        (Away (polyGrading k N) (X l))).inv := fun x =>
      ⟨(pullbackSpecIso k _ _).hom x, by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩
    rw [chartι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
      Set.image_univ]
  rw [hr, Scheme.Pullback.range_map]
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι,
    Proj.opensRange_awayι]
  rfl

private theorem mem_vertexLocus_iff
    (z : (pullback (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) : Scheme.{u}))
    (c : ι → k) (c' : Fin (N + 1) → k) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h1 : ∀ (n : ℕ) (g : MvPolynomial ι k), g.IsHomogeneous n →
      (g ∈ (pullback.fst (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) z).asHomogeneousIdeal ↔ eval c g = 0))
    (h2 : ∀ (n : ℕ) (g : MvPolynomial (Fin (N + 1)) k), g.IsHomogeneous n →
      (g ∈ (pullback.snd (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) z).asHomogeneousIdeal ↔ eval c' g = 0)) :
    z ∈ vertexLocus (k := k) m ↔
      ∀ v v' : Fin (N + 1) → k, v ⬝ᵥ c' = 0 → v' ⬝ᵥ c' = 0 → formEval m c v v' = 0 := by
  have chart : ∀ b₀ l 𝔭, chartι (k := k) b₀ l 𝔭 = z →
      (𝔭 ∈ vertexChart m b₀ l ↔
        ∀ v v' : Fin (N + 1) → k, v ⬝ᵥ c' = 0 → v' ⬝ᵥ c' = 0 → formEval m c v v' = 0) := by
    intro b₀ l 𝔭 h𝔭
    have hf : pullback.fst (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) z = Proj.awayι _ _ (X_mem_one' b₀) one_pos
        ((Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) 𝔭) := by
      rw [← h𝔭, ← Scheme.Hom.comp_apply, chartι_fst, Scheme.Hom.comp_apply]
    have hs : pullback.snd (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) z = Proj.awayι (polyGrading k N) _ (X_mem_one' l) one_pos
        ((Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)) 𝔭) := by
      rw [← h𝔭, ← Scheme.Hom.comp_apply, chartι_snd, Scheme.Hom.comp_apply]
    have hz := (mem_range_chartι_iff b₀ l z).mp ⟨𝔭, h𝔭⟩
    have hcb : c b₀ ≠ 0 := fun h0 => hz.1 ((h1 1 _ (isHomogeneous_X k b₀)).mpr (by simpa using h0))
    have hcl : c' l ≠ 0 := fun h0 => hz.2 ((h2 1 _ (isHomogeneous_X k l)).mpr (by simpa using h0))
    exact mem_vertexChart_iff m 𝔭 c c' hcb hcl (fun n g hg => hf ▸ h1 n g hg)
      (fun n g hg => hs ▸ h2 n g hg)
  constructor
  · intro hz
    obtain ⟨b₀, hb₀⟩ := Function.ne_iff.mp hc
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hc'
    have hr : z ∈ Set.range (chartι (k := k) b₀ l) := (mem_range_chartι_iff b₀ l z).mpr
      ⟨fun h => hb₀ (by simpa using (h1 1 _ (isHomogeneous_X k b₀)).mp h),
        fun h => hl (by simpa using (h2 1 _ (isHomogeneous_X k l)).mp h)⟩
    obtain ⟨𝔭, h𝔭, rfl⟩ := hz b₀ l hr
    exact (chart b₀ l 𝔭 rfl).mp h𝔭
  · intro h b₀ l ⟨𝔭, h𝔭⟩
    exact ⟨𝔭, (chart b₀ l 𝔭 h𝔭).mpr h, h𝔭⟩

end Charts

end VertexLocus

section LineRoots

/-! ### Roots of a form along a line

For a form `F = ∑_b c_b x^{m_b}` on `kˢ` with coefficient vector `[c] ∈ ℙ^ι_k`, all monomials of
degree `D`, the values of `F` along the line `x = p + t w` are the values at `[c]` of the linear
forms `L_t = ∑_b (p + t w)^{m_b} X_b = ∑_{n ≤ D} tⁿ Lₙ`, whose top coefficient is `L_D = L(w)`.
On the chart `D₊(L(w))` the fractions `Lₙ / L(w)` are the coefficients of a monic polynomial
`g` of degree `D` in `t`, whose roots over a point `[c]` are the `t` with `F(p + t w) = 0`. -/

open HomogeneousLocalization MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra awayAlgebra

variable {k : Type u} [Field k] {ι : Type*} [Fintype ι] {σ : Type*} [Fintype σ]

/-- The linear form `∑_b x^{m_b} X_b` on `ℙ^ι`, the value at `x` of the form with coefficients
`X_b` and monomials `x^{m_b}`. -/
private noncomputable def formLin (m : ι → σ →₀ ℕ) (x : σ → k) : MvPolynomial ι k :=
  ∑ b, C (∏ j, x j ^ m b j) * X b

private theorem isHomogeneous_formLin (m : ι → σ →₀ ℕ) (x : σ → k) :
    (formLin m x).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun b _ => isHomogeneous_C_mul_X _ b

private theorem eval_formLin (m : ι → σ →₀ ℕ) (x : σ → k) (c : ι → k) :
    eval c (formLin m x) = ∑ b, c b * ∏ j, x j ^ m b j := by
  simp [formLin, mul_comm]

/-- The monomial `x^e` along the line `x = p + t w`, as a polynomial in `t`. -/
private noncomputable def lineMono (p w : σ → k) (e : σ →₀ ℕ) : Polynomial k :=
  ∏ j, (Polynomial.C (p j) + Polynomial.C (w j) * Polynomial.X) ^ e j

private theorem eval_lineMono (p w : σ → k) (e : σ →₀ ℕ) (t : k) :
    (lineMono p w e).eval t = ∏ j, (p + t • w) j ^ e j := by
  simp only [lineMono, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.prod_congr rfl fun j _ => by rw [mul_comm (w j)]

private theorem natDegree_le_and_coeff_lineMono (p w : σ → k) (e : σ →₀ ℕ) (s : Finset σ) :
    (∏ j ∈ s, (Polynomial.C (p j) + Polynomial.C (w j) * Polynomial.X) ^ e j).natDegree ≤
        ∑ j ∈ s, e j ∧
      (∏ j ∈ s, (Polynomial.C (p j) + Polynomial.C (w j) * Polynomial.X) ^ e j).coeff
        (∑ j ∈ s, e j) = ∏ j ∈ s, w j ^ e j := by
  classical
  have h1 : ∀ j, (Polynomial.C (p j) + Polynomial.C (w j) * Polynomial.X).natDegree ≤ 1 :=
    fun j => by rw [add_comm]; exact Polynomial.natDegree_linear_le
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have hpow : ((Polynomial.C (p a) + Polynomial.C (w a) * Polynomial.X) ^ e a).natDegree ≤
        e a := by
      simpa using Polynomial.natDegree_pow_le_of_le (e a) (h1 a)
    refine ⟨(Polynomial.natDegree_mul_le).trans (add_le_add hpow ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hpow ih.1, ih.2]
    congr 1
    have := Polynomial.coeff_pow_of_natDegree_le (m := e a) (h1 a)
    rw [mul_one] at this
    rw [this]
    simp

/-- The `n`-th coefficient, in `t`, of the linear form `formLin m (p + t w)`. -/
private noncomputable def lineLin (m : ι → σ →₀ ℕ) (p w : σ → k) (n : ℕ) : MvPolynomial ι k :=
  ∑ b, C ((lineMono p w (m b)).coeff n) * X b

private theorem isHomogeneous_lineLin (m : ι → σ →₀ ℕ) (p w : σ → k) (n : ℕ) :
    (lineLin m p w n).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun b _ => isHomogeneous_C_mul_X _ b

private theorem lineLin_top (m : ι → σ →₀ ℕ) {D : ℕ} (hD : ∀ b, ∑ j, m b j = D) (p w : σ → k) :
    lineLin m p w D = formLin m w := by
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← hD b, show (lineMono p w (m b)).coeff (∑ j, m b j) = ∏ j, w j ^ m b j from
    (natDegree_le_and_coeff_lineMono p w (m b) Finset.univ).2]

private theorem sum_lineLin (m : ι → σ →₀ ℕ) {D : ℕ} (hD : ∀ b, ∑ j, m b j = D) (p w : σ → k)
    (t : k) :
    ∑ n ∈ Finset.range (D + 1), t ^ n • lineLin m p w n = formLin m (p + t • w) := by
  simp only [lineLin, Finset.smul_sum, formLin]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hdeg : (lineMono p w (m b)).natDegree < D + 1 := Nat.lt_succ_of_le
    (((natDegree_le_and_coeff_lineMono p w (m b) Finset.univ).1).trans (hD b).le)
  rw [← eval_lineMono, Polynomial.eval_eq_sum_range' hdeg, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_eq_C_mul, ← mul_assoc, ← C_mul, mul_comm (t ^ n)]

/-- The fraction `Lₙ / L(w)` on the chart `D₊(L(w))`. -/
private noncomputable def lineFrac (m : ι → σ →₀ ℕ) (p w : σ → k) (n : ℕ) :
    Away (homogeneousSubmodule ι k) (formLin m w) :=
  HomogeneousLocalization.mk ⟨1, ⟨lineLin m p w n, isHomogeneous_lineLin m p w n⟩,
    ⟨formLin m w, isHomogeneous_formLin m w⟩, ⟨1, pow_one _⟩⟩

/-- The polynomial `g(t) = ∑ₙ (Lₙ / L(w)) tⁿ` on the chart `D₊(L(w))`. -/
private noncomputable def rootPoly (m : ι → σ →₀ ℕ) (p w : σ → k) (D : ℕ) :
    Polynomial (Away (homogeneousSubmodule ι k) (formLin m w)) :=
  ∑ n ∈ Finset.range (D + 1), Polynomial.monomial n (lineFrac m p w n)

private theorem rootPoly_monic (m : ι → σ →₀ ℕ) {D : ℕ} (hD : ∀ b, ∑ j, m b j = D)
    (p w : σ → k) : (rootPoly m p w D).Monic := by
  refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one D
    (Polynomial.natDegree_sum_le_of_forall_le _ _ fun n hn =>
      (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))
    ?_
  rw [rootPoly, Polynomial.finset_sum_coeff, Finset.sum_eq_single D]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
    apply HomogeneousLocalization.val_injective
    simp only [lineFrac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
    rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [lineLin_top m hD]⟩
  · intro n _ hn
    rw [Polynomial.coeff_monomial, if_neg hn]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self D)) h

private theorem eval_map_awayEval_rootPoly (m : ι → σ →₀ ℕ) {D : ℕ} (hD : ∀ b, ∑ j, m b j = D)
    (p w : σ → k) (c : ι → k) (hc : eval c (formLin m w) ≠ 0) (t : k) :
    ((rootPoly m p w D).map (awayEval (formLin m w) c hc).toRingHom).eval t =
      eval c (formLin m (p + t • w)) * (eval c (formLin m w))⁻¹ := by
  rw [← sum_lineLin m hD p w t, map_sum, Finset.sum_mul, rootPoly, Polynomial.map_sum,
    Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Polynomial.map_monomial, Polynomial.eval_monomial, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, lineFrac, awayEval_mk, smul_eq_C_mul, eval_mul, eval_C]
  simp only [pow_one]
  ring

/-- A root of a nonzero polynomial over an algebraically closed field: if `P(x)` lies in a prime
`r` of a `k`-algebra, then `x - a ∈ r` for a root `a` of `P`. -/
private theorem exists_isRoot_sub_mem [IsAlgClosed k] {R : Type*} [CommRing R] [Algebra k R]
    (r : Ideal R) [r.IsPrime] (x : R) :
    ∀ (n : ℕ) (P : Polynomial k), P.natDegree = n → P ≠ 0 → Polynomial.aeval x P ∈ r →
      ∃ a, P.IsRoot a ∧ x - algebraMap k R a ∈ r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hn hP hx
    by_cases h0 : P.natDegree = 0
    · rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.aeval_C] at hx
      have hc : P.coeff 0 ≠ 0 := by
        intro h; apply hP; rw [Polynomial.eq_C_of_natDegree_eq_zero h0, h, map_zero]
      exact absurd (r.eq_top_of_isUnit_mem hx ((IsUnit.mk0 _ hc).map _)) (Ideal.IsPrime.ne_top ‹_›)
    · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P (by
        rw [Polynomial.degree_eq_natDegree hP]; exact_mod_cast h0)
      have hfac := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
      rw [← hfac, map_mul] at hx
      rcases (‹r.IsPrime›.mem_or_mem hx) with h1 | h1
      · exact ⟨a, ha, by simpa using h1⟩
      · have hQ : P /ₘ (Polynomial.X - Polynomial.C a) ≠ 0 := by
          intro h; rw [h, mul_zero] at hfac; exact hP hfac.symm
        have hdeg : (P /ₘ (Polynomial.X - Polynomial.C a)).natDegree < n := by
          rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C a),
            Polynomial.natDegree_X_sub_C]; omega
        obtain ⟨b, hb, hb'⟩ := ih _ hdeg _ rfl hQ h1
        refine ⟨b, ?_, hb'⟩
        rw [← hfac, Polynomial.IsRoot, Polynomial.eval_mul, hb.eq_zero, mul_zero]

/-- The ring `A⁰_{L(w)}[t] / (g)` of the roots of `g` over the chart `D₊(L(w))`. -/
private abbrev RootRing (m : ι → σ →₀ ℕ) (p w : σ → k) (D : ℕ) : Type _ :=
  Polynomial (Away (homogeneousSubmodule ι k) (formLin m w)) ⧸ Ideal.span {rootPoly m p w D}

/-- Evaluation of `A⁰_{L(w)}[t] / (g)` at a `k`-point `e` of the chart and a root `t` of `g` over
it. -/
private noncomputable def rootEval {m : ι → σ →₀ ℕ} {p w : σ → k} {D : ℕ}
    (e : Away (homogeneousSubmodule ι k) (formLin m w) →ₐ[k] k) (t : k)
    (ht : ((rootPoly m p w D).map e.toRingHom).eval t = 0) : RootRing m p w D →+* k :=
  Ideal.Quotient.lift _ (Polynomial.eval₂RingHom e.toRingHom t) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    change (b * rootPoly m p w D).eval₂ e.toRingHom t = 0
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_eq_eval_map (p := rootPoly m p w D), ht,
      mul_zero]

private theorem rootEval_mk {m : ι → σ →₀ ℕ} {p w : σ → k} {D : ℕ}
    (e : Away (homogeneousSubmodule ι k) (formLin m w) →ₐ[k] k) (t : k)
    (ht : ((rootPoly m p w D).map e.toRingHom).eval t = 0) (h : Polynomial _) :
    rootEval e t ht (Ideal.Quotient.mk _ h) = h.eval₂ e.toRingHom t := rfl

private theorem rootEval_algebraMap {m : ι → σ →₀ ℕ} {p w : σ → k} {D : ℕ}
    (e : Away (homogeneousSubmodule ι k) (formLin m w) →ₐ[k] k) (t : k)
    (ht : ((rootPoly m p w D).map e.toRingHom).eval t = 0) (α : Away _ (formLin m w)) :
    rootEval e t ht (algebraMap _ (RootRing m p w D) α) = e α := by
  change rootEval e t ht (Ideal.Quotient.mk _ (Polynomial.C α)) = e α
  rw [rootEval_mk, Polynomial.eval₂_C]
  rfl

private theorem rootEval_algebraMap_base {m : ι → σ →₀ ℕ} {p w : σ → k} {D : ℕ}
    (e : Away (homogeneousSubmodule ι k) (formLin m w) →ₐ[k] k) (t : k)
    (ht : ((rootPoly m p w D).map e.toRingHom).eval t = 0) (s : k) :
    rootEval e t ht (algebraMap k (RootRing m p w D) s) = s := by
  rw [IsScalarTower.algebraMap_apply k (Away (homogeneousSubmodule ι k) (formLin m w)),
    rootEval_algebraMap, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

private theorem rootEval_X {m : ι → σ →₀ ℕ} {p w : σ → k} {D : ℕ}
    (e : Away (homogeneousSubmodule ι k) (formLin m w) →ₐ[k] k) (t : k)
    (ht : ((rootPoly m p w D).map e.toRingHom).eval t = 0) :
    rootEval e t ht (Ideal.Quotient.mk _ Polynomial.X) = t := by
  rw [rootEval_mk, Polynomial.eval₂_X]

/-- **The points of the root ring over a `k`-point of the chart are the roots.** A prime `r` of
`A⁰_{L(w)}[t] / (g)` lying over the kernel of a `k`-point `e` of the chart is the kernel of
evaluation at `e` and some root `t` of `g` over `e`. -/
private theorem exists_eq_ker_rootEval [IsAlgClosed k] {m : ι → σ →₀ ℕ} {D : ℕ}
    (hD : ∀ b, ∑ j, m b j = D) {p w : σ → k}
    (e : Away (homogeneousSubmodule ι k) (formLin m w) →ₐ[k] k) (r : Ideal (RootRing m p w D))
    [r.IsPrime] (hr : ∀ α, algebraMap _ (RootRing m p w D) α ∈ r ↔ e α = 0) :
    ∃ t ht, r = RingHom.ker (rootEval (D := D) e t ht) := by
  classical
  set A := Away (homogeneousSubmodule ι k) (formLin m w)
  set π := Ideal.Quotient.mk r
  set x : RootRing m p w D := Ideal.Quotient.mk _ Polynomial.X
  have hπ : π.comp (Ideal.Quotient.mk (Ideal.span {rootPoly m p w D})) =
      π.comp (Polynomial.eval₂RingHom ((algebraMap k (RootRing m p w D)).comp e.toRingHom) x) := by
    refine Polynomial.ringHom_ext (fun α => ?_) ?_
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [Ideal.Quotient.eq]
      have h1 : Ideal.Quotient.mk (Ideal.span {rootPoly m p w D}) (Polynomial.C α) -
          algebraMap k (RootRing m p w D) (e α) =
          algebraMap A (RootRing m p w D) (α - algebraMap k A (e α)) := by
        rw [map_sub, ← IsScalarTower.algebraMap_apply]
        rfl
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, hr, map_sub, AlgHom.commutes]
      simp
    · simp [x]
  have hred : ∀ h : Polynomial A, π (Ideal.Quotient.mk _ h) =
      π (Polynomial.aeval x (h.map e.toRingHom)) := fun h => by
    have := congrArg (fun φ => φ h) hπ
    simp only [RingHom.comp_apply] at this
    rw [this, Polynomial.coe_eval₂RingHom, Polynomial.aeval_def, Polynomial.eval₂_map]
  have hev : ∀ (P : Polynomial k) (t : k), x - algebraMap k _ t ∈ r →
      π (Polynomial.aeval x P) = π (algebraMap k _ (P.eval t)) := fun P t hxt => by
    rw [Ideal.Quotient.eq]
    obtain ⟨Q, hQ⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := t) (p := P)
    have := congrArg (Polynomial.aeval x) hQ
    rw [map_sub, Polynomial.aeval_C, map_mul, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C] at this
    rw [this]
    exact r.mul_mem_right _ hxt
  have hg0 : Polynomial.aeval x ((rootPoly m p w D).map e.toRingHom) ∈ r := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hred, Ideal.Quotient.mk_singleton_self, map_zero]
  have hne : (rootPoly m p w D).map e.toRingHom ≠ 0 :=
    ((rootPoly_monic m hD p w).map e.toRingHom).ne_zero
  obtain ⟨t, ht₀, hxt⟩ := exists_isRoot_sub_mem r x _ _ rfl hne hg0
  have ht : ((rootPoly m p w D).map e.toRingHom).eval t = 0 := ht₀
  refine ⟨t, ht, ?_⟩
  have hsurj : Function.Surjective (rootEval (D := D) e t ht) := fun s =>
    ⟨algebraMap k _ s, rootEval_algebraMap_base e t ht s⟩
  have hmax := RingHom.ker_isMaximal_of_surjective _ hsurj
  refine (hmax.eq_of_le (Ideal.IsPrime.ne_top ‹_›) fun y hy => ?_).symm
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, rootEval_mk] at hy
  rw [← Ideal.Quotient.eq_zero_iff_mem, hred, hev _ t hxt, ← Polynomial.eval₂_eq_eval_map, hy,
    map_zero, map_zero]

end LineRoots

section ChowForms

open MvPolynomial MMP.Intersection

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}} {N : ℕ}

/-- The monomials of bidegree `(d, d)` in two sets `u, v` of `N + 1` variables. -/
private abbrev Bidegree (N d : ℕ) : Type :=
  {e : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ // (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d}

private theorem finite_bidegree (N d : ℕ) : Finite (Bidegree N d) := by
  refine Finite.of_injective
    (fun e : Bidegree N d => fun j : Fin (N + 1) ⊕ Fin (N + 1) =>
      (⟨min (e.1 j) d, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (d + 1))) ?_
  intro e e' h
  have hle : ∀ (e : Bidegree N d) j, e.1 j ≤ d := by
    intro e j
    rcases j with j | j
    · exact (Finset.single_le_sum (f := fun j => e.1 (Sum.inl j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans e.2.1.le
    · exact (Finset.single_le_sum (f := fun j => e.1 (Sum.inr j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans e.2.2.le
  refine Subtype.ext (Finsupp.ext fun j => ?_)
  have := congrArg (fun f => (f j : ℕ)) h
  simpa [min_eq_left (hle e j), min_eq_left (hle e' j)] using this

private theorem nonempty_bidegree (N d : ℕ) : Nonempty (Bidegree N d) :=
  ⟨⟨Finsupp.single (Sum.inl 0) d + Finsupp.single (Sum.inr 0) d, by
    simp [Finsupp.single_apply, Finset.sum_ite_eq']⟩⟩

/-- The projective space of bihomogeneous forms of bidegree `(d, d)`, the target of the Chow-form
morphism `MMP.Chow.exists_chowFormMorphism`. -/
private noncomputable abbrev FormSpace (k : Type u) [Field k] (N d : ℕ) : Scheme.{u} :=
  ProjSpace k (ULift.{u} (Bidegree N d))

/-- `p` is the point `[∏_C Ch_C^{Z(C)}]` of the space of `(d, d)`-forms given by the incidence
forms `Ch_C` of the components of a 1-cycle `Z` on `ℙᴺ_k`, for every choice of these forms. -/
private def IsChowPoint (d : ℕ) (Z : Mori.OneCycle ℤ (projToSpecCoeff k N))
    (p : FormSpace k N d) : Prop :=
  ∀ G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k,
    (∀ C ∈ Z.support, Irreducible (G C) ∧
      ∀ u v : Fin (N + 1) → k, eval (Sum.elim u v) (G C) = 0 ↔
        ∃ p ∈ closure ({C.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))),
          (∑ j, MvPolynomial.C (u j) * MvPolynomial.X j) ∈ ProjectiveSpectrum.asHomogeneousIdeal p ∧
          (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j) ∈ ProjectiveSpectrum.asHomogeneousIdeal p) →
    let F := ∏ C ∈ Z.support, G C ^ (Z C).toNat
    (∀ e ∈ F.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d) ∧
    ∀ b b' : ULift.{u} (Bidegree N d), F.coeff b'.down.1 • MvPolynomial.X b - F.coeff b.down.1 • MvPolynomial.X b' ∈
      ProjectiveSpectrum.asHomogeneousIdeal p

/-- The `𝒪(1)`-degree of a 1-cycle on `X ⊆ ℙᴺ_k`, computed on its push-forward. -/
private noncomputable abbrev cycleDegree (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    (Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)) : ℤ :=
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
    (Mori.OneCycle.pushforward ℤ (i ≫ projToSpecCoeff k N) (projToSpecCoeff k N) i Z)

/-- `p` is the Chow point of an effective degree-`d` 1-cycle `Z` on `X`. -/
private def IsChowPointOf (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (d : ℕ)
    (Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)) (p : FormSpace k N d) : Prop :=
  0 ≤ Z ∧ cycleDegree i Z = d ∧
    IsChowPoint d (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z) p

open Classical in
/-- The effective degree-`d` 1-cycle on `X` whose Chow point is `p`, and `0` if there is none. -/
private noncomputable def chowCycle (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) (d : ℕ)
    (p : FormSpace k N d) : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N) :=
  if h : ∃ Z, IsChowPointOf i d Z p then h.choose else 0

private theorem isChowPointOf_chowCycle {i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)}
    {d : ℕ} {p : FormSpace k N d} (h : ∃ Z, IsChowPointOf i d Z p) :
    IsChowPointOf i d (chowCycle i d p) p := by
  rw [chowCycle, dif_pos h]
  exact h.choose_spec

variable [IsAlgClosed k] [CharZero k]

/-- The incidence locus `{(u, v) | C ∩ H_u ∩ H_v ≠ ∅}` of a proper curve `C ⊆ ℙᴺ_k`. -/
private def IncidenceLocus (C : Mori.ProperCurve (projToSpecCoeff k N)) (u v : Fin (N + 1) → k) :
    Prop :=
  ∃ p ∈ closure ({C.point} : Set (AlgebraicGeometry.Proj (polyGrading k N))),
    (∑ j, MvPolynomial.C (u j) * MvPolynomial.X j) ∈ ProjectiveSpectrum.asHomogeneousIdeal p ∧
    (∑ j, MvPolynomial.C (v j) * MvPolynomial.X j) ∈ ProjectiveSpectrum.asHomogeneousIdeal p

private theorem weight_sumElim_one_zero (e : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (Sum.elim (fun _ => 1) (fun _ => 0)) e = ∑ j, e (Sum.inl j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_sum_type]

private theorem weight_sumElim_zero_one (e : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (Sum.elim (fun _ => 0) (fun _ => 1)) e = ∑ j, e (Sum.inr j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_sum_type]

/-- **Incidence forms exist.** Every proper curve `C ⊆ ℙᴺ_k` of degree `n` has an irreducible
incidence form, bihomogeneous of bidegree `(n, n)`: it vanishes at `(u, v)` exactly when `C` meets
the hyperplanes `H_u` and `H_v`. -/
private theorem exists_incidenceForm (C : Mori.ProperCurve (projToSpecCoeff k N)) :
    ∃ (G : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) (n : ℕ), Irreducible G ∧
      (∀ u v : Fin (N + 1) → k, eval (Sum.elim u v) G = 0 ↔ IncidenceLocus C u v) ∧
      (haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1;
        (n : ℤ) = C.degree k (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)) ∧
      IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0)) G n ∧
      IsWeightedHomogeneous (Sum.elim (fun _ => 0) (fun _ => 1)) G n := by
  obtain ⟨G, n, hG, hn, hdeg⟩ := exists_incForm_bidegree C
  refine ⟨G, n, hG.1, hG.2, hn, fun e he => ?_, fun e he => ?_⟩
  · rw [weight_sumElim_one_zero]
    exact (hdeg e (mem_support_iff.mpr he)).1
  · rw [weight_sumElim_zero_one]
    exact (hdeg e (mem_support_iff.mpr he)).2

/-- **The Chow point of a cycle is unique.** -/
private theorem eq_of_isChowPointOf (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) {Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)}
    {p p' : FormSpace k N d} (hp : IsClosed ({p} : Set _)) (hp' : IsClosed ({p'} : Set _))
    (h : IsChowPointOf i d Z p) (h' : IsChowPointOf i d Z p') : p = p' := by
  haveI := finite_bidegree N d
  haveI := Fintype.ofFinite (ULift.{u} (Bidegree N d))
  choose G n hG using fun C : Mori.ProperCurve (projToSpecCoeff k N) => exists_incidenceForm C
  set Z' := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z
  obtain ⟨hFdeg, hrel⟩ := h.2.2 G fun C _ => ⟨(hG C).1, (hG C).2.1⟩
  obtain ⟨-, hrel'⟩ := h'.2.2 G fun C _ => ⟨(hG C).1, (hG C).2.1⟩
  set F := ∏ C ∈ Z'.support, G C ^ (Z' C).toNat
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun C _ => pow_ne_zero _ (hG C).1.ne_zero
  obtain ⟨e, he⟩ : F.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h0 => hF (MvPolynomial.support_eq_empty.mp h0))
  let b₀ : ULift.{u} (Bidegree N d) := ⟨⟨e, hFdeg e he⟩⟩
  exact eq_of_relations (fun b : ULift.{u} (Bidegree N d) => F.coeff b.down.1)
    (b₀ := b₀) (Finsupp.mem_support_iff.mp he) p p' hrel hrel'

/-- **Every effective degree-`d` cycle has a Chow point**: the point `[∏_C Ch_C^{Z(C)}]`, which
does not depend on the choice of the incidence forms `Ch_C`, since these are unique up to
scalars. -/
private theorem exists_isChowPointOf (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) (Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N))
    (hZ : 0 ≤ Z) (hZd : cycleDegree i Z = d) :
    ∃ p, IsClosed ({p} : Set (FormSpace k N d)) ∧ IsChowPointOf i d Z p := by
  classical
  haveI := finite_bidegree N d
  haveI := Fintype.ofFinite (ULift.{u} (Bidegree N d))
  choose G n hG using fun C : Mori.ProperCurve (projToSpecCoeff k N) => exists_incidenceForm C
  set W := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z with hW
  have hWnn : ∀ C, 0 ≤ W C := pushforward_nonneg i _ hZ
  set F := ∏ C ∈ W.support, G C ^ (W C).toNat with hFdef
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun C _ => pow_ne_zero _ (hG C).1.ne_zero
  have hsum : ∑ C ∈ W.support, (W C).toNat * n C = d := by
    have h1 := hZd
    simp only [cycleDegree] at h1
    erw [Mori.OneCycle.degree_apply, Finsupp.sum] at h1
    have : ((∑ C ∈ W.support, (W C).toNat * n C : ℕ) : ℤ) = d := by
      rw [← h1]
      push_cast
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [Int.toNat_of_nonneg (hWnn C), (hG C).2.2.1]
    exact_mod_cast this
  have hhom : ∀ w : Fin (N + 1) ⊕ Fin (N + 1) → ℕ,
      (∀ C, IsWeightedHomogeneous w (G C) (n C)) → IsWeightedHomogeneous w F d := by
    intro w hw
    rw [← hsum]
    have := IsWeightedHomogeneous.prod W.support (fun C => G C ^ (W C).toNat)
      (fun C => (W C).toNat • n C) fun C _ => (hw C).pow _
    simpa only [smul_eq_mul] using this
  have hbideg : ∀ e ∈ F.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d :=
    fun e he => ⟨by
      rw [← weight_sumElim_one_zero]
      exact hhom _ (fun C => (hG C).2.2.2.1) (mem_support_iff.mp he), by
      rw [← weight_sumElim_zero_one]
      exact hhom _ (fun C => (hG C).2.2.2.2) (mem_support_iff.mp he)⟩
  obtain ⟨e, he⟩ : F.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h0 => hF (MvPolynomial.support_eq_empty.mp h0))
  obtain ⟨p, hpc, hrel⟩ := exists_isClosed_relations
    (fun b : ULift.{u} (Bidegree N d) => F.coeff b.down.1) (b₀ := ⟨⟨e, hbideg e he⟩⟩)
    (mem_support_iff.mp he)
  refine ⟨p, hpc, hZ, hZd, fun G' hG' => ?_⟩
  have hassoc : Associated F (∏ C ∈ W.support, G' C ^ (W C).toNat) :=
    Associated.prod _ _ _ fun C hC =>
      (associated_of_forall_eval (hG C).1 (hG' C hC).1 fun x => by
        rw [← Sum.elim_comp_inl_inr x, (hG C).2.1]
        exact ((hG' C hC).2 _ _).symm).pow_pow
  obtain ⟨w, hw⟩ := hassoc
  obtain ⟨r, hr, hwr⟩ := isUnit_iff_eq_C_of_isReduced.mp w.isUnit
  dsimp only
  rw [← hw, hwr, mul_comm]
  refine ⟨fun e he => hbideg e ?_, fun b b' => ?_⟩
  · rw [mem_support_iff, coeff_C_mul] at he
    exact mem_support_iff.mpr (right_ne_zero_of_mul he)
  · rw [coeff_C_mul, coeff_C_mul]
    have := Ideal.mul_mem_left (p.asHomogeneousIdeal.toIdeal) (MvPolynomial.C r) (hrel b b')
    rw [mul_sub, smul_eq_C_mul, smul_eq_C_mul, ← mul_assoc, ← mul_assoc, ← C_mul,
      ← C_mul] at this
    rw [smul_eq_C_mul, smul_eq_C_mul]
    exact this

private theorem jacobsonSpace_proj (k : Type u) [Field k] (N : ℕ) :
    JacobsonSpace (AlgebraicGeometry.Proj (polyGrading k N)) :=
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  LocallyOfFiniteType.jacobsonSpace (projToSpecCoeff k N)

private theorem noetherianSpace_proj (k : Type u) [Field k] (N : ℕ) :
    TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Proj (polyGrading k N)) := by
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  haveI : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading k N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff k N)
  haveI : CompactSpace (AlgebraicGeometry.Proj (polyGrading k N)) :=
    QuasiCompact.compactSpace_of_compactSpace (projToSpecCoeff k N)
  infer_instance

/-- In a Jacobson space, a closure `{y}⁻` not contained in a closed set `Z` contains a closed
point outside `Z`. -/
private theorem exists_isClosed_mem_closure_notMem {Y : Type*} [TopologicalSpace Y]
    [JacobsonSpace Y] {y : Y} {Z : Set Y} (hZ : IsClosed Z) (h : ¬ closure {y} ⊆ Z) :
    ∃ x ∈ closure {y}, IsClosed ({x} : Set Y) ∧ x ∉ Z := by
  by_contra hall
  push Not at hall
  apply h
  rw [← JacobsonSpace.closure_inter_closedPoints isClosed_closure]
  exact hZ.closure_subset_iff.mpr fun x hx => hall x hx.1 hx.2

/-- Through a closed point `x = [a]` of `ℙᴺ_k` off a closed set `L` lying on finitely many proper
curves there are two hyperplanes `H_u, H_v` through `x` with `H_u ∩ H_v ∩ L = ∅`: take `H_u`
through `x` containing none of the curves inside `L`, so that it meets `L` in finitely many points,
and `H_v` through `x` avoiding them. -/
private theorem exists_forall_not_and_of_isClosed (T : Finset (Mori.ProperCurve
    (projToSpecCoeff k N))) {L : Set (AlgebraicGeometry.Proj (polyGrading k N))} (hL : IsClosed L)
    (hLT : L ⊆ ⋃ C ∈ T, closure {C.point}) {x : AlgebraicGeometry.Proj (polyGrading k N)}
    (a : Fin (N + 1) → k) {j : Fin (N + 1)} (haj : a j = 1)
    (ha : ∀ b b', a b' • (MvPolynomial.X b : MvPolynomial (Fin (N + 1)) k) - a b • MvPolynomial.X b'
      ∈ ProjectiveSpectrum.asHomogeneousIdeal x)
    (hxL : x ∉ L) :
    ∃ u v, u ⬝ᵥ a = 0 ∧ v ⬝ᵥ a = 0 ∧ ∀ y ∈ L,
      ¬ ((∑ i, MvPolynomial.C (u i) * MvPolynomial.X i) ∈ ProjectiveSpectrum.asHomogeneousIdeal y ∧
        (∑ i, MvPolynomial.C (v i) * MvPolynomial.X i) ∈ ProjectiveSpectrum.asHomogeneousIdeal y) := by
  classical
  haveI := jacobsonSpace_proj k N
  haveI := noetherianSpace_proj k N
  have ha0 : a j ≠ 0 := by simp [haj]
  have hdot : ∀ b b' : Fin (N + 1),
      (Pi.single b (a b') - Pi.single b' (a b) : Fin (N + 1) → k) ⬝ᵥ a = 0 := by
    intro b b'
    simp only [sub_dotProduct, single_dotProduct]
    ring
  -- a relation of `x` not vanishing at a given point `p ≠ x`
  have hrel : ∀ p : AlgebraicGeometry.Proj (polyGrading k N), p ≠ x → ∃ b b',
      a b' • (MvPolynomial.X b : MvPolynomial (Fin (N + 1)) k) - a b • MvPolynomial.X b' ∉
        ProjectiveSpectrum.asHomogeneousIdeal p := by
    intro p hp
    by_contra hall
    push Not at hall
    exact hp (eq_of_relations a ha0 _ _ hall ha)
  -- the linear form `∑ vᵢ xᵢ` as a linear map, and the hyperplanes through `x`
  let Lf : (Fin (N + 1) → k) →ₗ[k] MvPolynomial (Fin (N + 1)) k :=
    { toFun := fun v => ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i
      map_add' := fun v w => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r v => by simp [Finset.mul_sum, mul_assoc, MvPolynomial.smul_eq_C_mul] }
  let ℓ : (Fin (N + 1) → k) →ₗ[k] k :=
    { toFun := fun v => v ⬝ᵥ a
      map_add' := fun v w => add_dotProduct v w a
      map_smul' := fun r v => smul_dotProduct r v a }
  let P : {C : T // C.1.point ∈ L} → Submodule k (LinearMap.ker ℓ) := fun C =>
    Submodule.comap (Lf ∘ₗ (LinearMap.ker ℓ).subtype)
      ((ProjectiveSpectrum.asHomogeneousIdeal C.1.1.point).toIdeal.restrictScalars k)
  have hP : ∀ C, P C ≠ ⊤ := by
    intro C htop
    have hne : C.1.1.point ≠ x := fun h => hxL (h ▸ C.2)
    obtain ⟨b, b', hbb⟩ := hrel _ hne
    have hmem : (⟨_, hdot b b'⟩ : LinearMap.ker ℓ) ∈ P C := htop ▸ Submodule.mem_top
    apply hbb
    have := hmem
    simp only [P, Submodule.mem_comap, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, Submodule.restrictScalars_mem] at this
    rwa [show Lf _ = _ from linearForm_single_sub_single b b' (a b') (a b)] at this
  obtain ⟨⟨u, hu⟩, huP⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hP
  have hua : u ⬝ᵥ a = 0 := hu
  have huC : ∀ C ∈ T, C.point ∈ L → (∑ i, MvPolynomial.C (u i) * MvPolynomial.X i) ∉
      ProjectiveSpectrum.asHomogeneousIdeal C.point := fun C hC hCL h => huP ⟨⟨C, hC⟩, hCL⟩ h
  -- the finitely many points of `H_u ∩ L`
  set S := L ∩
    {p : AlgebraicGeometry.Proj (polyGrading k N) |
      (∑ i, MvPolynomial.C (u i) * MvPolynomial.X i) ∈ ProjectiveSpectrum.asHomogeneousIdeal p}
  have hHu : IsClosed {p : AlgebraicGeometry.Proj (polyGrading k N) |
      (∑ i, MvPolynomial.C (u i) * MvPolynomial.X i) ∈ ProjectiveSpectrum.asHomogeneousIdeal p} := by
    have : {p : AlgebraicGeometry.Proj (polyGrading k N) |
        (∑ i, MvPolynomial.C (u i) * MvPolynomial.X i) ∈ ProjectiveSpectrum.asHomogeneousIdeal p} =
        ProjectiveSpectrum.zeroLocus (polyGrading k N)
          {∑ i, MvPolynomial.C (u i) * MvPolynomial.X i} := by
      ext p
      exact ((ProjectiveSpectrum.mem_zeroLocus _ _ _).trans Set.singleton_subset_iff).symm
    rw [this]
    exact ProjectiveSpectrum.isClosed_zeroLocus _ _
  have hSpts : ∀ s ∈ S, IsClosed ({s} : Set _) := fun s hs => by
    obtain ⟨C, hC, hsC⟩ := Set.mem_iUnion₂.mp (hLT hs.1)
    exact ProperCurve.isClosed_singleton_of_specializes C (specializes_iff_mem_closure.mpr hsC)
      (by rintro rfl; exact huC C hC hs.1 hs.2)
  have hSfin : S.Finite := finite_of_isClosed_of_forall_isClosed_singleton (hL.inter hHu) hSpts
  haveI := hSfin.fintype
  choose c jc hcj hc using fun s : S => exists_relations_of_isClosed s.1 (hSpts s.1 s.2)
  have hne : ∀ s : S, (s : AlgebraicGeometry.Proj (polyGrading k N)) ≠ x := fun s h =>
    hxL (h ▸ s.2.1)
  choose bs bs' hbs using fun s => hrel s.1 (hne s)
  let w : S → Fin (N + 1) → k := fun s =>
    Pi.single (bs s) (a (bs' s)) - Pi.single (bs' s) (a (bs s))
  have hw : ∀ s, w s ⬝ᵥ c s ≠ 0 := fun s h0 => hbs s (by
    rw [← linearForm_single_sub_single]
    exact (linearForm_mem_iff (c s) (hcj s) _ (hc s) _).mpr h0)
  obtain ⟨t, ht⟩ := exists_dotProduct_ne_zero w c hw
  set v := ∑ r, t r • w r
  have hva : v ⬝ᵥ a = 0 := by
    simp only [v, sum_dotProduct, smul_dotProduct, w, hdot, smul_zero, Finset.sum_const_zero]
  refine ⟨u, v, hua, hva, fun p hpL ⟨hpu, hpv⟩ => ?_⟩
  have hpS : p ∈ S := ⟨hpL, hpu⟩
  exact ht ⟨p, hpS⟩ ((linearForm_mem_iff (c ⟨p, hpS⟩) (hcj _) _ (hc _) v).mp hpv)

/-- Through a closed point `x = [a]` of `ℙᴺ_k` off finitely many proper curves `C ∈ T` there are
two hyperplanes `H_u, H_v` through `x` with `H_u ∩ H_v` disjoint from every `C ∈ T`: take `H_u`
through `x` containing none of the curves, so that it meets their union in finitely many points,
and `H_v` through `x` avoiding them. -/
private theorem exists_not_incidenceLocus_of_forall_notMem (T : Finset (Mori.ProperCurve
    (projToSpecCoeff k N))) {x : AlgebraicGeometry.Proj (polyGrading k N)}
    (a : Fin (N + 1) → k) {j : Fin (N + 1)} (haj : a j = 1)
    (ha : ∀ b b', a b' • (MvPolynomial.X b : MvPolynomial (Fin (N + 1)) k) - a b • MvPolynomial.X b'
      ∈ ProjectiveSpectrum.asHomogeneousIdeal x)
    (hx : ∀ C ∈ T, x ∉ closure {C.point}) :
    ∃ u v, u ⬝ᵥ a = 0 ∧ v ⬝ᵥ a = 0 ∧ ∀ C ∈ T, ¬ IncidenceLocus C u v := by
  obtain ⟨u, v, hua, hva, huv⟩ := exists_forall_not_and_of_isClosed T
    (isClosed_biUnion_finset fun _ _ => isClosed_closure) subset_rfl a haj ha
    (fun h => by obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp h; exact hx C hC hxC)
  exact ⟨u, v, hua, hva, fun C hC ⟨p, hp, hpu, hpv⟩ =>
    huv p (Set.mem_biUnion hC hp) ⟨hpu, hpv⟩⟩

/-- Through a closed point `x` of a proper curve `C ⊆ ℙᴺ_k` off another proper curve `C'` there
are two hyperplanes `H_u, H_v` meeting `C` but with `H_u ∩ H_v` disjoint from `C'`: take `H_u`
through `x` not containing `C'`, so that it meets `C'` in finitely many points, and `H_v` through
`x` avoiding them. -/
private theorem exists_incidenceLocus_not (C C' : Mori.ProperCurve (projToSpecCoeff k N))
    {x : AlgebraicGeometry.Proj (polyGrading k N)} (hx : x ∈ closure {C.point})
    (hxc : IsClosed ({x} : Set _)) (hx' : x ∉ closure {C'.point}) :
    ∃ u v, IncidenceLocus C u v ∧ ¬ IncidenceLocus C' u v := by
  obtain ⟨a, j, haj, ha⟩ := exists_relations_of_isClosed x hxc
  obtain ⟨u, v, hua, hva, huv⟩ :=
    exists_not_incidenceLocus_of_forall_notMem {C'} a haj ha (by simpa using hx')
  exact ⟨u, v, ⟨x, hx, (linearForm_mem_iff a haj x ha u).mpr hua,
    (linearForm_mem_iff a haj x ha v).mpr hva⟩, huv C' (Finset.mem_singleton_self _)⟩

/-- **A curve is determined by its incidence locus.** If `C, C' ⊆ ℙᴺ_k` meet exactly the same
pairs of hyperplanes, then `C = C'`: through a point of `C` off `C'`, a general codimension-two
linear subspace avoids `C'`. -/
private theorem eq_of_incidenceLocus_eq {C C' : Mori.ProperCurve (projToSpecCoeff k N)}
    (h : ∀ u v, IncidenceLocus C u v ↔ IncidenceLocus C' u v) : C = C' := by
  haveI := jacobsonSpace_proj k N
  by_contra hne
  have hsub : ¬ closure {C.point} ⊆ closure {C'.point} ∨
      ¬ closure {C'.point} ⊆ closure {C.point} := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact hne (Mori.ProperCurve.ext ((specializes_iff_closure_subset.mpr h2).antisymm
      (specializes_iff_closure_subset.mpr h1)).eq)
  rcases hsub with h1 | h1
  · obtain ⟨x, hxC, hxc, hx'⟩ := exists_isClosed_mem_closure_notMem isClosed_closure h1
    obtain ⟨u, v, h3, h4⟩ := exists_incidenceLocus_not C C' hxC hxc hx'
    exact h4 ((h u v).mp h3)
  · obtain ⟨x, hxC, hxc, hx'⟩ := exists_isClosed_mem_closure_notMem isClosed_closure h1
    obtain ⟨u, v, h3, h4⟩ := exists_incidenceLocus_not C' C hxC hxc hx'
    exact h4 ((h u v).mpr h3)

/-- Associated incidence forms belong to the same curve. -/
private theorem eq_of_associated_incidenceForm {C C' : Mori.ProperCurve (projToSpecCoeff k N)}
    {G G' : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    (hG : ∀ u v, eval (Sum.elim u v) G = 0 ↔ IncidenceLocus C u v)
    (hG' : ∀ u v, eval (Sum.elim u v) G' = 0 ↔ IncidenceLocus C' u v) (hGG : Associated G G') :
    C = C' := by
  obtain ⟨w, rfl⟩ := hGG
  refine eq_of_incidenceLocus_eq fun u v => ?_
  rw [← hG, ← hG', eval_mul, mul_eq_zero, or_iff_left]
  exact ((w.isUnit.map (eval (Sum.elim u v))).ne_zero)

/-- **The Chow form determines the cycle.** -/
private theorem eq_of_isChowPointOf_of_isChowPointOf
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i] (d : ℕ)
    (hd : 0 < d) {Z Z' : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)} {p : FormSpace k N d}
    (hp : IsClosed ({p} : Set _)) (h : IsChowPointOf i d Z p) (h' : IsChowPointOf i d Z' p) :
    Z = Z' := by
  classical
  haveI := finite_bidegree N d
  haveI := Fintype.ofFinite (ULift.{u} (Bidegree N d))
  choose G n hG using fun C : Mori.ProperCurve (projToSpecCoeff k N) => exists_incidenceForm C
  set W := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z with hW
  set W' := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z' with hW'
  obtain ⟨hFdeg, hrel⟩ := h.2.2 G fun C _ => ⟨(hG C).1, (hG C).2.1⟩
  obtain ⟨hFdeg', hrel'⟩ := h'.2.2 G fun C _ => ⟨(hG C).1, (hG C).2.1⟩
  set T := W.support ∪ W'.support
  have hext : ∀ (V : Mori.OneCycle ℤ (projToSpecCoeff k N)), V.support ⊆ T →
      ∏ C ∈ V.support, G C ^ (V C).toNat = ∏ C ∈ T, G C ^ (V C).toNat := fun V hV =>
    Finset.prod_subset hV fun C _ hC => by
      rw [Finsupp.notMem_support_iff.mp hC, Int.toNat_zero, pow_zero]
  set F := ∏ C ∈ W.support, G C ^ (W C).toNat
  set F' := ∏ C ∈ W'.support, G C ^ (W' C).toNat
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun C _ => pow_ne_zero _ (hG C).1.ne_zero
  have hF' : F' ≠ 0 := Finset.prod_ne_zero_iff.mpr fun C _ => pow_ne_zero _ (hG C).1.ne_zero
  obtain ⟨e, he⟩ : F.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h0 => hF (MvPolynomial.support_eq_empty.mp h0))
  let b₀ : ULift.{u} (Bidegree N d) := ⟨⟨e, hFdeg e he⟩⟩
  have hc : F.coeff e ≠ 0 := Finsupp.mem_support_iff.mp he
  have hprop := mul_eq_mul_of_relations (fun b : ULift.{u} (Bidegree N d) => F.coeff b.down.1)
    (fun b : ULift.{u} (Bidegree N d) => F'.coeff b.down.1) (b₀ := b₀) hc p hrel hrel'
  -- `F_e · F' = F'_e · F` as polynomials
  have hpoly : MvPolynomial.C (F.coeff e) * F' = MvPolynomial.C (F'.coeff e) * F := by
    ext m
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
    by_cases hm : (∑ j, m (Sum.inl j)) = d ∧ (∑ j, m (Sum.inr j)) = d
    · have := hprop ⟨⟨m, hm⟩⟩
      simp only at this
      rw [mul_comm, this, mul_comm]
    · have h1 : F.coeff m = 0 := by
        by_contra h1; exact hm (hFdeg m (Finsupp.mem_support_iff.mpr h1))
      have h2 : F'.coeff m = 0 := by
        by_contra h2; exact hm (hFdeg' m (Finsupp.mem_support_iff.mpr h2))
      rw [h1, h2, mul_zero, mul_zero]
  have hc' : F'.coeff e ≠ 0 := by
    intro h0
    rw [h0, MvPolynomial.C_0, zero_mul, mul_eq_zero, MvPolynomial.C_eq_zero] at hpoly
    exact hpoly.elim hc hF'
  have hassoc : Associated F F' := by
    have hF'eq : F' = F * MvPolynomial.C (F'.coeff e / F.coeff e) := by
      have := congrArg (MvPolynomial.C (F.coeff e)⁻¹ * ·) hpoly
      simp only [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hc, MvPolynomial.C_1,
        one_mul] at this
      conv_lhs => rw [this]
      rw [mul_comm, div_eq_inv_mul]
    rw [hF'eq]
    exact associated_mul_unit_right _ _ ((Ne.isUnit (div_ne_zero hc' hc)).map MvPolynomial.C)
  letI := UniqueFactorizationMonoid.normalizationMonoid
    (α := MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
  have hinj : ∀ a ∈ T, ∀ b ∈ T, Associated (G a) (G b) → a = b := fun a _ b _ hab =>
    eq_of_associated_incidenceForm (hG a).2.1 (hG b).2.1 hab
  have hcount : ∀ C ∈ T, (W C).toNat = (W' C).toNat := by
    intro C hC
    have e1 := count_normalizedFactors_prod_pow T G (fun C => (W C).toNat)
      (fun C _ => (hG C).1) hinj hC
    have e2 := count_normalizedFactors_prod_pow T G (fun C => (W' C).toNat)
      (fun C _ => (hG C).1) hinj hC
    rw [← hext W Finset.subset_union_left] at e1
    rw [← hext W' Finset.subset_union_right] at e2
    rw [← e1, ← e2, hassoc.normalizedFactors_eq]
  have hWW : W = W' := by
    ext C
    by_cases hC : C ∈ T
    · have := hcount C hC
      rw [← Int.toNat_of_nonneg (pushforward_nonneg i _ h.1 C),
        ← Int.toNat_of_nonneg (pushforward_nonneg i _ h'.1 C), this]
    · rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hC
      rw [hC.1, hC.2]
  exact pushforward_injective i _ hWW

/-- A homogeneous polynomial of degree `n` scales by `rⁿ`. -/
private theorem eval_mul_of_isHomogeneous {σ : Type*} [Fintype σ] (c : σ → k) (r : k)
    {g : MvPolynomial σ k} {n : ℕ} (hg : g.IsHomogeneous n) :
    eval (fun i => r * c i) g = r ^ n * eval c g := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : ∑ i, e i = n := by
    have := hg (mem_support_iff.mp he)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- The form with coefficients `F_b` on the monomials `b` of bidegree `(d, d)` is `F`. -/
private theorem formEval_eq_eval {d : ℕ} [Fintype (ULift.{u} (Bidegree N d))]
    (F : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
    (hF : ∀ e ∈ F.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d)
    (v v' : Fin (N + 1) → k) :
    formEval (k := k) (fun b : ULift.{u} (Bidegree N d) => b.down.1)
      (fun b => F.coeff b.down.1) v v' = eval (Sum.elim v v') F := by
  rw [formEval, eval_eq']
  symm
  refine Finset.sum_bij_ne_zero (fun e he _ => (⟨⟨e, hF e he⟩⟩ : ULift.{u} (Bidegree N d)))
    (fun _ _ _ => Finset.mem_univ _) (fun e₁ _ _ e₂ _ _ h => ?_) (fun b _ hb => ?_)
    (fun _ _ _ => rfl)
  · exact congrArg (fun b : ULift.{u} (Bidegree N d) => b.down.1) h
  · exact ⟨b.down.1, Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hb), hb, rfl⟩

/-- A closed point `y = [a]` lies on the support of an effective cycle `W` on `ℙᴺ_k` exactly when
the product `∏_C Ch_C^{W(C)}` of incidence forms vanishes on all pairs of hyperplanes through
`y`. -/
private theorem forall_eval_prod_eq_zero_iff (Wc : Mori.OneCycle ℤ (projToSpecCoeff k N))
    (hWc : ∀ C, 0 ≤ Wc C)
    (G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
    (hG : ∀ C, ∀ u v : Fin (N + 1) → k, eval (Sum.elim u v) (G C) = 0 ↔ IncidenceLocus C u v)
    {y : AlgebraicGeometry.Proj (polyGrading k N)} (a : Fin (N + 1) → k) {j : Fin (N + 1)}
    (haj : a j = 1)
    (ha : ∀ b b', a b' • (MvPolynomial.X b : MvPolynomial (Fin (N + 1)) k) - a b • MvPolynomial.X b'
      ∈ ProjectiveSpectrum.asHomogeneousIdeal y) :
    (∀ v v' : Fin (N + 1) → k, v ⬝ᵥ a = 0 → v' ⬝ᵥ a = 0 →
        eval (Sum.elim v v') (∏ C ∈ Wc.support, G C ^ (Wc C).toNat) = 0) ↔
      y ∈ ⋃ C ∈ Wc.support, closure {C.point} := by
  have hprod : ∀ v v' : Fin (N + 1) → k,
      eval (Sum.elim v v') (∏ C ∈ Wc.support, G C ^ (Wc C).toNat) = 0 ↔
        ∃ C ∈ Wc.support, IncidenceLocus C v v' := by
    intro v v'
    rw [map_prod, Finset.prod_eq_zero_iff]
    refine exists_congr fun C => and_congr_right fun hC => ?_
    have hpos : (Wc C).toNat ≠ 0 := by
      have := Finsupp.mem_support_iff.mp hC
      have := hWc C
      omega
    rw [map_pow, pow_eq_zero_iff hpos, hG]
  simp_rw [hprod]
  constructor
  · intro h
    by_contra hy
    simp only [Set.mem_iUnion, not_exists] at hy
    obtain ⟨u, v, hu, hv, hn⟩ := exists_not_incidenceLocus_of_forall_notMem Wc.support a haj ha
      (fun C hC => hy C hC)
    obtain ⟨C, hC, hI⟩ := h u v hu hv
    exact hn C hC hI
  · intro hy v v' hv hv'
    obtain ⟨C, hC, hyC⟩ := Set.mem_iUnion₂.mp hy
    exact ⟨C, hC, y, hyC, (linearForm_mem_iff a haj y ha v).mpr hv,
      (linearForm_mem_iff a haj y ha v').mpr hv'⟩

/-- A point `x` of `X` lies on the support of a 1-cycle exactly when its image lies on the
support of the push-forward along the closed immersion `i`. -/
private theorem mem_iUnion_support_pushforward_iff (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)) (x : X) :
    i x ∈ ⋃ C ∈ (Mori.OneCycle.pushforward ℤ (i ≫ projToSpecCoeff k N) (projToSpecCoeff k N) i
        Z).support, closure {C.point} ↔ x ∈ ⋃ C ∈ Z.support, closure {C.point} := by
  classical
  have himg : ∀ C : Mori.ProperCurve (i ≫ projToSpecCoeff k N),
      closure {(ProperCurve.mapClosedImmersion i (projToSpecCoeff k N) C).point} =
        i '' closure {C.point} := fun C => by
    rw [show (ProperCurve.mapClosedImmersion i (projToSpecCoeff k N) C).point = i C.point from rfl,
      ← Set.image_singleton, i.isClosedEmbedding.closure_image_eq]
  rw [pushforward_eq_mapDomain, Finsupp.mapDomain_support_of_injective
    (ProperCurve.mapClosedImmersion_injective i _)]
  simp only [Set.mem_iUnion, Finset.mem_image, exists_prop]
  constructor
  · rintro ⟨_, ⟨C, hC, rfl⟩, hx⟩
    rw [himg] at hx
    obtain ⟨x', hx', hxx⟩ := hx
    exact ⟨C, hC, i.isClosedEmbedding.injective hxx ▸ hx'⟩
  · rintro ⟨C, hC, hx⟩
    exact ⟨_, ⟨C, hC, rfl⟩, by rw [himg]; exact ⟨x, hx, rfl⟩⟩

/-- **The support incidence is closed.** For a morphism `φ` from a variety to the space of forms,
landing in the Chow-form locus `W`, the set of `(s, x)` with `x` on the support of the cycle
`chowCycle (φ s)` is (at closed points) the preimage of the vertex locus, a closed set. -/
private theorem exists_isClosed_supportIncidence
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i] (d : ℕ)
    (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (φ : S ⟶ FormSpace k N d) (hφ : φ ≫ ProjSpace.toSpec k _ = sS) (hφW : ∀ s, φ s ∈ W) :
    ∃ I : Set (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}), IsClosed I ∧
      ∀ p : (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}), IsClosed {p} →
        (p ∈ I ↔ pullback.snd sS (i ≫ projToSpecCoeff k N) p ∈
          ⋃ C ∈ (chowCycle i d (φ (pullback.fst sS (i ≫ projToSpecCoeff k N) p))).support,
            closure {C.point}) := by
  classical
  haveI := finite_bidegree N d
  haveI := Fintype.ofFinite (ULift.{u} (Bidegree N d))
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  set sX := i ≫ projToSpecCoeff k N
  let m : ULift.{u} (Bidegree N d) → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ := fun b => b.down.1
  let Φ := pullback.map sS sX (Intersection.ProjSpace.toSpec k (ULift.{u} (Bidegree N d)))
    (projToSpecCoeff k N) φ i (𝟙 _) (by rw [Category.comp_id, hφ]) (Category.comp_id _)
  refine ⟨Φ ⁻¹' vertexLocus (k := k) m, (isClosed_vertexLocus m).preimage Φ.continuous,
    fun p hp => ?_⟩
  set s := pullback.fst sS sX p
  set x := pullback.snd sS sX p
  have hfst : pullback.fst _ (projToSpecCoeff k N) (Φ p) = φ s := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
  have hsnd : pullback.snd (Intersection.ProjSpace.toSpec k (ULift.{u} (Bidegree N d)))
      (projToSpecCoeff k N) (Φ p) = i x := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
  -- the points `s`, `x`, `φ s` and `i x` are closed
  haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : JacobsonSpace (FormSpace k N d) :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k _)
  haveI : LocallyOfFiniteType (φ ≫ Intersection.ProjSpace.toSpec k _) := hφ ▸ inferInstance
  haveI : LocallyOfFiniteType φ :=
    locallyOfFiniteType_of_comp φ (Intersection.ProjSpace.toSpec k _)
  have hs : IsClosed ({s} : Set S) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints (pullback.fst sS sX) hp
  have hx : IsClosed ({x} : Set X) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints (pullback.snd sS sX) hp
  have hφs : IsClosed ({φ s} : Set (FormSpace k N d)) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints φ hs
  have hix : IsClosed ({i x} : Set (AlgebraicGeometry.Proj (polyGrading k N))) := by
    rw [← Set.image_singleton]
    exact i.isClosedEmbedding.isClosedMap _ hx
  -- the coordinates of `φ s`: the coefficients of its Chow form
  obtain ⟨Z, hZ⟩ := (hW _ hφs).mp (hφW s)
  have hch := isChowPointOf_chowCycle ⟨Z, hZ⟩
  choose G n hG using fun C : Mori.ProperCurve (projToSpecCoeff k N) => exists_incidenceForm C
  set Wc := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i (chowCycle i d (φ s))
  obtain ⟨hFdeg, hrel⟩ := hch.2.2 G fun C _ => ⟨(hG C).1, (hG C).2.1⟩
  set F := ∏ C ∈ Wc.support, G C ^ (Wc C).toNat
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun C _ => pow_ne_zero _ (hG C).1.ne_zero
  obtain ⟨e, he⟩ : F.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h0 => hF (MvPolynomial.support_eq_empty.mp h0))
  let c : ULift.{u} (Bidegree N d) → k := fun b => F.coeff b.down.1
  let b₀ : ULift.{u} (Bidegree N d) := ⟨⟨e, hFdeg e he⟩⟩
  have hc0 : c b₀ ≠ 0 := Finsupp.mem_support_iff.mp he
  have h1 : ∀ (n : ℕ) (g : MvPolynomial (ULift.{u} (Bidegree N d)) k), g.IsHomogeneous n →
      (g ∈ (pullback.fst _ (projToSpecCoeff k N) (Φ p)).asHomogeneousIdeal ↔ eval c g = 0) := by
    intro n g hg
    rw [hfst, mem_iff_eval_of_relations c hc0 _ hrel hg]
    have : (fun b => c b / c b₀) = fun b => (c b₀)⁻¹ * c b := by
      funext b; rw [div_eq_inv_mul]
    rw [this, eval_mul_of_isHomogeneous _ _ hg, mul_eq_zero,
      or_iff_right (pow_ne_zero _ (inv_ne_zero hc0))]
  -- the coordinates of `i x`
  obtain ⟨a, j, haj, ha⟩ := exists_relations_of_isClosed (i x) hix
  have h2 : ∀ (n : ℕ) (g : MvPolynomial (Fin (N + 1)) k), g.IsHomogeneous n →
      (g ∈ (pullback.snd (Intersection.ProjSpace.toSpec k (ULift.{u} (Bidegree N d)))
        (projToSpecCoeff k N) (Φ p)).asHomogeneousIdeal ↔ eval a g = 0) := by
    intro n g hg
    rw [hsnd, mem_iff_eval_of_relations a (b₀ := j) (by simp [haj]) _ ha hg]
    simp [haj]
  rw [Set.mem_preimage, mem_vertexLocus_iff m (Φ p) c a (fun h => hc0 (congrFun h b₀))
    (fun h => by simpa [haj] using congrFun h j) h1 h2]
  have hfe : ∀ v v', formEval (k := k) m c v v' = eval (Sum.elim v v') F :=
    formEval_eq_eval F hFdeg
  simp_rw [hfe]
  rw [forall_eval_prod_eq_zero_iff Wc (pushforward_nonneg i _ hch.1) G (fun C => (hG C).2.1) a haj
    ha]
  exact mem_iUnion_support_pushforward_iff i _ x

section KeyLemma

open HomogeneousLocalization MvPolynomial

attribute [local instance] awayAlgebra

/-- In a Jacobson space the closed points of a locally closed set are dense in it. -/
private theorem subset_closure_inter_closedPoints {Y : Type*} [TopologicalSpace Y] [JacobsonSpace Y]
    {Z O : Set Y} (hZ : IsClosed Z) (hO : IsOpen O) :
    Z ∩ O ⊆ closure (Z ∩ O ∩ closedPoints Y) := by
  intro a ⟨haZ, haO⟩
  rw [mem_closure_iff]
  intro V hV haV
  by_contra hem
  rw [Set.not_nonempty_iff_eq_empty] at hem
  have hsub : Z ∩ closedPoints Y ⊆ (V ∩ O)ᶜ := fun y ⟨hyZ, hyc⟩ ⟨hyV, hyO⟩ =>
    (Set.eq_empty_iff_forall_notMem.mp hem) y ⟨hyV, ⟨hyZ, hyO⟩, hyc⟩
  have := (hV.inter hO).isClosed_compl.closure_subset_iff.mpr hsub
  rw [JacobsonSpace.closure_inter_closedPoints hZ] at this
  exact this haZ ⟨haV, haO⟩

/-- The linear form `∑ⱼ uⱼ Xⱼ` of the hyperplane `H_u ⊆ ℙᴺ`. -/
private noncomputable abbrev hypForm {R : Type*} [CommRing R] {N : ℕ} (u : Fin (N + 1) → R) :
    MvPolynomial (Fin (N + 1)) R :=
  ∑ j, C (u j) * MvPolynomial.X j

/-- At a closed point of a scheme locally of finite type over an algebraically closed field `K`,
the structure morphism induces an isomorphism of residue fields. -/
public theorem isIso_residueFieldMap_of_isClosed {Y : Scheme.{u}} {K : Type u} [Field K]
    [IsAlgClosed K] (f : Y ⟶ Spec (.of K)) [LocallyOfFiniteType f] (x : Y)
    (hx : IsClosed ({x} : Set Y)) : IsIso (f.residueFieldMap x) := by
  set ρ := (residueFieldIsoBase f x hx).inv
  have hρ : Spec.map ρ = Y.fromSpecResidueField x ≫ f := by
    change Spec.map (Spec.preimage _) = _
    exact Spec.map_preimage _
  set σ := Spec.preimage ((Spec (.of K)).fromSpecResidueField (f x))
  have hσρ : σ ≫ f.residueFieldMap x = ρ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      hρ]
  have hbij : Function.Bijective (f.residueFieldMap x) := by
    refine ⟨(f.residueFieldMap x).hom.injective, fun a => ?_⟩
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso ρ).2 a
    exact ⟨σ b, by rw [← hσρ]; rfl⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

/-- Change of coefficients `ℙᴺ_R ⟶ ℙᴺ_k` along a `k`-algebra `R` lies over `Spec R ⟶ Spec k`. -/
private theorem coeffMap_comp_projToSpecCoeff (R : Type u) [CommRing R] [Algebra k R] (N : ℕ) :
    AlgebraicGeometry.Proj.map (coeffGradedHom k N (algebraMap k R))
        (irrelevant_le_map_coeffGradedHom k N _) ≫ projToSpecCoeff k N =
      projToSpecCoeff R N ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
  unfold projToSpecCoeff
  rw [Proj.map_toSpecZero_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  have h1 : (MvPolynomial.C r : MvPolynomial (Fin (N + 1)) k) ∈ polyGrading k N 0 :=
    MvPolynomial.isHomogeneous_C _ r
  have h2 : (MvPolynomial.C (algebraMap k R r) : MvPolynomial (Fin (N + 1)) R) ∈
      polyGrading R N 0 := MvPolynomial.isHomogeneous_C _ _
  simp [DirectSum.decompose_of_mem_same _ h1, DirectSum.decompose_of_mem_same _ h2,
    GradedRingHom.gradedZeroRingHom]

private theorem mem_proj_map_iff {A B σ τ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ}
    {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (g : 𝒜 →+*ᵍ ℬ)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    (y : AlgebraicGeometry.Proj ℬ) (a : A) :
    a ∈ (AlgebraicGeometry.Proj.map g hg y).asHomogeneousIdeal ↔
      g a ∈ y.asHomogeneousIdeal := Iff.rfl

/-- The structure morphism `ℙᴺ_R ⟶ Spec R` sends a homogeneous prime `y` to `{s | C s ∈ y}`. -/
private theorem mem_projToSpecCoeff_iff (R : Type u) [CommRing R] (N : ℕ)
    (y : AlgebraicGeometry.Proj (polyGrading R N)) (s : R) :
    s ∈ (projToSpecCoeff R N y).asIdeal ↔ MvPolynomial.C s ∈ y.asHomogeneousIdeal := by
  have h : (MvPolynomial.C s : MvPolynomial (Fin (N + 1)) R) ∈ polyGrading R N 0 :=
    MvPolynomial.isHomogeneous_C _ s
  have h0 : ((GradedRing.projZeroRingHom (polyGrading R N)) (C s) : MvPolynomial (Fin (N + 1)) R) =
      C s := by
    rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_same _ h]
  have key : (projToSpecCoeff R N y).asIdeal =
      Ideal.comap ((GradedRing.projZeroRingHom' (polyGrading R N)).comp
        (algebraMap R (MvPolynomial (Fin (N + 1)) R)))
        (Proj.toSpecZero (polyGrading R N) y).asIdeal := rfl
  rw [key, Ideal.mem_comap, Stacks.AlgebraicGeometry.ProjToSpecZero.toSpecZero_apply]
  change ((GradedRing.projZeroRingHom (polyGrading R N)) (C s) : MvPolynomial (Fin (N + 1)) R) ∈
    y.asHomogeneousIdeal ↔ _
  rw [h0]

/-- In a Jacobson space a nonempty locally closed set contains a closed point. -/
private theorem exists_isClosed_singleton_of_nonempty {Y : Type*} [TopologicalSpace Y]
    [JacobsonSpace Y] {Z O : Set Y} (hZ : IsClosed Z) (hO : IsOpen O) (h : (Z ∩ O).Nonempty) :
    ∃ y ∈ Z ∩ O, IsClosed ({y} : Set Y) := by
  obtain ⟨y, hy⟩ := h
  have h2 := subset_closure_inter_closedPoints hZ hO hy
  by_contra hcon
  push Not at hcon
  have : Z ∩ O ∩ closedPoints Y = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun y' hy' => hcon y' hy'.1 hy'.2
  rw [this, closure_empty] at h2
  exact h2

/-- Two commuting squares over a common base `e` give the commuting square needed to map the
pullback `P ×_{Spec R} Pr` to `B ×_k Pk`. -/
private theorem pullback_fst_comp_comm {C : Type*} [Category C] {P Pr B Pk E S : C}
    (f₁ : P ⟶ B) (s : P ⟶ E) (pr : Pr ⟶ E) (c : Pr ⟶ Pk) (sB : B ⟶ S) (pk : Pk ⟶ S)
    (e : E ⟶ S) [HasPullback s pr] (h₁ : f₁ ≫ sB = s ≫ e) (h₂ : c ≫ pk = pr ≫ e) :
    (pullback.fst s pr ≫ f₁) ≫ sB = (pullback.snd s pr ≫ c) ≫ pk := by
  rw [Category.assoc, Category.assoc, h₁, h₂, ← Category.assoc, pullback.condition,
    Category.assoc]

/-- **No incidence over a root avoiding `T`.** Let `P` be a scheme over `B` and over `Spec R`,
`Φ : P ×_R ℙᴺ_R ⟶ B ×ₖ ℙᴺ_k` the induced map, and `q₀` a closed point of `P` over `b₀` at which
`t_R` vanishes. If no closed point of `T` over `b₀` lies on both hyperplanes `H_{x₀'}` and
`H_{x₀''}`, then no point of `Φ⁻¹ T` over `q₀` lies on both hyperplanes
`H_{x₀' + t_R w'}` and `H_{x₀'' + t_R w''}`. -/
private theorem notMem_image_incidence {N : ℕ} {B : Scheme.{u}} {sB : B ⟶ Spec (.of k)}
    {T : Set (pullback sB (projToSpecCoeff k N) : Scheme.{u})} (hT : IsClosed T) {b₀ : B}
    {x₀ w : Fin (N + 1) ⊕ Fin (N + 1) → k}
    (havoid : ∀ z ∈ T, IsClosed ({z} : Set _) → pullback.fst sB (projToSpecCoeff k N) z = b₀ →
      ¬ (hypForm (x₀ ∘ Sum.inl) ∈ (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal ∧
        hypForm (x₀ ∘ Sum.inr) ∈ (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal))
    {R : Type u} [CommRing R] [Algebra k R] (tR : R) {P : Scheme.{u}} (gB : P ⟶ B)
    (sndP : P ⟶ Spec (.of R)) (prR : AlgebraicGeometry.Proj (polyGrading R N) ⟶ Spec (.of R))
    (hprRmem : ∀ (y : AlgebraicGeometry.Proj (polyGrading R N)) (s : R),
      s ∈ (prR y).asIdeal ↔ MvPolynomial.C s ∈ y.asHomogeneousIdeal)
    [JacobsonSpace (pullback sndP prR : Scheme.{u})]
    [JacobsonSpace (pullback sB (projToSpecCoeff k N) : Scheme.{u})]
    (Φ : pullback sndP prR ⟶ pullback sB (projToSpecCoeff k N)) [LocallyOfFiniteType Φ]
    (hΦ₁ : Φ ≫ pullback.fst sB (projToSpecCoeff k N) = pullback.fst sndP prR ≫ gB)
    (hΦ₂ : Φ ≫ pullback.snd sB (projToSpecCoeff k N) = pullback.snd sndP prR ≫
      AlgebraicGeometry.Proj.map (coeffGradedHom k N (algebraMap k R))
        (irrelevant_le_map_coeffGradedHom k N _))
    {q₀ : P} (hq₀c : IsClosed ({q₀} : Set P)) (hq₀f : gB q₀ = b₀)
    (hq₀t : tR ∈ (sndP q₀).asIdeal) :
    q₀ ∉ pullback.fst sndP prR '' (Φ ⁻¹' T ∩ pullback.snd sndP prR ⁻¹'
      ProjectiveSpectrum.zeroLocus (polyGrading R N)
        {hypForm (fun i => algebraMap k R (x₀ (Sum.inl i)) + tR * algebraMap k R (w (Sum.inl i))),
          hypForm (fun i => algebraMap k R (x₀ (Sum.inr i)) + tR * algebraMap k R (w (Sum.inr i)))}) := by
  set fst' := pullback.fst sndP prR
  set snd' := pullback.snd sndP prR
  set hu : MvPolynomial (Fin (N + 1)) R :=
    hypForm (fun i => algebraMap k R (x₀ (Sum.inl i)) + tR * algebraMap k R (w (Sum.inl i)))
  set hv : MvPolynomial (Fin (N + 1)) R :=
    hypForm (fun i => algebraMap k R (x₀ (Sum.inr i)) + tR * algebraMap k R (w (Sum.inr i)))
  have hK : IsClosed (Φ ⁻¹' T ∩ snd' ⁻¹' ProjectiveSpectrum.zeroLocus (polyGrading R N) {hu, hv}) :=
    (hT.preimage Φ.continuous).inter
      ((ProjectiveSpectrum.isClosed_zeroLocus _ _).preimage snd'.continuous)
  rintro ⟨y₁, hy₁K, hy₁q⟩
  obtain ⟨y, ⟨⟨hyK, hyq⟩, -⟩, hyc⟩ := exists_isClosed_singleton_of_nonempty
    (hK.inter (hq₀c.preimage fst'.continuous)) isOpen_univ
    ⟨y₁, ⟨hy₁K, by rwa [Set.mem_preimage, Set.mem_singleton_iff]⟩, trivial⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hyq
  have hzc : IsClosed ({Φ y} : Set (pullback sB (projToSpecCoeff k N) : Scheme.{u})) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints Φ hyc
  have hzf : pullback.fst sB (projToSpecCoeff k N) (Φ y) = b₀ := by
    rw [← Scheme.Hom.comp_apply Φ (pullback.fst sB (projToSpecCoeff k N)) y, hΦ₁,
      Scheme.Hom.comp_apply, hyq, hq₀f]
  have hsnd : pullback.snd sB (projToSpecCoeff k N) (Φ y) =
      AlgebraicGeometry.Proj.map (coeffGradedHom k N (algebraMap k R))
        (irrelevant_le_map_coeffGradedHom k N _) (snd' y) := by
    rw [← Scheme.Hom.comp_apply Φ (pullback.snd sB (projToSpecCoeff k N)) y, hΦ₂,
      Scheme.Hom.comp_apply]
  have htR : MvPolynomial.C tR ∈ (snd' y).asHomogeneousIdeal := by
    rw [← hprRmem, ← Scheme.Hom.comp_apply snd' prR y, ← pullback.condition,
      Scheme.Hom.comp_apply, hyq]
    exact hq₀t
  have hcoeff : ∀ v : Fin (N + 1) → k, coeffGradedHom k N (algebraMap k R) (hypForm v) =
      hypForm (fun i => algebraMap k R (v i)) := fun v => by
    simp only [hypForm, coeffGradedHom_apply, map_sum, map_mul, MvPolynomial.map_C,
      MvPolynomial.map_X]
  have hline : ∀ v v' : Fin (N + 1) → k,
      hypForm (fun i => algebraMap k R (v i) + tR * algebraMap k R (v' i)) =
        hypForm (fun i => algebraMap k R (v i)) +
          MvPolynomial.C tR * hypForm (fun i => algebraMap k R (v' i)) :=
    fun v v' => by
      simp only [hypForm, map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
        mul_assoc]
  refine havoid _ hyK.1 hzc hzf ⟨?_, ?_⟩
  · rw [hsnd, mem_proj_map_iff, hcoeff]
    have h1 : hu ∈ (snd' y).asHomogeneousIdeal := hyK.2 (Set.mem_insert _ _)
    have h2 := Ideal.mul_mem_right (hypForm (fun i => algebraMap k R (w (Sum.inl i))))
      (snd' y).asHomogeneousIdeal.toIdeal htR
    have h3 := (snd' y).asHomogeneousIdeal.toIdeal.sub_mem h1 h2
    rwa [show hu = _ from hline _ _, add_sub_cancel_right] at h3
  · rw [hsnd, mem_proj_map_iff, hcoeff]
    have h1 : hv ∈ (snd' y).asHomogeneousIdeal :=
      hyK.2 (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have h2 := Ideal.mul_mem_right (hypForm (fun i => algebraMap k R (w (Sum.inr i))))
      (snd' y).asHomogeneousIdeal.toIdeal htR
    have h3 := (snd' y).asHomogeneousIdeal.toIdeal.sub_mem h1 h2
    rwa [show hv = _ from hline _ _, add_sub_cancel_right] at h3

/-- **Incidence over a root on both hyperplanes.** In the setting of `notMem_image_incidence`,
let `ψ : R ⟶ k` be a `k`-point with kernel the point `q` of `P`, sending `t_R` to `t`. A closed
point `z` of `T` over `q` on both hyperplanes `H_{x₀' + t w'}` and `H_{x₀'' + t w''}` lifts to a
point of `Φ⁻¹ T` over `q` on both hyperplanes `H_{x₀' + t_R w'}` and `H_{x₀'' + t_R w''}`. -/
private theorem mem_image_incidence {N : ℕ} {B : Scheme.{u}} {sB : B ⟶ Spec (.of k)}
    [LocallyOfFiniteType sB] {T : Set (pullback sB (projToSpecCoeff k N) : Scheme.{u})}
    {x₀ w : Fin (N + 1) ⊕ Fin (N + 1) → k}
    {R : Type u} [CommRing R] [Algebra k R] (tR : R) {P : Scheme.{u}} (gB : P ⟶ B)
    (sndP : P ⟶ Spec (.of R)) (prR : AlgebraicGeometry.Proj (polyGrading R N) ⟶ Spec (.of R))
    (hprRmem : ∀ (y : AlgebraicGeometry.Proj (polyGrading R N)) (s : R),
      s ∈ (prR y).asIdeal ↔ MvPolynomial.C s ∈ y.asHomogeneousIdeal)
    (Φ : pullback sndP prR ⟶ pullback sB (projToSpecCoeff k N))
    (hΦ₁ : Φ ≫ pullback.fst sB (projToSpecCoeff k N) = pullback.fst sndP prR ≫ gB)
    (hΦ₂ : Φ ≫ pullback.snd sB (projToSpecCoeff k N) = pullback.snd sndP prR ≫
      AlgebraicGeometry.Proj.map (coeffGradedHom k N (algebraMap k R))
        (irrelevant_le_map_coeffGradedHom k N _))
    (q : P) (ψt : R →+* k) (hψt : ∀ s : k, ψt (algebraMap k R s) = s) (t : k)
    (hψtX : ψt tR = t) (hrt : (sndP q).asIdeal = RingHom.ker ψt)
    {z : (pullback sB (projToSpecCoeff k N) : Scheme.{u})} (hzT : z ∈ T)
    (hzc : IsClosed ({z} : Set _)) (hzf : pullback.fst sB (projToSpecCoeff k N) z = gB q)
    (hzu : hypForm ((x₀ + t • w) ∘ Sum.inl) ∈
      (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal)
    (hzv : hypForm ((x₀ + t • w) ∘ Sum.inr) ∈
      (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal) :
    q ∈ pullback.fst sndP prR '' (Φ ⁻¹' T ∩ pullback.snd sndP prR ⁻¹'
      ProjectiveSpectrum.zeroLocus (polyGrading R N)
        {hypForm (fun i => algebraMap k R (x₀ (Sum.inl i)) + tR * algebraMap k R (w (Sum.inl i))),
          hypForm (fun i => algebraMap k R (x₀ (Sum.inr i)) + tR * algebraMap k R (w (Sum.inr i)))}) := by
  haveI := jacobsonSpace_proj k N
  haveI : LocallyOfFiniteType (projToSpecCoeff k N) := by
    haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
    infer_instance
  haveI : LocallyOfFiniteType (pullback.snd sB (projToSpecCoeff k N)) := inferInstance
  have hzsc : IsClosed ({pullback.snd sB (projToSpecCoeff k N) z} :
      Set (AlgebraicGeometry.Proj (polyGrading k N))) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints _ hzc
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = AlgebraicGeometry.Proj.map (coeffGradedHom R N ψt)
      (irrelevant_le_map_coeffGradedHom R N ψt) (pullback.snd sB (projToSpecCoeff k N) z) :=
    ⟨_, rfl⟩
  have hYmem : ∀ g, g ∈ Y.asHomogeneousIdeal ↔
      MvPolynomial.map ψt g ∈ (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal :=
    fun g => by rw [hYdef]; exact mem_proj_map_iff _ _ _ _
  have hY : prR Y = sndP q := by
    refine PrimeSpectrum.ext (Ideal.ext fun s => ?_)
    rw [hprRmem, hYmem, hrt, RingHom.mem_ker, MvPolynomial.map_C]
    constructor
    · intro h
      by_contra hne
      exact (pullback.snd sB (projToSpecCoeff k N) z).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ h ((IsUnit.mk0 _ hne).map MvPolynomial.C))
    · intro h
      rw [h, map_zero]
      exact zero_mem _
  obtain ⟨y, hyf, hys⟩ := Scheme.Pullback.exists_preimage_pullback (f := sndP) (g := prR) q Y
    hY.symm
  refine ⟨y, ⟨?_, ?_⟩, hyf⟩
  · have hfst : pullback.fst sB (projToSpecCoeff k N) (Φ y) =
        pullback.fst sB (projToSpecCoeff k N) z := by
      rw [← Scheme.Hom.comp_apply Φ (pullback.fst sB (projToSpecCoeff k N)) y, hΦ₁,
        Scheme.Hom.comp_apply, hyf, hzf]
    have hsnd : pullback.snd sB (projToSpecCoeff k N) (Φ y) =
        pullback.snd sB (projToSpecCoeff k N) z := by
      rw [← Scheme.Hom.comp_apply Φ (pullback.snd sB (projToSpecCoeff k N)) y, hΦ₂,
        Scheme.Hom.comp_apply, hys]
      refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective (Ideal.ext fun g => ?_))
      change g ∈ (AlgebraicGeometry.Proj.map (coeffGradedHom k N (algebraMap k R))
        (irrelevant_le_map_coeffGradedHom k N _) Y).asHomogeneousIdeal ↔ _
      rw [mem_proj_map_iff, hYmem, coeffGradedHom_apply, MvPolynomial.map_map]
      have : ψt.comp (algebraMap k R) = RingHom.id k := RingHom.ext hψt
      rw [this, MvPolynomial.map_id]
      exact Iff.rfl
    have := Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap sB
      (projToSpecCoeff k N) (Φ y) z hfst hsnd
      (isIso_residueFieldMap_of_isClosed (projToSpecCoeff k N) _ hzsc)
    rw [Set.mem_preimage, this]
    exact hzT
  · change ({_, _} : Set (MvPolynomial (Fin (N + 1)) R)) ⊆
      (pullback.snd sndP prR y).asHomogeneousIdeal
    rw [hys]
    intro g hg
    rcases hg with rfl | hg
    · rw [SetLike.mem_coe, hYmem]
      convert hzu using 1
      simp [hypForm, hψt, hψtX]
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      rw [SetLike.mem_coe, hYmem]
      convert hzv using 1
      simp [hypForm, hψt, hψtX]

/-- **Avoiding a closed family along a line through a root.** Let `φ : B ⟶ ℙ^ι_k` be a family of
forms `F_b = ∑_β c_β x^{m_β}` of degree `D`, and `T ⊆ B ×ₖ ℙᴺ_k` closed. If `F_{b₀}(x₀) = 0` and
no closed point of `T` over `b₀` lies on both hyperplanes `H_{x₀'}` and `H_{x₀''}` given by the
two halves of `x₀`, then for all closed `b` near `b₀` there is a zero `x` of `F_b` with the same
property: the zeros of `F_b` on the line through `x₀` in a direction `w` with `F_{b₀}(w) ≠ 0` are
the roots of a monic polynomial, which move openly with `b`. -/
private theorem exists_isOpen_forall_exists_formLin_mem {ι : Type u} [Fintype ι]
    {N : ℕ} (m : ι → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ) (hm : Function.Injective m) {D : ℕ}
    (hD : ∀ b, ∑ j, m b j = D) {B : Scheme.{u}} (sB : B ⟶ Spec (.of k)) [LocallyOfFiniteType sB]
    (φ : B ⟶ Intersection.ProjSpace k ι) (hφ : φ ≫ Intersection.ProjSpace.toSpec k ι = sB)
    (T : Set (pullback sB (projToSpecCoeff k N) : Scheme.{u})) (hT : IsClosed T)
    {b₀ : B} (hb₀ : IsClosed ({b₀} : Set B)) (x₀ : Fin (N + 1) ⊕ Fin (N + 1) → k)
    (hroot : formLin m x₀ ∈ (φ b₀).asHomogeneousIdeal)
    (havoid : ∀ z ∈ T, IsClosed ({z} : Set _) → pullback.fst sB (projToSpecCoeff k N) z = b₀ →
      ¬ (hypForm (x₀ ∘ Sum.inl) ∈ (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal ∧
        hypForm (x₀ ∘ Sum.inr) ∈ (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal)) :
    ∃ O : Set B, IsOpen O ∧ b₀ ∈ O ∧ ∀ b ∈ O, IsClosed ({b} : Set B) →
      ∃ x : Fin (N + 1) ⊕ Fin (N + 1) → k, formLin m x ∈ (φ b).asHomogeneousIdeal ∧
        ∀ z ∈ T, IsClosed ({z} : Set _) → pullback.fst sB (projToSpecCoeff k N) z = b →
          ¬ (hypForm (x ∘ Sum.inl) ∈ (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal ∧
            hypForm (x ∘ Sum.inr) ∈ (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal) := by
  classical
  -- the coordinates of `φ b₀`, and a direction `w` with `F_{b₀}(w) ≠ 0`
  haveI : LocallyOfFiniteType (φ ≫ Intersection.ProjSpace.toSpec k ι) := hφ ▸ inferInstance
  haveI : LocallyOfFiniteType φ :=
    locallyOfFiniteType_of_comp φ (Intersection.ProjSpace.toSpec k ι)
  haveI : JacobsonSpace (Intersection.ProjSpace k ι) :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k ι)
  haveI : JacobsonSpace B := LocallyOfFiniteType.jacobsonSpace sB
  have hφb₀ : IsClosed ({φ b₀} : Set (Intersection.ProjSpace k ι)) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints φ hb₀
  obtain ⟨a, j, haj, ha⟩ := exists_relations_of_isClosed (φ b₀) hφb₀
  have ha0 : a j ≠ 0 := by simp [haj]
  obtain ⟨w, hw⟩ : ∃ w, eval a (formLin m w) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hP : (∑ b, C (a b) * monomial (m b) (1 : k) :
        MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) = 0 := by
      refine MvPolynomial.funext fun x => ?_
      rw [map_zero, ← hall x, eval_formLin, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [eval_mul, eval_C, eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    have := congrArg (fun p : MvPolynomial _ _ => p.coeff (m j)) hP
    rw [coeff_sum, Finset.sum_eq_single j] at this
    · simp [coeff_C_mul, coeff_monomial, haj] at this
    · intro b _ hb
      rw [coeff_C_mul, coeff_monomial, if_neg (fun h => hb (hm h)), mul_zero]
    · simp
  set f := formLin m w with hfdef
  have hf : f ∈ homogeneousSubmodule ι k 1 := isHomogeneous_formLin m w
  have hφmem : ∀ {b : B} {c : ι → k} {l : ι}, c l = 1 →
      (∀ β β', c β' • (MvPolynomial.X β : MvPolynomial ι k) - c β • MvPolynomial.X β' ∈ (φ b).asHomogeneousIdeal) →
      ∀ {n : ℕ} {g : MvPolynomial ι k}, g.IsHomogeneous n →
        (g ∈ (φ b).asHomogeneousIdeal ↔ eval c g = 0) := by
    intro b c l hcl hc n g hg
    rw [mem_iff_eval_of_relations c (b₀ := l) (by simp [hcl]) (φ b) hc hg]
    simp [hcl]
  have hfb₀ : f ∉ (φ b₀).asHomogeneousIdeal := by
    rw [hφmem haj ha (isHomogeneous_formLin m w)]
    exact hw
  -- the chart `V = φ⁻¹ D₊(f) ⟶ Spec A⁰_f`
  set 𝒜 := homogeneousSubmodule ι k
  set ιf := Proj.awayι 𝒜 f hf one_pos
  set V : B.Opens := φ ⁻¹ᵁ (Proj.basicOpen 𝒜 f)
  have hb₀V : b₀ ∈ V := hfb₀
  let ψV : V.toScheme ⟶ Spec (.of (Away 𝒜 f)) := IsOpenImmersion.lift ιf (V.ι ≫ φ) (by
    rintro _ ⟨x, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    exact x.2)
  have hψV : ψV ≫ ιf = V.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have hVmem : ∀ x : V.toScheme, f ∉ (φ (V.ι x)).asHomogeneousIdeal := fun x => x.2
  clear_value ψV
  -- the root scheme `Spec A⁰_f[t]/(g) ⟶ Spec A⁰_f`, finite free
  set R := RootRing m x₀ w D
  let πR : Spec (.of R) ⟶ Spec (.of (Away 𝒜 f)) := Spec.map (CommRingCat.ofHom (algebraMap _ R))
  haveI : Module.Free (Away 𝒜 f) R := (rootPoly_monic m hD x₀ w).free_quotient
  haveI : Algebra.FinitePresentation (Away 𝒜 f) R :=
    Algebra.FinitePresentation.quotient ⟨{rootPoly m x₀ w D}, by simp⟩
  haveI : Flat πR := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : LocallyOfFinitePresentation πR :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  haveI : UniversallyOpen πR := UniversallyOpen.of_flat πR
  -- `P = V ×_{A⁰_f} Spec R`, and `P' = P ×_R ℙᴺ_R`
  haveI : IsOpenMap (pullback.fst ψV πR) := (pullback.fst ψV πR).isOpenMap
  set prR := projToSpecCoeff R N with hprR
  haveI : IsProper prR := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := R) N
  have hprRmem : ∀ (y : AlgebraicGeometry.Proj (polyGrading R N)) (s : R),
      s ∈ (prR y).asIdeal ↔ MvPolynomial.C s ∈ y.asHomogeneousIdeal :=
    mem_projToSpecCoeff_iff R N
  clear_value prR
  let fstP := pullback.fst ψV πR
  let sndP := pullback.snd ψV πR
  let fst' := pullback.fst sndP prR
  let snd' := pullback.snd sndP prR
  obtain ⟨cM, hcM⟩ : ∃ g, g = AlgebraicGeometry.Proj.map (coeffGradedHom k N (algebraMap k R))
    (irrelevant_le_map_coeffGradedHom k N _) := ⟨_, rfl⟩
  have hVs : V.ι ≫ sB = ψV ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 f))) := by
    rw [← hφ, ← Category.assoc, ← hψV, Category.assoc, awayι_comp_toSpec]
  have hRs : πR ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 f))) =
      Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hπR : ∀ (r : Spec (.of R)) (α : Away 𝒜 f),
      α ∈ (πR r).asIdeal ↔ algebraMap _ R α ∈ r.asIdeal := fun _ _ => Iff.rfl
  clear_value πR
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ Φ : pullback sndP prR ⟶ pullback sB (projToSpecCoeff k N),
      Φ ≫ pullback.fst sB (projToSpecCoeff k N) = fst' ≫ fstP ≫ V.ι ∧
        Φ ≫ pullback.snd sB (projToSpecCoeff k N) = snd' ≫ cM :=
    have h₁ : (fstP ≫ V.ι) ≫ sB = sndP ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
      rw [Category.assoc, hVs, ← Category.assoc fstP, pullback.condition, Category.assoc, hRs]
    have h₂ : cM ≫ projToSpecCoeff k N = prR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
      rw [hcM, coeffMap_comp_projToSpecCoeff, ← hprR]
    ⟨pullback.lift (fst' ≫ fstP ≫ V.ι) (snd' ≫ cM)
      (pullback_fst_comp_comm (fstP ≫ V.ι) sndP prR cM sB (projToSpecCoeff k N) _ h₁ h₂),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- the hyperplanes `H_{x₀ + t w}` over `R`, and the incidence locus `Inc ⊆ P`
  let tR : R := Ideal.Quotient.mk _ Polynomial.X
  let hu : MvPolynomial (Fin (N + 1)) R :=
    hypForm (fun i => algebraMap k R (x₀ (Sum.inl i)) + tR * algebraMap k R (w (Sum.inl i)))
  let hv : MvPolynomial (Fin (N + 1)) R :=
    hypForm (fun i => algebraMap k R (x₀ (Sum.inr i)) + tR * algebraMap k R (w (Sum.inr i)))
  let K : Set (pullback sndP prR : Scheme.{u}) := Φ ⁻¹' T ∩
    snd' ⁻¹' (ProjectiveSpectrum.zeroLocus (polyGrading R N) {hu, hv})
  have hK : IsClosed K := (hT.preimage Φ.continuous).inter
    ((ProjectiveSpectrum.isClosed_zeroLocus _ _).preimage snd'.continuous)
  let Inc : Set (pullback ψV πR : Scheme.{u}) := fst' '' K
  have hInc : IsClosed Inc := fst'.isClosedMap _ hK
  -- points of the chart
  have hψVpt : ∀ b' : V.toScheme, ιf (ψV b') = φ (V.ι b') := fun b' => by
    rw [← Scheme.Hom.comp_apply, hψV, Scheme.Hom.comp_apply]
  have hker : ∀ (b' : V.toScheme) (c : ι → k) (l : ι), c l = 1 →
      (∀ β β', c β' • (MvPolynomial.X β : MvPolynomial ι k) - c β • MvPolynomial.X β' ∈ (φ (V.ι b')).asHomogeneousIdeal) →
      ∀ (hcf : eval c f ≠ 0) (α : Away 𝒜 f), α ∈ (ψV b').asIdeal ↔ awayEval f c hcf α = 0 :=
    fun b' c l hcl hc hcf α => mem_iff_awayEval_eq_zero hf c hcf (ψV b')
      (fun n g hg => by rw [hψVpt]; exact hφmem hcl hc hg) α
  -- the root `t = 0` over `b₀`
  let b₀' : V.toScheme := ⟨b₀, hb₀V⟩
  have hb₀' : V.ι b₀' = b₀ := rfl
  have h0 : ((rootPoly m x₀ w D).map (awayEval f a hw).toRingHom).eval 0 = 0 := by
    rw [eval_map_awayEval_rootPoly m hD x₀ w a hw 0, zero_smul, add_zero,
      (hφmem haj ha (isHomogeneous_formLin m x₀)).mp hroot, zero_mul]
  let r₀ : Spec (.of R) := ⟨RingHom.ker (rootEval (awayEval f a hw) 0 h0), RingHom.ker_isPrime _⟩
  have hr₀ : πR r₀ = ψV b₀' := by
    refine PrimeSpectrum.ext (Ideal.ext fun α => ?_)
    rw [hπR, hker b₀' a j haj ha hw]
    exact (rootEval_algebraMap _ 0 h0 α).symm ▸ Iff.rfl
  -- finiteness and Jacobson spaces
  haveI : LocallyOfFiniteType (fstP ≫ V.ι ≫ sB) := inferInstance
  haveI : JacobsonSpace (pullback ψV πR : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (fstP ≫ V.ι ≫ sB)
  haveI : LocallyOfFiniteType (fst' ≫ fstP ≫ V.ι ≫ sB) := inferInstance
  haveI : JacobsonSpace (pullback sndP prR : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (fst' ≫ fstP ≫ V.ι ≫ sB)
  haveI : LocallyOfFiniteType (projToSpecCoeff k N) := by
    haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
    infer_instance
  haveI : LocallyOfFiniteType (pullback.fst sB (projToSpecCoeff k N)) := inferInstance
  haveI : LocallyOfFiniteType (pullback.fst sB (projToSpecCoeff k N) ≫ sB) := inferInstance
  haveI : JacobsonSpace (pullback sB (projToSpecCoeff k N) : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst sB (projToSpecCoeff k N) ≫ sB)
  haveI : LocallyOfFiniteType (Φ ≫ pullback.fst sB (projToSpecCoeff k N) ≫ sB) := by
    rw [← Category.assoc, hΦ₁]; infer_instance
  haveI : LocallyOfFiniteType Φ := locallyOfFiniteType_of_comp Φ
    (pullback.fst sB (projToSpecCoeff k N) ≫ sB)
  -- the closed point `q₀` of `P` over `(b₀, 0)`
  have hb₀'c : IsClosed ({b₀'} : Set V.toScheme) := by
    have : ({b₀'} : Set V.toScheme) = V.ι ⁻¹' {b₀} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hb₀', fun h => V.ι.isOpenEmbedding.injective (h.trans hb₀'.symm)⟩
    rw [this]
    exact hb₀.preimage V.ι.continuous
  have hr₀c : IsClosed ({r₀} : Set (Spec (.of R))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal r₀).mpr
      (RingHom.ker_isMaximal_of_surjective _ fun s =>
        ⟨algebraMap k R s, rootEval_algebraMap_base _ 0 h0 s⟩)
  obtain ⟨q₁, hq₁f, hq₁s⟩ := Scheme.Pullback.exists_preimage_pullback b₀' r₀ hr₀.symm
  obtain ⟨q₀, ⟨⟨hq₀f, hq₀s⟩, -⟩, hq₀c⟩ := exists_isClosed_singleton_of_nonempty
    ((hb₀'c.preimage fstP.continuous).inter (hr₀c.preimage sndP.continuous)) isOpen_univ
    ⟨q₁, ⟨hq₁f, hq₁s⟩, trivial⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hq₀f hq₀s
  -- `q₀` is not in the incidence locus
  have hq₀Inc : q₀ ∉ Inc := by
    have hq₀t : tR ∈ (sndP q₀).asIdeal := by
      rw [hq₀s]
      show rootEval _ 0 h0 tR = 0
      exact rootEval_X _ 0 h0
    exact notMem_image_incidence hT havoid tR (fstP ≫ V.ι) sndP prR hprRmem Φ hΦ₁
      (by rw [hΦ₂, hcM]) hq₀c (by rw [Scheme.Hom.comp_apply, hq₀f, hb₀']) hq₀t
  -- the open set `O`
  refine ⟨V.ι '' (fstP '' Incᶜ), V.ι.isOpenEmbedding.isOpenMap _
    ((pullback.fst ψV πR).isOpenMap _ hInc.isOpen_compl), ⟨b₀', ⟨q₀, hq₀Inc, hq₀f⟩, hb₀'⟩, ?_⟩
  rintro _ ⟨_, ⟨q, hqInc, rfl⟩, rfl⟩ hbc
  -- the coordinates of `φ b`
  have hφb : IsClosed ({φ (V.ι (fstP q))} : Set (Intersection.ProjSpace k ι)) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints φ hbc
  obtain ⟨c, l, hcl, hc⟩ := exists_relations_of_isClosed _ hφb
  have hcf : eval c f ≠ 0 := by
    have := hVmem (fstP q)
    rwa [hφmem hcl hc (isHomogeneous_formLin m w)] at this
  -- the root `t` of `g` over `b` given by `q`
  haveI : (sndP q).asIdeal.IsPrime := (sndP q).isPrime
  obtain ⟨t, ht, hrt⟩ := exists_eq_ker_rootEval hD (awayEval f c hcf) (sndP q).asIdeal
    (fun α => by
      rw [← hπR, ← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply,
        hker _ c l hcl hc hcf])
  refine ⟨x₀ + t • w, ?_, ?_⟩
  · rw [hφmem hcl hc (isHomogeneous_formLin m _)]
    have := eval_map_awayEval_rootPoly m hD x₀ w c hcf t
    rw [ht] at this
    exact (mul_eq_zero.mp this.symm).resolve_right (inv_ne_zero hcf)
  · rintro z hzT hzc hzf ⟨hzu, hzv⟩
    exact hqInc (mem_image_incidence tR (fstP ≫ V.ι) sndP prR hprRmem Φ hΦ₁ (by rw [hΦ₂, hcM])
      q (rootEval (awayEval f c hcf) t ht) (rootEval_algebraMap_base _ t ht) t
      (rootEval_X _ t ht) hrt hzT hzc (hzf.trans (Scheme.Hom.comp_apply _ _ _).symm) hzu hzv)

end KeyLemma

/-- In a `T₀` space, a specialization `a ⤳ b` with `a ≠ b` gives dimension at least one. -/
private theorem one_le_topologicalKrullDim_of_specializes {Y : Type*} [TopologicalSpace Y]
    [T0Space Y] {a b : Y} (hab : a ⤳ b) (hne : a ≠ b) : 1 ≤ topologicalKrullDim Y := by
  let f : Fin 2 → TopologicalSpace.IrreducibleCloseds Y := fun j =>
    ⟨closure {![b, a] j}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : f 0 < f 1 := by
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp hab) fun h => hne ?_
    have : b ⤳ a := specializes_iff_closure_subset.mpr
      (le_of_eq (congrArg TopologicalSpace.IrreducibleCloseds.carrier h).symm)
    exact (hab.antisymm this).eq
  have hmono : StrictMono f := by
    rw [Fin.strictMono_iff_lt_succ]
    intro j
    fin_cases j
    exact hlt
  exact_mod_cast Order.le_krullDim_iff.mpr ⟨LTSeries.mk 1 f hmono, rfl⟩

/-- The section `Y ⟶ S ×ₖ Y`, `y ↦ (s, y)`, at a closed point `s` of a scheme locally of finite
type over an algebraically closed field; every closed point of `S ×ₖ Y` over `s` is on it. -/
private theorem exists_section_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {S Y : Scheme.{u}} (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS] (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] {s : S} (hs : IsClosed ({s} : Set S)) :
    ∃ j : Y ⟶ pullback sS sY, j ≫ pullback.snd sS sY = 𝟙 Y ∧
      (∀ y, pullback.snd sS sY (j y) = y) ∧ (∀ y, pullback.fst sS sY (j y) = s) ∧
      ∀ z, pullback.fst sS sY z = s → IsClosed ({pullback.snd sS sY z} : Set Y) →
        z = j (pullback.snd sS sY z) := by
  set e := residueFieldIsoBase sS s hs
  have he : Spec.map e.inv = S.fromSpecResidueField s ≫ sS := by
    change Spec.map (Spec.preimage _) = _
    exact Spec.map_preimage _
  let σ : Spec (.of k) ⟶ S := Spec.map e.hom ≫ S.fromSpecResidueField s
  have hσ : σ ≫ sS = 𝟙 _ := by
    rw [Category.assoc, ← he, ← Spec.map_comp, e.inv_hom_id, Spec.map_id]
  set j : Y ⟶ pullback sS sY := pullback.lift (sY ≫ σ) (𝟙 Y) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hjs : ∀ y, pullback.snd sS sY (j y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    rfl
  have hjf : ∀ y, pullback.fst sS sY (j y) = s := fun y => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  refine ⟨j, pullback.lift_snd _ _ _, hjs, hjf, fun z hz hzc => ?_⟩
  have hwc : IsClosed ({pullback.snd sS sY (j (pullback.snd sS sY z))} : Set Y) := by
    rwa [hjs]
  exact Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap sS sY _ _
    (by rw [hz, hjf]) (hjs _).symm (isIso_residueFieldMap_of_isClosed sY _ hwc)
/-- At the Chow point `[F]` of an effective cycle `Z`, the linear form `L_{(u, v)}` vanishes exactly
when `F(u, v) = 0`, i.e. when some component of `Z` meets `H_u ∩ H_v`. -/
private theorem formLin_mem_iff_exists_incidenceLocus
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i] {d : ℕ}
    [Fintype (ULift.{u} (Bidegree N d))] {Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)}
    {p : FormSpace k N d} (h : IsChowPointOf i d Z p) (u v : Fin (N + 1) → k) :
    formLin (fun b : ULift.{u} (Bidegree N d) => b.down.1) (Sum.elim u v) ∈
        p.asHomogeneousIdeal ↔
      ∃ C ∈ (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z).support,
        IncidenceLocus C u v := by
  classical
  choose G n hG using fun C : Mori.ProperCurve (projToSpecCoeff k N) => exists_incidenceForm C
  set Wc := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z
  obtain ⟨hFdeg, hrel⟩ := h.2.2 G fun C _ => ⟨(hG C).1, (hG C).2.1⟩
  set F := ∏ C ∈ Wc.support, G C ^ (Wc C).toNat
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun C _ => pow_ne_zero _ (hG C).1.ne_zero
  obtain ⟨e, he⟩ : F.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun h0 => hF (MvPolynomial.support_eq_empty.mp h0))
  let c : ULift.{u} (Bidegree N d) → k := fun b => F.coeff b.down.1
  let b₀ : ULift.{u} (Bidegree N d) := ⟨⟨e, hFdeg e he⟩⟩
  have hc0 : c b₀ ≠ 0 := Finsupp.mem_support_iff.mp he
  rw [mem_iff_eval_of_relations c hc0 _ hrel (isHomogeneous_formLin _ _)]
  have : (fun b => c b / c b₀) = fun b => (c b₀)⁻¹ * c b := by
    funext b; rw [div_eq_inv_mul]
  rw [this, eval_mul_of_isHomogeneous _ _ (isHomogeneous_formLin _ _), mul_eq_zero,
    or_iff_right (pow_ne_zero _ (inv_ne_zero hc0)), eval_formLin]
  have hfe := formEval_eq_eval (k := k) F hFdeg u v
  simp only [formEval] at hfe
  rw [hfe, map_prod, Finset.prod_eq_zero_iff]
  refine exists_congr fun C => and_congr_right fun hC => ?_
  have hpos : (Wc C).toNat ≠ 0 := by
    have := Finsupp.mem_support_iff.mp hC
    have : 0 ≤ Wc C := pushforward_nonneg i _ h.1 C
    omega
  rw [map_pow, pow_eq_zero_iff hpos, (hG C).2.1]

/-- The push-forward of a 1-cycle along a closed immersion `i` is supported on the image of `i`. -/
private theorem point_mem_range_of_mem_support_pushforward
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i]
    (Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)) {C : Mori.ProperCurve (projToSpecCoeff k N)}
    (hC : C ∈ (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z).support) :
    C.point ∈ Set.range i := by
  classical
  rw [pushforward_eq_mapDomain] at hC
  obtain ⟨C₀, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hC)
  exact ⟨C₀.point, rfl⟩

/-- **Points of the support incidence are limits over any dense open.** For a morphism `φ` from
a scheme `S` of finite type to the Chow-form locus, a closed point `(s, x)` of the support
incidence `I ⊆ S ×ₖ X` lies in the closure `J` of the part of `I` over a dense open `S₀`. Else
choose hyperplanes `H_u, H_v` through `x` avoiding the closed fibre `J_s`, which lies on the curves
of `Z_s`. The root `(u, v)` of the Chow form of `φ s` moves to roots of the Chow forms of `φ s'`,
`s' ∈ S₀` near `s`, still avoiding `J`; but a root of the Chow form of `φ s'` gives a point of
`H_u ∩ H_v` on the support of `Z_{s'}`, which lies in `J`. -/
private theorem mem_closure_supportIncidence_of_dense
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i] (d : ℕ)
    (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS]
    (φ : S ⟶ FormSpace k N d) (hφ : φ ≫ ProjSpace.toSpec k _ = sS) (hφW : ∀ s, φ s ∈ W)
    (I : Set (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u})) (hI : IsClosed I)
    (hpin : ∀ p : (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}), IsClosed {p} →
        (p ∈ I ↔ pullback.snd sS (i ≫ projToSpecCoeff k N) p ∈
          ⋃ C ∈ (chowCycle i d (φ (pullback.fst sS (i ≫ projToSpecCoeff k N) p))).support,
            closure {C.point}))
    (S₀ : Set S) (hS₀ : IsOpen S₀) (hS₀d : Dense S₀)
    (p : (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u})) (hp : IsClosed {p})
    (hpI : p ∈ I) :
    p ∈ closure (I ∩ pullback.fst sS (i ≫ projToSpecCoeff k N) ⁻¹' S₀) := by
  classical
  haveI := finite_bidegree N d
  haveI := Fintype.ofFinite (ULift.{u} (Bidegree N d))
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  haveI := jacobsonSpace_proj k N
  let m : ULift.{u} (Bidegree N d) → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ := fun b => b.down.1
  haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (i ≫ projToSpecCoeff k N)
  haveI : JacobsonSpace (FormSpace k N d) :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k _)
  haveI : LocallyOfFiniteType (pullback.fst sS (i ≫ projToSpecCoeff k N) ≫ sS) := inferInstance
  haveI : JacobsonSpace (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst sS (i ≫ projToSpecCoeff k N) ≫ sS)
  haveI : LocallyOfFiniteType (φ ≫ Intersection.ProjSpace.toSpec k _) := hφ ▸ inferInstance
  haveI : LocallyOfFiniteType φ :=
    locallyOfFiniteType_of_comp φ (Intersection.ProjSpace.toSpec k _)
  by_contra hpJ
  set J := closure (I ∩ pullback.fst sS (i ≫ projToSpecCoeff k N) ⁻¹' S₀)
  have hJI : J ⊆ I := hI.closure_subset_iff.mpr Set.inter_subset_left
  set s := pullback.fst sS (i ≫ projToSpecCoeff k N) p
  set x := pullback.snd sS (i ≫ projToSpecCoeff k N) p
  have hs : IsClosed ({s} : Set S) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints (pullback.fst sS (i ≫ projToSpecCoeff k N)) hp
  have hx : IsClosed ({x} : Set X) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints (pullback.snd sS (i ≫ projToSpecCoeff k N)) hp
  have hix : IsClosed ({i x} : Set (AlgebraicGeometry.Proj (polyGrading k N))) := by
    rw [← Set.image_singleton]
    exact i.isClosedEmbedding.isClosedMap _ hx
  -- the fibre `J_s` of `J` over `s`, through the section `X ⟶ S ×ₖ X` at `s`
  obtain ⟨jS, hjS, hjSs, hjSf, hjSu⟩ := exists_section_of_isClosed sS (i ≫ projToSpecCoeff k N) hs
  haveI : LocallyOfFiniteType (jS ≫ pullback.snd sS (i ≫ projToSpecCoeff k N) ≫
      (i ≫ projToSpecCoeff k N)) := by
    rw [← Category.assoc, hjS, Category.id_comp]; infer_instance
  haveI : LocallyOfFiniteType jS := locallyOfFiniteType_of_comp jS
    (pullback.snd sS (i ≫ projToSpecCoeff k N) ≫ (i ≫ projToSpecCoeff k N))
  have hjx : jS x = p := (hjSu p rfl hx).symm
  have hJ : IsClosed J := isClosed_closure
  set Js := jS ⁻¹' J
  have hJs : IsClosed Js := hJ.preimage jS.continuous
  have hxJs : x ∉ Js := fun h => hpJ (by rwa [← hjx])
  set Z := chowCycle i d (φ s)
  have hJsupp : Js ⊆ ⋃ C ∈ Z.support, closure {C.point} := by
    have hcl : IsClosed (⋃ C ∈ Z.support, closure {C.point}) :=
      isClosed_biUnion_finset fun _ _ => isClosed_closure
    rw [← JacobsonSpace.closure_inter_closedPoints hJs]
    refine hcl.closure_subset_iff.mpr fun y ⟨hyJ, hyc⟩ => ?_
    have hjyc : IsClosed ({jS y} : Set _) :=
      Scheme.Hom.closePoints_subset_preimage_closedPoints jS hyc
    have := (hpin (jS y) hjyc).mp (hJI hyJ)
    rwa [hjSf, hjSs] at this
  -- its image `L` in `ℙᴺ_k`, and hyperplanes `H_u, H_v` through `x` avoiding it
  set Wc := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z
  set L := i '' Js
  have hL : IsClosed L := i.isClosedEmbedding.isClosedMap _ hJs
  have hLT : L ⊆ ⋃ C ∈ Wc.support, closure {C.point} := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_iUnion_support_pushforward_iff i Z y).mpr (hJsupp hy)
  have hixL : i x ∉ L := fun ⟨y, hy, hyx⟩ => hxJs (i.isClosedEmbedding.injective hyx ▸ hy)
  obtain ⟨a, j₀, haj, ha⟩ := exists_relations_of_isClosed (i x) hix
  obtain ⟨u, v, hua, hva, huv⟩ := exists_forall_not_and_of_isClosed Wc.support hL hLT a haj ha
    hixL
  -- `(u, v)` is a root of the Chow form at `s`
  have hφs : IsClosed ({φ s} : Set (FormSpace k N d)) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints φ hs
  have hch : IsChowPointOf i d Z (φ s) := isChowPointOf_chowCycle ((hW _ hφs).mp (hφW s))
  have hroot : formLin m (Sum.elim u v) ∈ (φ s).asHomogeneousIdeal := by
    rw [formLin_mem_iff_exists_incidenceLocus i hch]
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp
      ((mem_iUnion_support_pushforward_iff i Z x).mpr ((hpin p hp).mp hpI))
    exact ⟨C, hC, i x, hxC, (linearForm_mem_iff a haj (i x) ha u).mpr hua,
      (linearForm_mem_iff a haj (i x) ha v).mpr hva⟩
  -- the closed set `T ⊆ S ×ₖ ℙᴺ_k`, the image of `J`
  let ι₂ := pullback.map sS (i ≫ projToSpecCoeff k N) sS (projToSpecCoeff k N) (𝟙 S) i (𝟙 _)
    (by simp) (by simp)
  haveI : IsClosedImmersion ι₂ := by
    unfold ι₂
    infer_instance
  have hι₂f : ∀ z, pullback.fst sS (projToSpecCoeff k N) (ι₂ z) =
      pullback.fst sS (i ≫ projToSpecCoeff k N) z := fun z => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Category.comp_id]
  have hι₂s : ∀ z, pullback.snd sS (projToSpecCoeff k N) (ι₂ z) =
      i (pullback.snd sS (i ≫ projToSpecCoeff k N) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
  set T := ι₂ '' J
  have hT : IsClosed T := ι₂.isClosedEmbedding.isClosedMap _ hJ
  have hm : Function.Injective m := fun b b' h => ULift.ext (Subtype.ext h)
  have hD : ∀ b, ∑ j, m b j = d + d := fun b => by
    rw [Fintype.sum_sum_type, b.down.2.1, b.down.2.2]
  have havoid : ∀ z ∈ T, IsClosed ({z} : Set _) → pullback.fst sS (projToSpecCoeff k N) z = s →
      ¬ (hypForm (Sum.elim u v ∘ Sum.inl) ∈
          (pullback.snd sS (projToSpecCoeff k N) z).asHomogeneousIdeal ∧
        hypForm (Sum.elim u v ∘ Sum.inr) ∈
          (pullback.snd sS (projToSpecCoeff k N) z).asHomogeneousIdeal) := by
    rintro _ ⟨z, hzJ, rfl⟩ hzc hzf ⟨h1, h2⟩
    have hz : IsClosed ({z} : Set _) := by
      rw [ι₂.isClosedEmbedding.isClosed_iff_image_isClosed, Set.image_singleton]
      exact hzc
    rw [hι₂f] at hzf
    have hzsc : IsClosed ({pullback.snd sS (i ≫ projToSpecCoeff k N) z} : Set X) :=
      Scheme.Hom.closePoints_subset_preimage_closedPoints _ hz
    have hzj := hjSu z hzf hzsc
    have hmem : pullback.snd sS (i ≫ projToSpecCoeff k N) z ∈ Js := by
      show jS _ ∈ J
      rw [← hzj]
      exact hzJ
    rw [hι₂s] at h1 h2
    exact huv _ ⟨_, hmem, rfl⟩ ⟨h1, h2⟩
  obtain ⟨O, hO, hsO, hOgood⟩ := exists_isOpen_forall_exists_formLin_mem m hm hD sS φ hφ T hT hs
    (Sum.elim u v) hroot havoid
  -- a closed point `s'` of `O ∩ S₀`, and the root there
  obtain ⟨s', ⟨-, hs'O, hs'S₀⟩, hs'c⟩ := exists_isClosed_singleton_of_nonempty isClosed_univ
    (hO.inter hS₀) (by
      obtain ⟨y, hy⟩ := hS₀d.inter_open_nonempty O hO ⟨s, hsO⟩
      exact ⟨y, trivial, hy.1, hy.2⟩)
  obtain ⟨x', hx'root, hx'avoid⟩ := hOgood s' hs'O hs'c
  have hφs' : IsClosed ({φ s'} : Set (FormSpace k N d)) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints φ hs'c
  set Z' := chowCycle i d (φ s')
  have hch' : IsChowPointOf i d Z' (φ s') := isChowPointOf_chowCycle ((hW _ hφs').mp (hφW s'))
  rw [← Sum.elim_comp_inl_inr x', formLin_mem_iff_exists_incidenceLocus i hch'] at hx'root
  obtain ⟨C, hC, q, hqC, hqu, hqv⟩ := hx'root
  -- a closed point `y` of `C ∩ H_u ∩ H_v`
  have hZq : IsClosed (closure {q} ∩ ProjectiveSpectrum.zeroLocus (polyGrading k N)
      {hypForm (x' ∘ Sum.inl), hypForm (x' ∘ Sum.inr)}) :=
    isClosed_closure.inter (ProjectiveSpectrum.isClosed_zeroLocus _ _)
  obtain ⟨y, ⟨⟨hyq, hyH⟩, -⟩, hyc⟩ := exists_isClosed_singleton_of_nonempty hZq isOpen_univ
    ⟨q, ⟨subset_closure rfl, by
      intro g hg
      rcases hg with rfl | hg
      · exact hqu
      · rw [Set.mem_singleton_iff] at hg; subst hg; exact hqv⟩, trivial⟩
  have hyC : y ∈ closure {C.point} := closure_minimal (Set.singleton_subset_iff.mpr hqC)
    isClosed_closure hyq
  obtain ⟨x'', rfl⟩ : y ∈ Set.range i :=
    (i.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr (point_mem_range_of_mem_support_pushforward i Z' hC))) hyC
  have hx''c : IsClosed ({x''} : Set X) := by
    rw [i.isClosedEmbedding.isClosed_iff_image_isClosed, Set.image_singleton]
    exact hyc
  have hx''Z : x'' ∈ ⋃ C ∈ Z'.support, closure {C.point} :=
    (mem_iUnion_support_pushforward_iff i Z' x'').mp (Set.mem_biUnion hC hyC)
  -- the point `(s', x'')` of `I` over `S₀`, whose image lies in `T`
  obtain ⟨jS', hjS', hjS's, hjS'f, -⟩ :=
    exists_section_of_isClosed sS (i ≫ projToSpecCoeff k N) hs'c
  haveI : LocallyOfFiniteType (jS' ≫ pullback.snd sS (i ≫ projToSpecCoeff k N) ≫
      (i ≫ projToSpecCoeff k N)) := by
    rw [← Category.assoc, hjS', Category.id_comp]
    infer_instance
  haveI : LocallyOfFiniteType jS' := locallyOfFiniteType_of_comp jS'
    (pullback.snd sS (i ≫ projToSpecCoeff k N) ≫ (i ≫ projToSpecCoeff k N))
  have hp''c : IsClosed ({jS' x''} : Set _) :=
    Scheme.Hom.closePoints_subset_preimage_closedPoints jS' hx''c
  have hp''I : jS' x'' ∈ I := (hpin _ hp''c).mpr (by rwa [hjS'f, hjS's])
  have hp''J : jS' x'' ∈ J :=
    subset_closure ⟨hp''I, by rwa [Set.mem_preimage, hjS'f]⟩
  have hzc : IsClosed ({ι₂ (jS' x'')} : Set _) := by
    rw [← Set.image_singleton]
    exact ι₂.isClosedEmbedding.isClosedMap _ hp''c
  refine hx'avoid (ι₂ (jS' x'')) ⟨_, hp''J, rfl⟩ hzc (by rw [hι₂f, hjS'f]) ?_
  rw [hι₂s, hjS's]
  exact ⟨hyH (Set.mem_insert _ _), hyH (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

/-- In a Noetherian quasi-sober space, the generic point of a maximal irreducible subset `Z` of a
closed set `I` does not lie in the closure of `I \ Z`. -/
private theorem genericPoint_notMem_closure_diff {P : Type*} [TopologicalSpace P]
    [TopologicalSpace.NoetherianSpace P] [QuasiSober P] {I Z : Set P} (hI : IsClosed I)
    (hZ : Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Z) {ζ : P} (hζ : IsGenericPoint ζ Z) :
    ζ ∉ closure (I \ Z) := by
  intro hmem
  have hZc : IsClosed Z := by
    rw [← hζ.def]; exact isClosed_closure
  obtain ⟨T, hTf, hTc, hTi, hT⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure (s := I \ Z))
  have hsub : I \ Z ⊆ ⋃₀ {t ∈ T | (t ∩ (I \ Z)).Nonempty} := by
    intro y hy
    have : y ∈ ⋃₀ T := hT ▸ subset_closure hy
    obtain ⟨t, ht, hyt⟩ := this
    exact ⟨t, ⟨ht, y, hyt, hy⟩, hyt⟩
  have hclosed : IsClosed (⋃₀ {t ∈ T | (t ∩ (I \ Z)).Nonempty}) :=
    (hTf.subset fun t ht => ht.1).isClosed_sUnion fun t ht => hTc t ht.1
  obtain ⟨t, ⟨htT, y, hyt, hy⟩, hζt⟩ := hclosed.closure_subset_iff.mpr hsub hmem
  have hZt : Z ⊆ t := by
    rw [← hζ.def]; exact (hTc t htT).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hζt)
  have htI : t ⊆ I := fun z hz => by
    have : z ∈ closure (I \ Z) := hT ▸ Set.mem_sUnion_of_mem hz htT
    exact (hI.closure_subset_iff.mpr Set.diff_subset) this
  have htZ : t ⊆ Z := hZ.2 ⟨hTi t htT, htI⟩ hZt
  exact hy.2 (htZ hyt)

/-- **No component of the support incidence is vertical.** For a morphism `φ` from a normal
variety `S` to the Chow-form locus, every irreducible component of the (closed) support incidence
`I ⊆ S ×ₖ X` dominates `S`: a closed point of a vertical component off the other components would
not be a limit of points of `I` over the complement of the component's image. -/
private theorem dense_image_fst_of_maximal_supportIncidence
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)) (hS : Mori.IsNormalVariety k sS)
    (φ : S ⟶ FormSpace k N d) (hφ : φ ≫ ProjSpace.toSpec k _ = sS) (hφW : ∀ s, φ s ∈ W)
    (I : Set (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u})) (hI : IsClosed I)
    (hpin : ∀ p : (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}), IsClosed {p} →
        (p ∈ I ↔ pullback.snd sS (i ≫ projToSpecCoeff k N) p ∈
          ⋃ C ∈ (chowCycle i d (φ (pullback.fst sS (i ≫ projToSpecCoeff k N) p))).support,
            closure {C.point})) :
    ∀ Z, Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Z →
      Dense (pullback.fst sS (i ≫ projToSpecCoeff k N) '' Z) := by
  intro Z hZ
  haveI := hS.1
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  haveI : LocallyOfFiniteType (pullback.fst sS (i ≫ projToSpecCoeff k N) ≫ sS) := inferInstance
  haveI : QuasiCompact (pullback.fst sS (i ≫ projToSpecCoeff k N) ≫ sS) := inferInstance
  haveI : IsLocallyNoetherian (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst sS (i ≫ projToSpecCoeff k N) ≫ sS)
  haveI : CompactSpace (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sS (i ≫ projToSpecCoeff k N) ≫ sS)
  haveI : JacobsonSpace (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst sS (i ≫ projToSpecCoeff k N) ≫ sS)
  haveI : IsNoetherian (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}) := {}
  by_contra hnd
  -- the generic point of `Z` is off the other components
  have hZc : IsClosed Z := by
    have := hZ.2 ⟨hZ.1.1.closure, hI.closure_subset_iff.mpr hZ.1.2⟩ subset_closure
    exact closure_subset_iff_isClosed.mp this
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hZ.1.1 hZc
  have hζ' := genericPoint_notMem_closure_diff hI hZ hζ
  -- a closed point of `Z` off the other components
  obtain ⟨q, ⟨hqZ, hqc⟩, hq⟩ : ((Z ∩ closedPoints (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u})) ∩
      (closure (I \ Z))ᶜ).Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    have : Z ∩ closedPoints (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}) ⊆ closure (I \ Z) :=
        fun y hy => by
      by_contra hy'
      exact (Set.eq_empty_iff_forall_notMem.mp hem) y ⟨hy, hy'⟩
    have h2 := isClosed_closure.closure_subset_iff.mpr this
    rw [JacobsonSpace.closure_inter_closedPoints hZc] at h2
    exact hζ' (h2 hζ.mem)
  -- the complement of the image of `Z` is a dense open
  set S₀ := (closure (pullback.fst sS (i ≫ projToSpecCoeff k N) '' Z))ᶜ
  have hS₀ : IsOpen S₀ := isClosed_closure.isOpen_compl
  have hS₀ne : S₀.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    exact hnd (dense_iff_closure_eq.mpr h)
  have hS₀d : Dense S₀ := hS₀.dense hS₀ne
  have hmem := mem_closure_supportIncidence_of_dense i d W hW S sS φ hφ hφW I hI hpin S₀
    hS₀ hS₀d q hqc (hZ.1.2 hqZ)
  have hsub : I ∩ pullback.fst sS (i ≫ projToSpecCoeff k N) ⁻¹' S₀ ⊆ I \ Z := fun y ⟨hyI, hyS⟩ =>
    ⟨hyI, fun hyZ => hyS (subset_closure ⟨y, hyZ, rfl⟩)⟩
  exact hq (closure_mono hsub hmem)

/-- **The support incidence.** For a morphism `φ` from a normal variety to the space of forms,
landing in the Chow-form locus `W`, the incidence of the supports of the cycles `chowCycle (φ s)`
is closed and each of its irreducible components dominates `S`. -/
private theorem exists_supportIncidence (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)) (hS : Mori.IsNormalVariety k sS)
    (φ : S ⟶ FormSpace k N d) (hφ : φ ≫ ProjSpace.toSpec k _ = sS) (hφW : ∀ s, φ s ∈ W) :
    ∃ I : Set (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}), IsClosed I ∧
      (∀ p : (pullback sS (i ≫ projToSpecCoeff k N) : Scheme.{u}), IsClosed {p} →
        (p ∈ I ↔ pullback.snd sS (i ≫ projToSpecCoeff k N) p ∈
          ⋃ C ∈ (chowCycle i d (φ (pullback.fst sS (i ≫ projToSpecCoeff k N) p))).support,
            closure {C.point})) ∧
      ∀ Z, Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Z →
        Dense (pullback.fst sS (i ≫ projToSpecCoeff k N) '' Z) := by
  haveI := hS.1
  obtain ⟨I, hI, hpin⟩ := exists_isClosed_supportIncidence i d W hW S sS φ hφ hφW
  exact ⟨I, hI, hpin,
    dense_image_fst_of_maximal_supportIncidence i d hd W hW S sS hS φ hφ hφW I hI hpin⟩

/-- A nonempty scheme all of whose irreducible components are curves is one-dimensional. -/
private theorem topologicalKrullDim_eq_one_of_forall_irreducibleComponents {Y : Scheme.{u}}
    [Nonempty Y] (hpure : ∀ x : Y, closure {x} ∈ irreducibleComponents Y →
      topologicalKrullDim (Mori.curveSubschemeAt x) = 1) :
    topologicalKrullDim Y = 1 := by
  have key : ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim Z = 1 := by
    intro Z hZ
    obtain ⟨x, hx⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
    have hrange : Set.range (Mori.curveSubschemeAtι x) = Z := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hx
    rw [← hpure x (by rw [hx.def]; exact hZ), ← hrange]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Mori.curveSubschemeAtι x).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
    isIrreducible_singleton
  refine le_antisymm (MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents
    fun Z hZ => (key Z hZ).le) ?_
  rw [← key Z hZ]
  exact topologicalKrullDim_subspace_le Y Z

/-- Push-forward of the fibre cycle along the closed immersion `X ⟶ ℙᴺ_k`. -/
public theorem pushforward_fiberCycle (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] {S 𝒞' : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (π : 𝒞' ⟶ S)
    (q : 𝒞' ⟶ X) (s : S) :
    Mori.OneCycle.pushforward ℤ (i ≫ projToSpecCoeff k N) (projToSpecCoeff k N) i
        (∑ᶠ C : {C : Mori.ProperCurve (π.fiberι s ≫ π ≫ sS) //
              closure {C.point} ∈ irreducibleComponents (π.fiber s)},
          ((Module.length ((π.fiber s).presheaf.stalk C.1.point)
              ((π.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
            Mori.cyclePushforwardOfPoint ℤ (i ≫ projToSpecCoeff k N) (π.fiberι s ≫ q) C.1.point) =
      ∑ᶠ C : {C : Mori.ProperCurve (π.fiberι s ≫ π ≫ sS) //
              closure {C.point} ∈ irreducibleComponents (π.fiber s)},
        ((Module.length ((π.fiber s).presheaf.stalk C.1.point)
            ((π.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
          Mori.cyclePushforwardOfPoint ℤ (projToSpecCoeff k N) (π.fiberι s ≫ q ≫ i) C.1.point := by
  simpa only [Category.assoc] using
    pushforward_finsum_smul_cyclePushforwardOfPoint (π.fiberι s ≫ q) i (projToSpecCoeff k N)
      (fun C : {C : Mori.ProperCurve (π.fiberι s ≫ π ≫ sS) //
          closure {C.point} ∈ irreducibleComponents (π.fiber s)} =>
        ((Module.length ((π.fiber s).presheaf.stalk C.1.point)
          ((π.fiber s).presheaf.stalk C.1.point)).toNat : ℤ)) (fun C => C.1.point)

/-- **The family clause.** A proper flat family of pure curves of degree `d` over a normal variety
has a classifying morphism to the space of forms, landing in the Chow-form locus, whose value at
each closed point is the Chow point of the fibre cycle. -/
private theorem exists_chowPoint_family (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d)
    (S 𝒞' : Scheme.{u}) (sS : S ⟶ Spec (.of k)) (hS : Mori.IsNormalVariety k sS)
    (π : 𝒞' ⟶ S) (q : 𝒞' ⟶ X) (hπq : π ≫ sS = q ≫ (i ≫ projToSpecCoeff k N))
    (himm : IsClosedImmersion (pullback.lift π q hπq)) (hprop : IsProper π) (hflat : Flat π)
    (hpure : ∀ s : S, IsClosed ({s} : Set S) → ∀ x : π.fiber s,
      closure {x} ∈ irreducibleComponents (π.fiber s) →
        topologicalKrullDim (Mori.curveSubschemeAt x) = 1)
    (Z : S → Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N))
    (hZ : ∀ s : S, Z s = ∑ᶠ C : {C : Mori.ProperCurve (π.fiberι s ≫ π ≫ sS) //
              closure {C.point} ∈ irreducibleComponents (π.fiber s)},
        ((Module.length ((π.fiber s).presheaf.stalk C.1.point)
            ((π.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
          Mori.cyclePushforwardOfPoint ℤ (i ≫ projToSpecCoeff k N) (π.fiberι s ≫ q) C.1.point)
    (hdeg : ∀ s : S, IsClosed ({s} : Set S) → cycleDegree i (Z s) = d) :
    ∃ φ : S ⟶ FormSpace k N d, φ ≫ ProjSpace.toSpec k _ = sS ∧
      ∀ s : S, IsClosed ({s} : Set S) → IsClosed ({φ s} : Set _) ∧ IsChowPointOf i d (Z s) (φ s) := by
  haveI := himm
  haveI := hprop
  haveI := hflat
  haveI := hS.1
  have hne : ∀ s : S, IsClosed ({s} : Set S) → Nonempty (π.fiber s) := by
    intro s hs
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : Z s = 0 := by
      rw [hZ s]
      haveI : IsEmpty {C : Mori.ProperCurve (π.fiberι s ≫ π ≫ sS) //
          closure {C.point} ∈ irreducibleComponents (π.fiber s)} :=
        ⟨fun C => h.elim C.1.point⟩
      exact finsum_of_isEmpty _
    have := hdeg s hs
    rw [h0, cycleDegree, map_zero, map_zero] at this
    exact hd.ne (by exact_mod_cast this)
  obtain ⟨φ, hφ, -⟩ := MMP.Chow.exists_chowFormMorphism sS (i ≫ projToSpecCoeff k N) hS
    (isProjectiveMorphism_comp_projToSpecCoeff k i) i
    (MMP.isProjectiveMorphism_of_isClosedImmersion i) rfl π q hπq
    (fun s hs => haveI := hne s hs
      topologicalKrullDim_eq_one_of_forall_irreducibleComponents (hpure s hs)) d hd
    (fun s hs => by
      beta_reduce
      rw [← pushforward_fiberCycle i sS π q s, ← hZ s]
      exact hdeg s hs)
  obtain ⟨hφS, hφC⟩ := (hφ φ).mpr rfl
  haveI : LocallyOfFiniteType (φ ≫ Intersection.ProjSpace.toSpec k _) := hφS ▸ inferInstance
  haveI := finite_bidegree N d
  haveI : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ (Intersection.ProjSpace.toSpec k _)
  haveI : JacobsonSpace (FormSpace k N d) :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k _)
  refine ⟨φ, hφS, fun s hs => ⟨Scheme.Hom.closePoints_subset_preimage_closedPoints φ hs, ?_,
    hdeg s hs, ?_⟩⟩
  · rw [hZ s]
    refine finsum_nonneg fun C => smul_nonneg (Int.natCast_nonneg _) ?_
    unfold Mori.cyclePushforwardOfPoint
    split_ifs
    · exact Finsupp.single_nonneg.mpr (Int.natCast_nonneg _)
    · exact le_rfl
  · intro G hG
    have := hφC s hs G
    beta_reduce at this
    rw [← pushforward_fiberCycle i sS π q s, ← hZ s] at this
    exact this hG

/-! ### The Chow-form locus is closed -/

/-- The form `∑_b c_b x^{m_b}` with coefficient vector `c` and monomials `m`. -/
private noncomputable def formPoly {ι σ : Type*} [Fintype ι] (m : ι → σ →₀ ℕ) (c : ι → k) :
    MvPolynomial σ k :=
  ∑ b, MvPolynomial.C (c b) * MvPolynomial.monomial (m b) 1

private theorem eval_formPoly {ι σ : Type*} [Fintype ι] [Fintype σ] (m : ι → σ →₀ ℕ)
    (c : ι → k) (x : σ → k) :
    MvPolynomial.eval x (formPoly m c) = MvPolynomial.eval c (formLin m x) := by
  rw [eval_formLin, formPoly, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_monomial, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _)]

private theorem coeff_formPoly {ι σ : Type*} [Fintype ι] {m : ι → σ →₀ ℕ}
    (hm : Function.Injective m) (c : ι → k) (b : ι) : (formPoly m c).coeff (m b) = c b := by
  classical
  rw [formPoly, MvPolynomial.coeff_sum, Finset.sum_eq_single b]
  · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, if_pos rfl, mul_one]
  · intro b' _ hb'
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, if_neg (fun h => hb' (hm h)),
      mul_zero]
  · simp

private theorem mem_range_of_mem_support_formPoly {ι σ : Type*} [Fintype ι] (m : ι → σ →₀ ℕ)
    (c : ι → k) {e : σ →₀ ℕ} (he : e ∈ (formPoly m c).support) : e ∈ Set.range m := by
  classical
  by_contra h
  apply MvPolynomial.mem_support_iff.mp he
  rw [formPoly, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, if_neg (fun h' => h ⟨b, h'⟩),
    mul_zero]

/-- A point `p` satisfying the relations of `[c]`, normalized by `c_l = 1`, contains a form `g`
exactly when `g(c) = 0`. -/
private theorem mem_iff_eval_of_relations_one {ι : Type*} [Fintype ι] (c : ι → k) {l : ι}
    (hcl : c l = 1) (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ι k))
    (hp : ∀ b b', c b' • (MvPolynomial.X b : MvPolynomial ι k) - c b • MvPolynomial.X b' ∈
      p.asHomogeneousIdeal)
    {g : MvPolynomial ι k} {n : ℕ} (hg : g.IsHomogeneous n) :
    g ∈ p.asHomogeneousIdeal ↔ MvPolynomial.eval c g = 0 := by
  rw [mem_iff_eval_of_relations c (b₀ := l) (by rw [hcl]; exact one_ne_zero) p hp hg]
  simp [hcl]

/-- The vertex locus at a pair of points `([c], [a])` with normalized coordinates. -/
private theorem mem_vertexLocus_iff_formLin {ι : Type u} [Fintype ι]
    (m : ι → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ)
    (z : (pullback (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) : Scheme.{u}))
    (c : ι → k) {l : ι} (hcl : c l = 1)
    (hc : ∀ b b', c b' • (MvPolynomial.X b : MvPolynomial ι k) - c b • MvPolynomial.X b' ∈
      (pullback.fst (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) z).asHomogeneousIdeal)
    (a : Fin (N + 1) → k) {j : Fin (N + 1)} (haj : a j = 1)
    (ha : ∀ b b', a b' • (MvPolynomial.X b : MvPolynomial (Fin (N + 1)) k) - a b • MvPolynomial.X b'
      ∈ (pullback.snd (Intersection.ProjSpace.toSpec k ι) (projToSpecCoeff k N) z).asHomogeneousIdeal) :
    z ∈ vertexLocus (k := k) m ↔ ∀ v v' : Fin (N + 1) → k, v ⬝ᵥ a = 0 → v' ⬝ᵥ a = 0 →
      MvPolynomial.eval c (formLin m (Sum.elim v v')) = 0 := by
  rw [mem_vertexLocus_iff m z c a (fun h => by simpa [hcl] using congrFun h l)
    (fun h => by simpa [haj] using congrFun h j)
    (fun n g hg => mem_iff_eval_of_relations_one c hcl _ hc hg)
    (fun n g hg => mem_iff_eval_of_relations_one a haj _ ha hg)]
  simp only [formEval, eval_formLin]

/-- A point `p` of `ℙᴺ_k` on two hyperplanes `H_u, H_v` specializes to a closed point on both. -/
private theorem exists_isClosed_mem_closure_hypForm (p : AlgebraicGeometry.Proj (polyGrading k N))
    {u v : Fin (N + 1) → k} (hu : hypForm u ∈ p.asHomogeneousIdeal)
    (hv : hypForm v ∈ p.asHomogeneousIdeal) :
    ∃ y ∈ closure ({p} : Set _), IsClosed ({y} : Set _) ∧ hypForm u ∈ y.asHomogeneousIdeal ∧
      hypForm v ∈ y.asHomogeneousIdeal := by
  haveI := jacobsonSpace_proj k N
  obtain ⟨y, ⟨⟨hyp, hyH⟩, -⟩, hyc⟩ := exists_isClosed_singleton_of_nonempty
    ((isClosed_closure (s := ({p} : Set (AlgebraicGeometry.Proj (polyGrading k N))))).inter
      (ProjectiveSpectrum.isClosed_zeroLocus (polyGrading k N) {hypForm u, hypForm v}))
    isOpen_univ ⟨p, ⟨subset_closure rfl, by
      intro g hg
      rcases hg with rfl | hg
      · exact hu
      · rw [Set.mem_singleton_iff] at hg; subst hg; exact hv⟩, trivial⟩
  exact ⟨y, hyp, hyc, hyH (Set.mem_insert _ _),
    hyH (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

public theorem topologicalKrullDim_eq_of_range_eq {A B Y : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace Y] {f : A → Y} {g : B → Y}
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) (h : Set.range f = Set.range g) :
    topologicalKrullDim A = topologicalKrullDim B := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ hf.toHomeomorph.isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ hg.toHomeomorph.isHomeomorph, h]

/-- In `ℙᴺ_k`, a point `η` that is not closed and whose closure contains only finitely many proper
curves is itself the generic point of a proper curve: any two closed points of `{η}⁻` lie on a
curve inside it, so finitely many curves cover the closed points of `{η}⁻`, and one of them is all
of it. -/
private theorem isProperCurve_of_finite {η : AlgebraicGeometry.Proj (polyGrading k N)}
    (hη : ¬ IsClosed ({η} : Set _))
    (hfin : {C : Mori.ProperCurve (projToSpecCoeff k N) | C.point ∈ closure {η}}.Finite) :
    Mori.IsProperCurve (projToSpecCoeff k N) η := by
  classical
  haveI := jacobsonSpace_proj k N
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  let J := Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({η} : Set (AlgebraicGeometry.Proj (polyGrading k N))))
  have hrange : Set.range J.subschemeι = closure {η} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hemb := J.subschemeι.isClosedEmbedding
  haveI : IsReduced J.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  haveI : IrreducibleSpace J.subscheme := by
    have h1 : IsIrreducible (Set.univ : Set (Set.range J.subschemeι)) :=
      (Subtype.irreducibleSpace (hrange ▸ isIrreducible_singleton.closure :
        IsIrreducible (Set.range J.subschemeι))).isIrreducible_univ
    have h2 := h1.image hemb.isEmbedding.toHomeomorph.symm
      hemb.isEmbedding.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ, Homeomorph.range_coe] at h2
    exact (irreducibleSpace_def _).mpr h2
  haveI : IsIntegral J.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : Mori.IsVariety k (J.subschemeι ≫ projToSpecCoeff k N) := {}
  -- a closed point `y₀ ≠ η` of `{η}⁻`
  obtain ⟨y₀, ⟨hy₀, -⟩, hy₀c⟩ := exists_isClosed_singleton_of_nonempty
    (isClosed_closure (s := ({η} : Set (AlgebraicGeometry.Proj (polyGrading k N))))) isOpen_univ
    ⟨η, subset_closure rfl, trivial⟩
  obtain ⟨y₀', rfl⟩ : y₀ ∈ Set.range J.subschemeι := hrange ▸ hy₀
  obtain ⟨η', hη'⟩ : η ∈ Set.range J.subschemeι := hrange ▸ subset_closure rfl
  have hclosed : ∀ y : J.subscheme, IsClosed ({J.subschemeι y} : Set _) →
      IsClosed ({y} : Set J.subscheme) := fun y hy =>
    hemb.isClosed_iff_image_isClosed.mpr (by rw [Set.image_singleton]; exact hy)
  have hdim : 0 < topologicalKrullDim J.subscheme := by
    have hsp : η' ⤳ y₀' := by
      rw [← hemb.isInducing.specializes_iff, hη']
      exact specializes_iff_mem_closure.mpr hy₀
    have hne : η' ≠ y₀' := by
      rintro rfl
      exact hη (hη' ▸ hy₀c)
    exact lt_of_lt_of_le (by exact_mod_cast zero_lt_one)
      (one_le_topologicalKrullDim_of_specializes hsp hne)
  -- every closed point of `{η}⁻` lies on one of the finitely many curves
  have hcover : ∀ y : J.subscheme, IsClosed ({y} : Set J.subscheme) →
      ∃ C ∈ hfin.toFinset, J.subschemeι y ∈ closure {C.point} := by
    intro y hy
    obtain ⟨C, iC, hiC, hCc, -, ⟨e, he⟩, -⟩ :=
      MMP.exists_isClosedImmersion_isCurve_and_isProper_of_isClosed_singleton
        (J.subschemeι ≫ projToSpecCoeff k N) hdim (hclosed y₀' hy₀c) hy
    haveI := hiC
    haveI : IsIntegral C := hCc.toIsVariety.toIsIntegral
    set g := iC ≫ J.subschemeι
    have hgemb := g.isClosedEmbedding
    have hξ : closure ({g (genericPoint C)} : Set _) = Set.range g := by
      rw [← Set.image_singleton, hgemb.closure_image_eq, genericPoint_closure, Set.image_univ]
    have hcurve : Mori.IsProperCurve (projToSpecCoeff k N) (g (genericPoint C)) := by
      refine Mori.isProperCurve_of_isProper _ ?_
      rw [topologicalKrullDim_eq_of_range_eq
        (Mori.curveSubschemeAtι (g (genericPoint C))).isClosedEmbedding.isEmbedding
        hgemb.isEmbedding (by
          rw [Scheme.IdealSheafData.range_subschemeι,
            Scheme.IdealSheafData.coe_support_vanishingIdeal]
          exact hξ)]
      exact IsCurve.topologicalKrullDim_eq_one (k := k)
        (f := iC ≫ J.subschemeι ≫ projToSpecCoeff k N)
    refine ⟨⟨_, hcurve⟩, hfin.mem_toFinset.mpr ?_, ?_⟩
    · rw [← hrange]
      exact ⟨iC (genericPoint C), rfl⟩
    · change J.subschemeι y ∈ closure {g (genericPoint C)}
      rw [hξ, ← he]
      exact ⟨e, rfl⟩
  have hsub : closure ({η} : Set _) ⊆ ⋃₀ (hfin.toFinset.image fun C => closure {C.point} :
      Finset (Set (AlgebraicGeometry.Proj (polyGrading k N)))) := by
    refine subset_trans (JacobsonSpace.closure_inter_closedPoints isClosed_closure).symm.subset ?_
    refine ((Finset.finite_toSet _).isClosed_sUnion fun t ht => ?_).closure_subset_iff.mpr ?_
    · obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp ht
      exact isClosed_closure
    · rintro y ⟨hy, hyc⟩
      obtain ⟨y', rfl⟩ : y ∈ Set.range J.subschemeι := hrange ▸ hy
      obtain ⟨C, hC, h⟩ := hcover y' (hclosed y' hyc)
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hC), h⟩
  obtain ⟨t, ht, hηt⟩ := (isIrreducible_iff_sUnion_isClosed.mp isIrreducible_singleton.closure) _
    (fun t ht => by
      obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp ht
      exact isClosed_closure) hsub
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp ht
  have h1 : C.point ⤳ η := specializes_iff_mem_closure.mpr (hηt (subset_closure rfl))
  have h2 : η ⤳ C.point := specializes_iff_mem_closure.mpr (hfin.mem_toFinset.mp hC)
  rw [← (h1.antisymm h2).eq]
  exact C.isProperCurve

/-- A linear form `∑ᵢ aᵢ x_{e(i)}` with some `aⱼ ≠ 0` is nonzero, of total degree at most one. -/
private theorem linearForm_ne_zero_and_totalDegree_le {σ τ : Type*} [Fintype σ] {e : σ → τ}
    (he : Function.Injective e) (a : σ → k) {j : σ} (ha : a j ≠ 0) :
    (∑ i, MvPolynomial.C (a i) * MvPolynomial.X (e i) : MvPolynomial τ k) ≠ 0 ∧
      (∑ i, MvPolynomial.C (a i) * MvPolynomial.X (e i) : MvPolynomial τ k).totalDegree ≤ 1 := by
  classical
  refine ⟨fun h0 => ha ?_, ?_⟩
  · have := congrArg (fun p : MvPolynomial _ _ => p.coeff (Finsupp.single (e j) 1)) h0
    simpa [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
      Finsupp.single_left_inj one_ne_zero, he.eq_iff] using this
  · refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- An irreducible divisor of a nonzero polynomial of total degree at most one is associated to
it. -/
private theorem associated_of_dvd_of_totalDegree_le_one {σ : Type*} {P ℓ : MvPolynomial σ k}
    (hP : Irreducible P) (hℓ : ℓ ≠ 0) (hdeg : ℓ.totalDegree ≤ 1) (h : P ∣ ℓ) :
    Associated P ℓ := by
  obtain ⟨Q, rfl⟩ := h
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hℓ
  rw [MvPolynomial.totalDegree_mul_of_isDomain hP.ne_zero hQ] at hdeg
  have hPdeg : P.totalDegree ≠ 0 := by
    intro h0
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
    apply hP.not_isUnit
    have hc : P.coeff 0 ≠ 0 := by
      intro hc; apply hP.ne_zero; rw [h0, hc, map_zero]
    rw [h0]
    exact (IsUnit.mk0 _ hc).map MvPolynomial.C
  have hQdeg : Q.totalDegree = 0 := by omega
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hQdeg
  have hc : Q.coeff 0 ≠ 0 := by intro hc; apply hQ; rw [hQdeg, hc, map_zero]
  have hu : IsUnit Q := by rw [hQdeg]; exact (IsUnit.mk0 _ hc).map MvPolynomial.C
  exact associated_mul_unit_right P Q hu

/-- Linear forms in the two different sets of variables `u` and `v` are not associated. -/
private theorem not_associated_linearForm_inl_inr {a a' : Fin (N + 1) → k} {j : Fin (N + 1)}
    (ha : a j ≠ 0) :
    ¬ Associated (∑ i, MvPolynomial.C (a i) * MvPolynomial.X (Sum.inl i) :
        MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
      (∑ i, MvPolynomial.C (a' i) * MvPolynomial.X (Sum.inr i)) := by
  classical
  rintro ⟨w, hw⟩
  obtain ⟨r, hr, hwr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp w.isUnit
  have := congrArg (fun p : MvPolynomial _ _ => p.coeff (Finsupp.single (Sum.inl j) 1)) hw
  rw [hwr, mul_comm, MvPolynomial.coeff_C_mul] at this
  simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
    Finsupp.single_left_inj one_ne_zero, ha, hr.ne_zero] at this

/-- **A form whose zeros all come from a closed subset of `X` is a Chow form.** Let
`F = ∑_b c_b x^b` be a `(d, d)`-form and `L ⊆ X ⊆ ℙᴺ_k` closed. Suppose `F(u, v) = 0` whenever
`H_u ∩ H_v` contains a closed point of `L`, and conversely `H_u ∩ H_v` contains a closed point of
`L` for every zero `(u, v)` of `F`. Then `[F]` is the Chow point of an effective cycle of degree
`d` on `X`. Every curve `C ⊆ L` has `Ch_C ∣ F`, so there are finitely many; hence `L` is a finite
union of curves and points, and every irreducible factor of `F` is some `Ch_C`. -/
private theorem exists_isChowPointOf_of_forall_exists
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i] (d : ℕ)
    [Fintype (ULift.{u} (Bidegree N d))] (b : FormSpace k N d)
    (c : ULift.{u} (Bidegree N d) → k) {l : ULift.{u} (Bidegree N d)} (hcl : c l = 1)
    (hc : ∀ β β', c β' • (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N d)) k) -
      c β • MvPolynomial.X β' ∈ b.asHomogeneousIdeal)
    (L : Set (AlgebraicGeometry.Proj (polyGrading k N))) (hL : IsClosed L)
    (hLi : L ⊆ Set.range i)
    (hLF : ∀ y ∈ L, IsClosed ({y} : Set _) → ∀ u v : Fin (N + 1) → k,
      hypForm u ∈ y.asHomogeneousIdeal → hypForm v ∈ y.asHomogeneousIdeal →
        MvPolynomial.eval (Sum.elim u v)
          (formPoly (fun β : ULift.{u} (Bidegree N d) => β.down.1) c) = 0)
    (hFL : ∀ u v : Fin (N + 1) → k, MvPolynomial.eval (Sum.elim u v)
        (formPoly (fun β : ULift.{u} (Bidegree N d) => β.down.1) c) = 0 →
      ∃ y ∈ L, IsClosed ({y} : Set _) ∧ hypForm u ∈ y.asHomogeneousIdeal ∧
        hypForm v ∈ y.asHomogeneousIdeal) :
    ∃ Z, IsChowPointOf i d Z b := by
  classical
  haveI := jacobsonSpace_proj k N
  haveI := noetherianSpace_proj k N
  letI := UniqueFactorizationMonoid.normalizationMonoid
    (α := MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
  set m : ULift.{u} (Bidegree N d) → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ := fun β => β.down.1
  have hm : Function.Injective m := fun β β' h => ULift.ext (Subtype.ext h)
  set F := formPoly m c with hFdef
  have hFm : ∀ β, F.coeff β.down.1 = c β := coeff_formPoly hm c
  have hF0 : F ≠ 0 := fun h => by
    have := hFm l
    rw [h, hcl] at this
    simp at this
  have hFdeg : ∀ e ∈ F.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d := by
    intro e he
    obtain ⟨β, rfl⟩ := mem_range_of_mem_support_formPoly m c he
    exact β.down.2
  choose G n hG using fun C : Mori.ProperCurve (projToSpecCoeff k N) => exists_incidenceForm C
  -- every curve in `L` has its incidence form dividing `F`
  set 𝒮 := {C : Mori.ProperCurve (projToSpecCoeff k N) | C.point ∈ L}
  have hdvd : ∀ C ∈ 𝒮, G C ∣ F := by
    intro C hC
    refine dvd_of_forall_eval (hG C).1 fun x hx => ?_
    rw [← Sum.elim_comp_inl_inr x] at hx ⊢
    have hI := ((hG C).2.1 _ _).mp hx
    unfold IncidenceLocus at hI
    obtain ⟨p, hp, hpu, hpv⟩ := hI
    obtain ⟨y, hy, hyc, hyu, hyv⟩ := exists_isClosed_mem_closure_hypForm p hpu hpv
    have hyL : y ∈ L := (hL.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hC))
      (closure_minimal (Set.singleton_subset_iff.mpr hp) isClosed_closure hy)
    exact hLF y hyL hyc _ _ hyu hyv
  have hfac : ∀ C ∈ 𝒮, ∃ q ∈ UniqueFactorizationMonoid.normalizedFactors F,
      Associated (G C) q := fun C hC =>
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hF0 (hG C).1 (hdvd C hC)
  have h𝒮fin : 𝒮.Finite := by
    choose! q hq hGq using hfac
    refine Set.Finite.of_finite_image (f := q)
      ((UniqueFactorizationMonoid.normalizedFactors F).toFinset.finite_toSet.subset ?_) ?_
    · rintro _ ⟨C, hC, rfl⟩
      exact Multiset.mem_toFinset.mpr (hq C hC)
    · intro C hC C' hC' h
      exact eq_of_associated_incidenceForm (hG C).2.1 (hG C').2.1
        ((hGq C hC).trans (by rw [h]; exact (hGq C' hC').symm))
  -- every point of `L` is a closed point or the generic point of a curve in `L`
  have hcp : ∀ η ∈ L, IsClosed ({η} : Set _) ∨ ∃ C ∈ 𝒮, C.point = η := by
    intro η hη
    by_cases hc : IsClosed ({η} : Set (AlgebraicGeometry.Proj (polyGrading k N)))
    · exact Or.inl hc
    · right
      have hsub : {C : Mori.ProperCurve (projToSpecCoeff k N) | C.point ∈ closure {η}} ⊆ 𝒮 :=
        fun C hC => (hL.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη)) hC
      exact ⟨⟨η, isProperCurve_of_finite hc (h𝒮fin.subset hsub)⟩, hη, rfl⟩
  -- the finitely many closed points of `L` off the curves of `L`
  obtain ⟨T, hTf, hTc, hTi, hT⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hL
  choose! η hη using fun t (ht : t ∈ T) => QuasiSober.sober (hTi t ht) (hTc t ht)
  set Pts := {y | y ∈ L ∧ IsClosed ({y} : Set (AlgebraicGeometry.Proj (polyGrading k N))) ∧
    ∀ C ∈ 𝒮, y ∉ closure {C.point}}
  have hPts : Pts ⊆ η '' T := by
    rintro y ⟨hyL, hyc, hyC⟩
    rw [hT] at hyL
    obtain ⟨t, ht, hyt⟩ := hyL
    have htL : t ⊆ L := hT ▸ Set.subset_sUnion_of_mem ht
    rcases hcp (η t) (htL (hη t ht).mem) with h | ⟨C, hC, hCη⟩
    · refine ⟨t, ht, ?_⟩
      have htη : t = {η t} := (hη t ht).def.symm.trans h.closure_eq
      rw [htη] at hyt
      exact hyt.symm
    · exact absurd (by rw [hCη, (hη t ht).def]; exact hyt) (hyC C hC)
  have hPtsfin : Pts.Finite := (hTf.image η).subset hPts
  haveI := hPtsfin.fintype
  choose a jy hajy hay using fun y : Pts => exists_relations_of_isClosed
    (y : AlgebraicGeometry.Proj (polyGrading k N)) y.2.2.1
  let ℓu : Pts → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k := fun y =>
    ∑ j, MvPolynomial.C (a y j) * MvPolynomial.X (Sum.inl j)
  let ℓv : Pts → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k := fun y =>
    ∑ j, MvPolynomial.C (a y j) * MvPolynomial.X (Sum.inr j)
  have hℓu : ∀ y x, MvPolynomial.eval x (ℓu y) = (x ∘ Sum.inl) ⬝ᵥ a y := fun y x => by
    simp [ℓu, dotProduct, mul_comm]
  have hℓv : ∀ y x, MvPolynomial.eval x (ℓv y) = (x ∘ Sum.inr) ⬝ᵥ a y := fun y x => by
    simp [ℓv, dotProduct, mul_comm]
  have ha0 : ∀ y, a y (jy y) ≠ 0 := fun y => by rw [hajy]; exact one_ne_zero
  -- the zeros of `F` lie on the incidence hypersurfaces of the curves and the points of `L`
  have hcover : ∀ x, MvPolynomial.eval x F = 0 → (∃ C ∈ 𝒮, MvPolynomial.eval x (G C) = 0) ∨
      ∃ y, MvPolynomial.eval x (ℓu y) = 0 ∧ MvPolynomial.eval x (ℓv y) = 0 := by
    intro x hx
    rw [← Sum.elim_comp_inl_inr x] at hx
    obtain ⟨y, hyL, hyc, hyu, hyv⟩ := hFL _ _ hx
    by_cases h : ∃ C ∈ 𝒮, y ∈ closure {C.point}
    · obtain ⟨C, hC, hyC⟩ := h
      refine Or.inl ⟨C, hC, ?_⟩
      rw [← Sum.elim_comp_inl_inr x, (hG C).2.1]
      exact ⟨y, hyC, hyu, hyv⟩
    · push Not at h
      let y' : Pts := ⟨y, hyL, hyc, h⟩
      refine Or.inr ⟨y', ?_, ?_⟩
      · rw [hℓu]
        exact (linearForm_mem_iff (a y') (hajy y') y (hay y') _).mp hyu
      · rw [hℓv]
        exact (linearForm_mem_iff (a y') (hajy y') y (hay y') _).mp hyv
  -- every irreducible factor of `F` is an incidence form
  have hfactor : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors F, ∃ C ∈ 𝒮,
      Associated P (G C) := by
    intro P hP
    have hPirr : Irreducible P := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
    have hPprime : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.mp hPirr
    have hPF : P ∣ F := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hZ : ∀ H, (∀ x, MvPolynomial.eval x F = 0 → MvPolynomial.eval x H = 0) → P ∣ H :=
      fun H hH => dvd_of_forall_eval hPirr fun x hx => hH x (by
        obtain ⟨Q, hQ⟩ := hPF
        rw [hQ, map_mul, hx, zero_mul])
    have hcase : ∀ ℓ : Pts → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k,
        (∀ x, MvPolynomial.eval x F = 0 →
          MvPolynomial.eval x ((∏ C ∈ h𝒮fin.toFinset, G C) * ∏ y, ℓ y) = 0) →
        (∃ C ∈ 𝒮, Associated P (G C)) ∨ ∃ y, P ∣ ℓ y := by
      intro ℓ hℓ
      rcases hPprime.dvd_or_dvd (hZ _ hℓ) with h | h
      · obtain ⟨C, hC, hdC⟩ := (Prime.dvd_finset_prod_iff hPprime _).mp h
        exact Or.inl ⟨C, h𝒮fin.mem_toFinset.mp hC, hPirr.associated_of_dvd (hG C).1 hdC⟩
      · obtain ⟨y, -, hy⟩ := (Prime.dvd_finset_prod_iff hPprime _).mp h
        exact Or.inr ⟨y, hy⟩
    have hH : ∀ ℓ : Pts → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k,
        (∀ x y, MvPolynomial.eval x (ℓu y) = 0 → MvPolynomial.eval x (ℓv y) = 0 →
          MvPolynomial.eval x (ℓ y) = 0) →
        ∀ x, MvPolynomial.eval x F = 0 →
          MvPolynomial.eval x ((∏ C ∈ h𝒮fin.toFinset, G C) * ∏ y, ℓ y) = 0 := by
      intro ℓ hℓ x hx
      simp only [map_mul, map_prod, mul_eq_zero, Finset.prod_eq_zero_iff]
      rcases hcover x hx with ⟨C, hC, h⟩ | ⟨y, h1, h2⟩
      · exact Or.inl ⟨C, h𝒮fin.mem_toFinset.mpr hC, h⟩
      · exact Or.inr ⟨y, Finset.mem_univ _, hℓ x y h1 h2⟩
    rcases hcase ℓu (hH ℓu fun _ _ h _ => h) with h | ⟨y, hy⟩
    · exact h
    rcases hcase ℓv (hH ℓv fun _ _ _ h => h) with h | ⟨y', hy'⟩
    · exact h
    exfalso
    have h1 := associated_of_dvd_of_totalDegree_le_one hPirr
      (linearForm_ne_zero_and_totalDegree_le Sum.inl_injective (a y) (ha0 y)).1
      (linearForm_ne_zero_and_totalDegree_le Sum.inl_injective (a y) (ha0 y)).2 hy
    have h2 := associated_of_dvd_of_totalDegree_le_one hPirr
      (linearForm_ne_zero_and_totalDegree_le Sum.inr_injective (a y') (ha0 y')).1
      (linearForm_ne_zero_and_totalDegree_le Sum.inr_injective (a y') (ha0 y')).2 hy'
    exact not_associated_linearForm_inl_inr (ha0 y) (h1.symm.trans h2)
  -- `F` is associated to `∏_C Ch_C ^ {n_C}`
  set s := UniqueFactorizationMonoid.normalizedFactors F
  set 𝒮f := h𝒮fin.toFinset
  let nC : Mori.ProperCurve (projToSpecCoeff k N) → ℕ := fun C => s.count (normalize (G C))
  have hFassoc : Associated F (∏ C ∈ 𝒮f, G C ^ nC C) := by
    have h1 : Associated s.prod F := UniqueFactorizationMonoid.prod_normalizedFactors hF0
    have h2 : s.prod = ∏ C ∈ 𝒮f, normalize (G C) ^ nC C := by
      rw [Finset.prod_multiset_count]
      have hinj : Set.InjOn (fun C => normalize (G C)) 𝒮f := fun C _ C' _ h =>
        eq_of_associated_incidenceForm (hG C).2.1 (hG C').2.1
          (normalize_eq_normalize_iff_associated.mp h)
      rw [← Finset.prod_image (f := fun q => q ^ s.count q) hinj]
      refine Finset.prod_subset ?_ ?_
      · intro q hq
        obtain ⟨C, hC, hPC⟩ := hfactor q (Multiset.mem_toFinset.mp hq)
        refine Finset.mem_image.mpr ⟨C, h𝒮fin.mem_toFinset.mpr hC, ?_⟩
        rw [← UniqueFactorizationMonoid.normalize_normalized_factor q (Multiset.mem_toFinset.mp hq)]
        exact normalize_eq_normalize_iff_associated.mpr hPC.symm
      · intro q _ hq
        rw [Multiset.count_eq_zero_of_notMem (fun h => hq (Multiset.mem_toFinset.mpr h)),
          pow_zero]
    refine h1.symm.trans ?_
    rw [h2]
    exact Associated.prod _ _ _ fun C _ => (normalize_associated (G C)).pow_pow
  -- the cycle
  have hpre : ∀ C ∈ 𝒮, ∃ C₀ : Mori.ProperCurve (i ≫ projToSpecCoeff k N),
      ProperCurve.mapClosedImmersion i _ C₀ = C := by
    intro C hC
    obtain ⟨x, hx⟩ := hLi hC
    exact ⟨⟨x, (isProperCurve_comp_iff i _ x).mpr (by rw [hx]; exact C.isProperCurve)⟩,
      Mori.ProperCurve.ext hx⟩
  choose pre hpre using hpre
  let Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N) :=
    ∑ C ∈ 𝒮f.attach, (nC C.1 : ℤ) • Finsupp.single (pre C.1 (h𝒮fin.mem_toFinset.mp C.2)) 1
  let Wc : Mori.OneCycle ℤ (projToSpecCoeff k N) := ∑ C ∈ 𝒮f, (nC C : ℤ) • Finsupp.single C 1
  have hZW : Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z = Wc := by
    rw [pushforward_eq_mapDomain, Finsupp.mapDomain_finset_sum,
      show Wc = ∑ C ∈ 𝒮f.attach, (nC C.1 : ℤ) • Finsupp.single C.1 1 from
        (Finset.sum_attach _ (fun C => (nC C : ℤ) • Finsupp.single C 1)).symm]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single, hpre]
  have hWc : ∀ C, Wc C = if C ∈ 𝒮f then (nC C : ℤ) else 0 := by
    intro C
    simp [Wc, Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hprod : ∀ G' : Mori.ProperCurve (projToSpecCoeff k N) →
      MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k,
      ∏ C ∈ Wc.support, G' C ^ (Wc C).toNat = ∏ C ∈ 𝒮f, G' C ^ nC C := by
    intro G'
    have hsupp : Wc.support ⊆ 𝒮f := fun C hC => by
      by_contra h
      exact Finsupp.mem_support_iff.mp hC (by rw [hWc, if_neg h])
    rw [Finset.prod_subset hsupp (fun C _ hC => by
      rw [Finsupp.notMem_support_iff.mp hC, Int.toNat_zero, pow_zero])]
    exact Finset.prod_congr rfl fun C hC => by rw [hWc, if_pos hC, Int.toNat_natCast]
  have hchow : IsChowPoint d Wc b := by
    intro G' hG'
    dsimp only
    rw [hprod G']
    have hassoc : Associated F (∏ C ∈ 𝒮f, G' C ^ nC C) :=
      hFassoc.trans (Associated.prod _ _ _ fun C hC => by
        by_cases hn : nC C = 0
        · rw [hn, pow_zero, pow_zero]
          exact Associated.refl _
        · have hC' : C ∈ Wc.support := Finsupp.mem_support_iff.mpr (by
            rw [hWc, if_pos hC]; exact_mod_cast hn)
          exact (associated_of_forall_eval (hG C).1 (hG' C hC').1 fun x => by
            rw [← Sum.elim_comp_inl_inr x, (hG C).2.1]
            exact ((hG' C hC').2 _ _).symm).pow_pow)
    obtain ⟨w, hw⟩ := hassoc
    obtain ⟨r, hr, hwr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp w.isUnit
    rw [← hw, hwr, mul_comm]
    refine ⟨fun e he => hFdeg e ?_, fun β β' => ?_⟩
    · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at he
      exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul he)
    · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, hFm, hFm]
      have := Ideal.mul_mem_left (b.asHomogeneousIdeal.toIdeal) (MvPolynomial.C r) (hc β β')
      have hEq : (r * c β') • (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N d)) k) -
          (r * c β) • MvPolynomial.X β' =
          MvPolynomial.C r * (c β' • MvPolynomial.X β - c β • MvPolynomial.X β') := by
        simp only [smul_eq_C_mul, map_mul]
        ring
      rw [hEq]
      exact this
  have hdegW : cycleDegree i Z = d := by
    have hw1F : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0)) F d :=
      fun e he => by
        rw [weight_sumElim_one_zero]
        exact (hFdeg e (MvPolynomial.mem_support_iff.mpr he)).1
    have hw1F₁ : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0))
        (∏ C ∈ 𝒮f, G C ^ nC C) (∑ C ∈ 𝒮f, nC C * n C) := by
      have := MvPolynomial.IsWeightedHomogeneous.prod 𝒮f (fun C => G C ^ nC C)
        (fun C => nC C • n C) fun C _ => ((hG C).2.2.2.1).pow _
      simpa only [smul_eq_mul] using this
    obtain ⟨w, hw⟩ := hFassoc
    obtain ⟨r, hr, hwr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp w.isUnit
    have hw1F₁' : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0))
        (∏ C ∈ 𝒮f, G C ^ nC C) d := by
      rw [← hw, hwr]
      simpa using hw1F.mul (MvPolynomial.isWeightedHomogeneous_C _ r)
    have hF₁0 : (∏ C ∈ 𝒮f, G C ^ nC C) ≠ 0 := by
      rw [← hw]; exact mul_ne_zero hF0 w.ne_zero
    have hD := MvPolynomial.IsWeightedHomogeneous.inj_right hF₁0 hw1F₁ hw1F₁'
    haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
    have hdeg1 : ∀ C, Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1) (Finsupp.single C 1) = n C :=
      fun C => (Mori.OneCycle.degree_apply ℤ _ _ _).trans (by
        rw [Finsupp.sum_single_index (by simp), one_mul, (hG C).2.2.1, Int.cast_id])
    simp only [cycleDegree]
    rw [hZW, map_sum]
    simp only [map_zsmul, hdeg1, smul_eq_mul]
    rw [← hD]
    push_cast
    rfl
  refine ⟨Z, ?_, hdegW, ?_⟩
  · exact Finset.sum_nonneg fun C _ =>
      smul_nonneg (Int.natCast_nonneg _) (Finsupp.single_nonneg.mpr zero_le_one)
  · rw [hZW]
    exact hchow

/-- **The Chow-form locus is closed.** There is a closed subset of the space of `(d, d)`-forms
whose closed points are exactly the Chow points of the effective degree-`d` cycles on `X`. It is
the closure of the closed points `[F]` all of whose zeros `(u, v)` have `H_u ∩ H_v` meeting the
vertex locus of `F` on `X`; the complementary property is open by
`exists_isOpen_forall_exists_formLin_mem`. -/
private theorem exists_closeds_chowPoints (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) :
    ∃ W : TopologicalSpace.Closeds (FormSpace k N d), ∀ p, IsClosed ({p} : Set _) →
      (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p) := by
  classical
  haveI := finite_bidegree N d
  haveI := Fintype.ofFinite (ULift.{u} (Bidegree N d))
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  haveI := jacobsonSpace_proj k N
  haveI : JacobsonSpace (FormSpace k N d) :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k _)
  let m : ULift.{u} (Bidegree N d) → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ := fun β => β.down.1
  have hm : Function.Injective m := fun β β' h => ULift.ext (Subtype.ext h)
  have hD : ∀ β, ∑ j, m β j = d + d := fun β => by
    rw [Fintype.sum_sum_type, β.down.2.1, β.down.2.2]
  set sB := Intersection.ProjSpace.toSpec k (ULift.{u} (Bidegree N d))
  let T : Set (pullback sB (projToSpecCoeff k N) : Scheme.{u}) := vertexLocus (k := k) m ∩
    pullback.snd sB (projToSpecCoeff k N) ⁻¹' Set.range i
  have hT : IsClosed T := (isClosed_vertexLocus m).inter
    (i.isClosedEmbedding.isClosed_range.preimage
      (pullback.snd sB (projToSpecCoeff k N)).continuous)
  -- the forms with a zero `(u, v)` such that `H_u ∩ H_v` misses the vertex locus on `X`
  let Bad : FormSpace k N d → Prop := fun b => ∃ x, formLin m x ∈ b.asHomogeneousIdeal ∧
    ∀ z ∈ T, IsClosed ({z} : Set _) → pullback.fst sB (projToSpecCoeff k N) z = b →
      ¬ (hypForm (x ∘ Sum.inl) ∈ (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal ∧
        hypForm (x ∘ Sum.inr) ∈ (pullback.snd sB (projToSpecCoeff k N) z).asHomogeneousIdeal)
  have hBad : ∀ b, IsClosed ({b} : Set (FormSpace k N d)) → Bad b →
      ∃ O, IsOpen O ∧ b ∈ O ∧ ∀ b' ∈ O, IsClosed ({b'} : Set (FormSpace k N d)) → Bad b' := by
    rintro b hb ⟨x, hx, hxT⟩
    exact exists_isOpen_forall_exists_formLin_mem m hm hD sB (𝟙 _)
      (Category.id_comp _) T hT hb x hx hxT
  let good := {b : FormSpace k N d | IsClosed ({b} : Set _) ∧ ¬ Bad b}
  refine ⟨⟨closure good, isClosed_closure⟩, fun b hb => ?_⟩
  have hgood : b ∈ closure good ↔ ¬ Bad b := by
    refine ⟨fun hmem hbad => ?_, fun h => subset_closure ⟨hb, h⟩⟩
    obtain ⟨O, hO, hbO, hOb⟩ := hBad b hb hbad
    obtain ⟨b', hb'O, hb'c, hb'⟩ := mem_closure_iff.mp hmem O hO hbO
    exact hb' (hOb b' hb'O hb'c)
  change b ∈ closure good ↔ _
  rw [hgood]
  -- coordinates of `b`, and the section `ℙᴺ_k ⟶ FormSpace ×ₖ ℙᴺ_k` at `b`
  obtain ⟨c, l, hcl, hc⟩ := exists_relations_of_isClosed b hb
  obtain ⟨jb, hjb, hjbs, hjbf, hjbu⟩ := exists_section_of_isClosed sB (projToSpecCoeff k N) hb
  haveI : LocallyOfFiniteType (jb ≫ pullback.snd sB (projToSpecCoeff k N) ≫
      projToSpecCoeff k N) := by
    rw [← Category.assoc, hjb, Category.id_comp]; infer_instance
  haveI : LocallyOfFiniteType jb :=
    locallyOfFiniteType_of_comp jb (pullback.snd sB (projToSpecCoeff k N) ≫ projToSpecCoeff k N)
  haveI : LocallyOfFiniteType (pullback.fst sB (projToSpecCoeff k N) ≫ sB) := inferInstance
  haveI : JacobsonSpace (pullback sB (projToSpecCoeff k N) : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst sB (projToSpecCoeff k N) ≫ sB)
  have hjbc : ∀ y, IsClosed ({y} : Set (AlgebraicGeometry.Proj (polyGrading k N))) →
      IsClosed ({jb y} : Set _) := fun y hy =>
    Scheme.Hom.closePoints_subset_preimage_closedPoints jb hy
  have hvert : ∀ y : AlgebraicGeometry.Proj (polyGrading k N), IsClosed ({y} : Set _) →
      (jb y ∈ vertexLocus (k := k) m ↔ ∀ u v : Fin (N + 1) → k,
        hypForm u ∈ y.asHomogeneousIdeal → hypForm v ∈ y.asHomogeneousIdeal →
          MvPolynomial.eval c (formLin m (Sum.elim u v)) = 0) := by
    intro y hy
    obtain ⟨a, j, haj, ha⟩ := exists_relations_of_isClosed y hy
    rw [mem_vertexLocus_iff_formLin m (jb y) c hcl (by rw [hjbf]; exact hc) a haj
      (by rw [hjbs]; exact ha)]
    exact ⟨fun h u v hu hv => h u v ((linearForm_mem_iff a haj y ha u).mp hu)
        ((linearForm_mem_iff a haj y ha v).mp hv),
      fun h u v hu hv => h u v ((linearForm_mem_iff a haj y ha u).mpr hu)
        ((linearForm_mem_iff a haj y ha v).mpr hv)⟩
  have hroot : ∀ x, formLin m x ∈ b.asHomogeneousIdeal ↔
      MvPolynomial.eval c (formLin m x) = 0 := fun x =>
    mem_iff_eval_of_relations_one c hcl b hc (isHomogeneous_formLin m x)
  constructor
  · -- a good form is a Chow form
    intro hnb
    refine exists_isChowPointOf_of_forall_exists i d b c hcl hc (jb ⁻¹' T)
      (hT.preimage jb.continuous) (fun y hy => by
        have := hy.2
        rwa [Set.mem_preimage, hjbs] at this) ?_ ?_
    · intro y hy hyc u v hu hv
      rw [eval_formPoly]
      exact (hvert y hyc).mp hy.1 u v hu hv
    · intro u v huv
      by_contra hcon
      apply hnb
      refine ⟨Sum.elim u v, (hroot _).mpr (by rwa [eval_formPoly] at huv), ?_⟩
      intro z hzT hzc hzf ⟨h1, h2⟩
      have hsc : IsClosed ({pullback.snd sB (projToSpecCoeff k N) z} :
          Set (AlgebraicGeometry.Proj (polyGrading k N))) :=
        Scheme.Hom.closePoints_subset_preimage_closedPoints _ hzc
      have hzj := hjbu z hzf hsc
      rw [Sum.elim_comp_inl] at h1
      rw [Sum.elim_comp_inr] at h2
      exact hcon ⟨_, by rw [Set.mem_preimage, ← hzj]; exact hzT, hsc, h1, h2⟩
  · -- a Chow form is good
    rintro ⟨Z, hZ⟩ ⟨x, hx, hxT⟩
    rw [← Sum.elim_comp_inl_inr x, formLin_mem_iff_exists_incidenceLocus i hZ] at hx
    obtain ⟨C, hC, hI⟩ := hx
    unfold IncidenceLocus at hI
    obtain ⟨p, hp, hpu, hpv⟩ := hI
    obtain ⟨y, hy, hyc, hyu, hyv⟩ := exists_isClosed_mem_closure_hypForm p hpu hpv
    have hyC : y ∈ closure {C.point} :=
      closure_minimal (Set.singleton_subset_iff.mpr hp) isClosed_closure hy
    refine hxT (jb y) ⟨(hvert y hyc).mpr ?_, ?_⟩ (hjbc y hyc) (hjbf y) ?_
    · intro u v hu hv
      rw [← hroot, formLin_mem_iff_exists_incidenceLocus i hZ]
      exact ⟨C, hC, y, hyC, hu, hv⟩
    · rw [Set.mem_preimage, hjbs]
      exact (i.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (point_mem_range_of_mem_support_pushforward i Z hC))) hyC
    · rw [hjbs]
      exact ⟨hyu, hyv⟩

/-! ### Chow points and associated forms -/

/-- `G` is an incidence form of the proper curve `C ⊆ ℙᴺ_k`, of bidegree `(n, n)`: the data of
`exists_incidenceForm`. -/
private def IsIncidenceForm (C : Mori.ProperCurve (projToSpecCoeff k N))
    (G : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) (n : ℕ) : Prop :=
  Irreducible G ∧ (∀ u v : Fin (N + 1) → k, MvPolynomial.eval (Sum.elim u v) G = 0 ↔
      IncidenceLocus C u v) ∧
    (haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1;
      (n : ℤ) = C.degree k (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)) ∧
    MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0)) G n ∧
    MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 0) (fun _ => 1)) G n

/-- The Chow product `∏_C Ch_C^{W(C)}` of a 1-cycle `W` on `ℙᴺ_k`, for a choice of incidence
forms. -/
private noncomputable abbrev chowProd
    (G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
    (W : Mori.OneCycle ℤ (projToSpecCoeff k N)) : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k :=
  ∏ C ∈ W.support, G C ^ (W C).toNat

private theorem chowProd_ne_zero
    {G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    {n : Mori.ProperCurve (projToSpecCoeff k N) → ℕ} (hG : ∀ C, IsIncidenceForm C (G C) (n C))
    (W : Mori.OneCycle ℤ (projToSpecCoeff k N)) : chowProd G W ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun C _ => pow_ne_zero _ (hG C).1.ne_zero

/-- Chow products of two choices of incidence forms are associated. -/
private theorem associated_chowProd
    {G G' : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    (W : Mori.OneCycle ℤ (projToSpecCoeff k N))
    (hG : ∀ C ∈ W.support, Irreducible (G C) ∧ ∀ u v : Fin (N + 1) → k,
      MvPolynomial.eval (Sum.elim u v) (G C) = 0 ↔ IncidenceLocus C u v)
    (hG' : ∀ C ∈ W.support, Irreducible (G' C) ∧ ∀ u v : Fin (N + 1) → k,
      MvPolynomial.eval (Sum.elim u v) (G' C) = 0 ↔ IncidenceLocus C u v) :
    Associated (chowProd G W) (chowProd G' W) :=
  Associated.prod _ _ _ fun C hC =>
    (associated_of_forall_eval (hG C hC).1 (hG' C hC).1 fun x => by
      rw [← Sum.elim_comp_inl_inr x, (hG C hC).2, (hG' C hC).2]).pow_pow

/-- The form `∑_b c_b x^b` with the coefficients of a polynomial supported in bidegree `(d, d)` is
that polynomial. -/
private theorem formPoly_coeff {d : ℕ} [Fintype (ULift.{u} (Bidegree N d))]
    {P : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    (hP : ∀ e ∈ P.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d) :
    formPoly (fun β : ULift.{u} (Bidegree N d) => β.down.1) (fun β => P.coeff β.down.1) = P := by
  classical
  have hm : Function.Injective (fun β : ULift.{u} (Bidegree N d) => β.down.1) :=
    fun β β' h => ULift.ext (Subtype.ext h)
  ext e
  by_cases he : e ∈ Set.range (fun β : ULift.{u} (Bidegree N d) => β.down.1)
  · obtain ⟨β, rfl⟩ := he
    exact coeff_formPoly hm _ β
  · rw [show (formPoly (fun β : ULift.{u} (Bidegree N d) => β.down.1)
        (fun β => P.coeff β.down.1)).coeff e = 0 from by
      by_contra h
      exact he (mem_range_of_mem_support_formPoly _ _ (MvPolynomial.mem_support_iff.mpr h))]
    by_contra h
    exact he ⟨⟨⟨e, hP e (MvPolynomial.mem_support_iff.mpr (Ne.symm h))⟩⟩, rfl⟩

/-- **A closed point whose form is associated to the Chow product of an effective cycle is its
Chow point.** -/
private theorem isChowPointOf_of_associated (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) [Fintype (ULift.{u} (Bidegree N d))] (b : FormSpace k N d)
    (c : ULift.{u} (Bidegree N d) → k)
    (hc : ∀ β β', c β' • (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N d)) k) -
      c β • MvPolynomial.X β' ∈ b.asHomogeneousIdeal)
    {G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    {n : Mori.ProperCurve (projToSpecCoeff k N) → ℕ} (hG : ∀ C, IsIncidenceForm C (G C) (n C))
    {Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)} (hZ : 0 ≤ Z)
    (hF : Associated (formPoly (fun β : ULift.{u} (Bidegree N d) => β.down.1) c)
      (chowProd G (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z))) :
    IsChowPointOf i d Z b := by
  classical
  set m : ULift.{u} (Bidegree N d) → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ := fun β => β.down.1
  have hm : Function.Injective m := fun β β' h => ULift.ext (Subtype.ext h)
  set W := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z
  have hWnn : ∀ C, 0 ≤ W C := pushforward_nonneg i _ hZ
  set F := formPoly m c
  have hFdeg : ∀ e ∈ F.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d := by
    intro e he
    obtain ⟨β, rfl⟩ := mem_range_of_mem_support_formPoly m c he
    exact β.down.2
  have hFm : ∀ β, F.coeff β.down.1 = c β := coeff_formPoly hm c
  obtain ⟨w, hw⟩ := hF
  obtain ⟨r, hr, hwr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp w.isUnit
  have hF₁ : chowProd G W = MvPolynomial.C r * F := by rw [← hw, hwr, mul_comm]
  refine ⟨hZ, ?_, fun G' hG' => ?_⟩
  · -- the degree
    have hw1F : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0)) F d :=
      fun e he => by
        rw [weight_sumElim_one_zero]
        exact (hFdeg e (MvPolynomial.mem_support_iff.mpr he)).1
    have hw1F₁ : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0))
        (chowProd G W) (∑ C ∈ W.support, (W C).toNat * n C) := by
      have := MvPolynomial.IsWeightedHomogeneous.prod W.support (fun C => G C ^ (W C).toNat)
        (fun C => (W C).toNat • n C) fun C _ => ((hG C).2.2.2.1).pow _
      simpa only [smul_eq_mul] using this
    have hw1F₁' : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0))
        (chowProd G W) d := by
      rw [hF₁]
      simpa using (MvPolynomial.isWeightedHomogeneous_C _ r).mul hw1F
    have hD := MvPolynomial.IsWeightedHomogeneous.inj_right (chowProd_ne_zero hG W) hw1F₁
      hw1F₁'
    haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
    simp only [cycleDegree]
    erw [Mori.OneCycle.degree_apply, Finsupp.sum]
    rw [← hD]
    push_cast
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Int.toNat_of_nonneg (hWnn C), (hG C).2.2.1]
  · -- the Chow-point relations
    have hassoc := associated_chowProd W (fun C _ => ⟨(hG C).1, (hG C).2.1⟩) hG'
    obtain ⟨w', hw'⟩ := hassoc
    obtain ⟨r', hr', hwr'⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp w'.isUnit
    have hF' : chowProd G' W = MvPolynomial.C (r' * r) * F := by
      rw [← hw', hwr', hF₁, mul_comm, ← mul_assoc, ← MvPolynomial.C_mul, mul_comm r']
    show (∀ e ∈ (chowProd G' W).support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d) ∧
      ∀ β β' : ULift.{u} (Bidegree N d), (chowProd G' W).coeff β'.down.1 •
        (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N d)) k) -
          (chowProd G' W).coeff β.down.1 • MvPolynomial.X β' ∈ b.asHomogeneousIdeal
    rw [hF']
    refine ⟨fun e he => hFdeg e ?_, fun β β' => ?_⟩
    · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at he
      exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul he)
    · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, hFm, hFm]
      have := Ideal.mul_mem_left (b.asHomogeneousIdeal.toIdeal) (MvPolynomial.C (r' * r)) (hc β β')
      have hEq : ((r' * r) * c β') • (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N d)) k) -
          ((r' * r) * c β) • MvPolynomial.X β' =
          MvPolynomial.C (r' * r) * (c β' • MvPolynomial.X β - c β • MvPolynomial.X β') := by
        simp only [smul_eq_C_mul, map_mul]
        ring
      rw [hEq]
      exact this

/-- **The form of a Chow point is associated to the Chow product of its cycle.** -/
private theorem associated_of_isChowPointOf (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) [Fintype (ULift.{u} (Bidegree N d))] (b : FormSpace k N d)
    (c : ULift.{u} (Bidegree N d) → k) {β₀ : ULift.{u} (Bidegree N d)} (hc0 : c β₀ ≠ 0)
    (hc : ∀ β β', c β' • (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N d)) k) -
      c β • MvPolynomial.X β' ∈ b.asHomogeneousIdeal)
    {G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    {n : Mori.ProperCurve (projToSpecCoeff k N) → ℕ} (hG : ∀ C, IsIncidenceForm C (G C) (n C))
    {Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)} (h : IsChowPointOf i d Z b) :
    Associated (formPoly (fun β : ULift.{u} (Bidegree N d) => β.down.1) c)
      (chowProd G (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z)) := by
  classical
  set m : ULift.{u} (Bidegree N d) → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ := fun β => β.down.1
  have hm : Function.Injective m := fun β β' h => ULift.ext (Subtype.ext h)
  set W := Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z
  obtain ⟨hFdeg, hrel⟩ := h.2.2 G fun C _ => ⟨(hG C).1, (hG C).2.1⟩
  set F₁ := chowProd G W
  have hprop := mul_eq_mul_of_relations c (fun β : ULift.{u} (Bidegree N d) => F₁.coeff β.down.1)
    hc0 b hc hrel
  have hF₁0 : F₁ ≠ 0 := chowProd_ne_zero hG W
  have hF₁eq : formPoly m (fun β => F₁.coeff β.down.1) = F₁ := formPoly_coeff hFdeg
  have hc1 : F₁.coeff β₀.down.1 ≠ 0 := by
    intro h0
    apply hF₁0
    rw [← hF₁eq]
    ext e
    have : ∀ β : ULift.{u} (Bidegree N d), F₁.coeff β.down.1 = 0 := fun β => by
      have := hprop β
      rw [h0, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hc0
    simp [formPoly, MvPolynomial.coeff_sum, this]
  have hpoly : formPoly m c = MvPolynomial.C (c β₀ / F₁.coeff β₀.down.1) * F₁ := by
    conv_rhs => arg 2; rw [← hF₁eq]
    ext e
    rw [MvPolynomial.coeff_C_mul]
    by_cases he : e ∈ Set.range m
    · obtain ⟨β, rfl⟩ := he
      rw [coeff_formPoly hm, coeff_formPoly hm]
      have := hprop β
      rw [div_mul_eq_mul_div, eq_div_iff hc1]
      linear_combination -this
    · have h1 : (formPoly m c).coeff e = 0 := by
        by_contra h1
        exact he (mem_range_of_mem_support_formPoly _ _ (MvPolynomial.mem_support_iff.mpr h1))
      have h2 : (formPoly m (fun β => F₁.coeff β.down.1)).coeff e = 0 := by
        by_contra h2
        exact he (mem_range_of_mem_support_formPoly _ _ (MvPolynomial.mem_support_iff.mpr h2))
      rw [h1, h2, mul_zero]
  rw [hpoly]
  exact associated_unit_mul_left F₁ _ ((Ne.isUnit (div_ne_zero hc0 hc1)).map MvPolynomial.C)

/-- The Chow product of a nonnegative combination of effective cycles is the product of their
Chow products. -/
private theorem chowProd_sum {ι : Type*} (s : Finset ι)
    (G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
    (W : ι → Mori.OneCycle ℤ (projToSpecCoeff k N)) (hW : ∀ j ∈ s, ∀ C, 0 ≤ W j C)
    (e : ι → ℕ) :
    chowProd G (∑ j ∈ s, e j • W j) = ∏ j ∈ s, chowProd G (W j) ^ e j := by
  classical
  set T := s.biUnion fun j => (W j).support
  have hext : ∀ V : Mori.OneCycle ℤ (projToSpecCoeff k N), V.support ⊆ T →
      chowProd G V = ∏ C ∈ T, G C ^ (V C).toNat := fun V hV =>
    Finset.prod_subset hV fun C _ hC => by
      rw [Finsupp.notMem_support_iff.mp hC, Int.toNat_zero, pow_zero]
  have happ : ∀ C, (∑ j ∈ s, e j • W j) C = ∑ j ∈ s, (e j : ℤ) * W j C := fun C => by
    simp [Finsupp.finset_sum_apply, nsmul_eq_mul]
  have hsupp : (∑ j ∈ s, e j • W j).support ⊆ T := by
    intro C hC
    rw [Finsupp.mem_support_iff, happ] at hC
    obtain ⟨j, hj, hjC⟩ := Finset.exists_ne_zero_of_sum_ne_zero hC
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hjC)⟩
  have htoNat : ∀ C, ((∑ j ∈ s, e j • W j) C).toNat = ∑ j ∈ s, e j * (W j C).toNat := by
    intro C
    have h0 : 0 ≤ (∑ j ∈ s, e j • W j) C := by
      rw [happ]
      exact Finset.sum_nonneg fun j hj => mul_nonneg (Int.natCast_nonneg _) (hW j hj C)
    have h1 : ((((∑ j ∈ s, e j • W j) C).toNat : ℕ) : ℤ) =
        ((∑ j ∈ s, e j * (W j C).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0, happ]
      push_cast
      exact Finset.sum_congr rfl fun j hj => by rw [Int.toNat_of_nonneg (hW j hj C)]
    exact_mod_cast h1
  rw [hext _ hsupp]
  simp_rw [htoNat, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [hext (W j) (fun C hC => Finset.mem_biUnion.mpr ⟨j, hj, hC⟩), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun C _ => ?_
  rw [← pow_mul, mul_comm]

section WeightedFactors

open MvPolynomial

private theorem weightedHomogeneousComponent_mul_eq {R σ : Type*} [CommRing R] (w : σ → ℕ)
    (P Q : MvPolynomial σ R) (m : ℕ) :
    weightedHomogeneousComponent w m (P * Q) =
      ∑ i ∈ Finset.range (weightedTotalDegree w P + 1),
        ∑ j ∈ Finset.range (weightedTotalDegree w Q + 1),
          if i + j = m then weightedHomogeneousComponent w i P * weightedHomogeneousComponent w j Q
          else 0 := by
  classical
  have hsum : ∀ F : MvPolynomial σ R, F = ∑ i ∈ Finset.range (weightedTotalDegree w F + 1),
      weightedHomogeneousComponent w i F := fun F => by
    conv_lhs => rw [← sum_weightedHomogeneousComponent w F]
    rw [finsum_eq_sum_of_support_subset]
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hi (weightedHomogeneousComponent_eq_zero _ _ (by omega))
  conv_lhs => rw [hsum P, hsum Q, Finset.sum_mul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weightedHomogeneousComponent_of_mem
    ((weightedHomogeneousComponent_isWeightedHomogeneous i P).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous j Q))]
  simp only [eq_comm (a := m)]

private theorem exists_weight_eq_and_le {R σ : Type*} [CommRing R] (w : σ → ℕ) {P : MvPolynomial σ R}
    (hP : P ≠ 0) :
    (∃ e ∈ P.support, Finsupp.weight w e = weightedTotalDegree w P) ∧
      ∃ a, (∃ e ∈ P.support, Finsupp.weight w e = a) ∧ ∀ e ∈ P.support, a ≤ Finsupp.weight w e := by
  classical
  have hne : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hP (support_eq_empty.mp h))
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image P.support (Finsupp.weight w) hne
  obtain ⟨e', he', hmin⟩ := Finset.exists_min_image P.support (Finsupp.weight w) hne
  exact ⟨⟨e, he, le_antisymm (le_weightedTotalDegree w he) (Finset.sup_le fun e' he' => hmax e' he')⟩,
    _, ⟨e', he', rfl⟩, hmin⟩

private theorem weightedHomogeneousComponent_ne_zero_of_mem {R σ : Type*} [CommRing R] (w : σ → ℕ)
    {P : MvPolynomial σ R} {e : σ →₀ ℕ} (he : e ∈ P.support) :
    weightedHomogeneousComponent w (Finsupp.weight w e) P ≠ 0 := by
  classical
  intro h0
  have := congrArg (fun p : MvPolynomial _ _ => p.coeff e) h0
  rw [coeff_weightedHomogeneousComponent, if_pos rfl, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply] at this
  exact mem_support_iff.mp he this

private theorem weightedHomogeneousComponent_eq_zero_of_lt {R σ : Type*} [CommRing R] (w : σ → ℕ)
    {P : MvPolynomial σ R} {a i : ℕ} (ha : ∀ e ∈ P.support, a ≤ Finsupp.weight w e) (hi : i < a) :
    weightedHomogeneousComponent w i P = 0 :=
  weightedHomogeneousComponent_eq_zero' _ _ fun e he h => by have := ha e he; omega

/-- Over a domain, a divisor of a nonzero weighted homogeneous polynomial is weighted
homogeneous. -/
private theorem isWeightedHomogeneous_of_dvd {R σ : Type*} [CommRing R] [IsDomain R] {w : σ → ℕ}
    {F P : MvPolynomial σ R} {n : ℕ} (hF : IsWeightedHomogeneous w F n) (hF0 : F ≠ 0)
    (h : P ∣ F) : IsWeightedHomogeneous w P (weightedTotalDegree w P) := by
  classical
  obtain ⟨Q, rfl⟩ := h
  have hP : P ≠ 0 := left_ne_zero_of_mul hF0
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hF0
  obtain ⟨⟨e₁, he₁, hw₁⟩, a', ⟨e₂, he₂, hw₂⟩, hmin⟩ := exists_weight_eq_and_le w hP
  obtain ⟨⟨f₁, hf₁, hv₁⟩, b', ⟨f₂, hf₂, hv₂⟩, hmin'⟩ := exists_weight_eq_and_le w hQ
  set a := weightedTotalDegree w P
  set b := weightedTotalDegree w Q
  -- a nonzero component of `F` has degree `n`
  have hcomp : ∀ m, weightedHomogeneousComponent w m (P * Q) ≠ 0 → m = n := fun m hm => by
    by_contra hmn
    exact hm (hF.weightedHomogeneousComponent_ne m hmn)
  have hPa := weightedHomogeneousComponent_ne_zero_of_mem w he₁
  have hPa' := weightedHomogeneousComponent_ne_zero_of_mem w he₂
  have hQb := weightedHomogeneousComponent_ne_zero_of_mem w hf₁
  have hQb' := weightedHomogeneousComponent_ne_zero_of_mem w hf₂
  rw [hw₁] at hPa
  rw [hv₁] at hQb
  rw [hw₂] at hPa'
  rw [hv₂] at hQb'
  have ha'a : a' ≤ a := hw₂ ▸ le_weightedTotalDegree w he₂
  have hb'b : b' ≤ b := hv₂ ▸ le_weightedTotalDegree w hf₂
  -- top components
  have htop : weightedHomogeneousComponent w (a + b) (P * Q) =
      weightedHomogeneousComponent w a P * weightedHomogeneousComponent w b Q := by
    rw [weightedHomogeneousComponent_mul_eq, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · rw [if_pos rfl]
    · intro j hj hjb
      rw [if_neg (by have := Finset.mem_range.mp hj; omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
    · intro i hi hia
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [if_neg (by have := Finset.mem_range.mp hi; have := Finset.mem_range.mp hj; omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  -- bottom components
  have hbot : weightedHomogeneousComponent w (a' + b') (P * Q) =
      weightedHomogeneousComponent w a' P * weightedHomogeneousComponent w b' Q := by
    rw [weightedHomogeneousComponent_mul_eq, Finset.sum_eq_single a', Finset.sum_eq_single b']
    · rw [if_pos rfl]
    · intro j _ hjb
      split_ifs with h
      · by_cases hj : j < b'
        · rw [weightedHomogeneousComponent_eq_zero_of_lt w hmin' hj, mul_zero]
        · rw [weightedHomogeneousComponent_eq_zero_of_lt w hmin (show a' < a' by omega), zero_mul]
      · rfl
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · intro i _ hia
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · by_cases hi : i < a'
        · rw [weightedHomogeneousComponent_eq_zero_of_lt w hmin hi, zero_mul]
        · rw [weightedHomogeneousComponent_eq_zero_of_lt w hmin' (show j < b' by omega), mul_zero]
      · rfl
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have h1 := hcomp _ (by rw [htop]; exact mul_ne_zero hPa hQb)
  have h2 := hcomp _ (by rw [hbot]; exact mul_ne_zero hPa' hQb')
  have haa : a' = a := by omega
  intro e he
  exact le_antisymm (le_weightedTotalDegree w (mem_support_iff.mpr he))
    (haa ▸ hmin e (mem_support_iff.mpr he))

end WeightedFactors

section FlatDegree

open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- The fundamental 1-cycle `∑ᵢ mᵢ q_*[Cᵢ]` of the fibre over `s` of a family `π : 𝒞 ⟶ S`,
pushed forward to `Y` along `q`. -/
public noncomputable abbrev fibreCyc {S 𝒞 Y : Scheme.{u}} (sS : S ⟶ Spec (.of k)) (π : 𝒞 ⟶ S)
    (q : 𝒞 ⟶ Y) (sY : Y ⟶ Spec (.of k)) (s : S) : Mori.OneCycle ℤ sY :=
  ∑ᶠ C : {C : Mori.ProperCurve (π.fiberι s ≫ π ≫ sS) //
      closure {C.point} ∈ irreducibleComponents (π.fiber s)},
    ((Module.length ((π.fiber s).presheaf.stalk C.1.point)
        ((π.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
      Mori.cyclePushforwardOfPoint ℤ sY (π.fiberι s ≫ q) C.1.point

/-- The degree of an invertible module on the push-forward of the fundamental cycle of a proper
`k`-scheme of dimension at most one is a difference of Euler characteristics. -/
private theorem degree_eq_eulerSum_sub {Y X₀ : Scheme.{u}}
    (gY : Y ⟶ Spec (.of k)) [IsProper gY] (hY : topologicalKrullDim Y ≤ 1)
    (s₀ : X₀ ⟶ Spec (.of k)) [IsSeparated s₀] [LocallyOfFiniteType s₀] (y : Y ⟶ X₀)
    (hy : y ≫ s₀ = gY) (L : X₀.Modules)
    [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L] :
    Mori.OneCycle.degree ℤ s₀ L
        (∑ᶠ C : {C : Mori.ProperCurve gY // closure ({C.point} : Set Y) ∈ irreducibleComponents Y},
          ((Module.length (Y.presheaf.stalk C.1.point) (Y.presheaf.stalk C.1.point)).toNat : ℤ) •
            Mori.cyclePushforwardOfPoint ℤ s₀ y C.1.point) =
      eulerSum k gY ((Scheme.Modules.pullback y).obj L) -
        eulerSum k gY (SheafOfModules.unit Y.ringCatSheaf) := by
  classical
  haveI : Stacks.Ample.IsInvertibleModule Y (SheafOfModules.unit Y.ringCatSheaf) := inferInstance
  have hpi : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback y).obj L) := inferInstance
  haveI : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback y).obj L) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      Y.presheaf _ _).mpr hpi
  have hcoh : ∀ (H : Y.Modules) [Stacks.Ample.IsInvertibleModule Y H], H.IsCoherent := by
    intro H _
    haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} H 1 :=
      Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Y H
    exact AlgebraicGeometry.SheafOfModules.isCoherent_of_isInvertible k gY H
  haveI hu : (SheafOfModules.unit Y.ringCatSheaf).IsCoherent := hcoh _
  haveI : Stacks.Ample.IsInvertibleModule Y (Stacks.RelativeVeryAmple.tensorModules Y
      (SheafOfModules.unit Y.ringCatSheaf) ((Scheme.Modules.pullback y).obj L)) :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules Y _ _
  haveI hT : (Stacks.RelativeVeryAmple.tensorModules Y (SheafOfModules.unit Y.ringCatSheaf)
      ((Scheme.Modules.pullback y).obj L)).IsCoherent := hcoh _
  have key := MMP.Chow.eulerCharacteristic_tensorModules_sub_eq_degree_fundamentalCycle hY y hy L
    (SheafOfModules.unit Y.ringCatSheaf)
  have key' : eulerSum k gY (Stacks.RelativeVeryAmple.tensorModules Y
        (SheafOfModules.unit Y.ringCatSheaf) ((Scheme.Modules.pullback y).obj L)) -
      eulerSum k gY (SheafOfModules.unit Y.ringCatSheaf) = _ := key
  have hiso := eulerSum_congr k gY (Stacks.TensorSheafSpellingIso.tensorModulesLeftUnitor Y
    ((Scheme.Modules.pullback y).obj L))
  rw [hiso] at key'
  rw [← key']

/-- A `k`-point of `S` at a closed point `s`, with the fibre of `π` over it as a pullback. -/
private theorem exists_kPoint_isPullback {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType sS] (π : 𝒞 ⟶ S) {s : S} (hs : IsClosed ({s} : Set S)) :
    ∃ p : Spec (.of k) ⟶ S, p ≫ sS = 𝟙 _ ∧
      IsPullback (π.fiberι s) (π.fiberι s ≫ π ≫ sS) π p := by
  have hiso : IsIso (CommRingCat.ofHom (MMP.Chow.DeterminantCurveForm.kEval sS s)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (MMP.Chow.DeterminantCurveForm.kEval_bijective sS s hs)
  let ψ : Spec (S.residueField s) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (MMP.Chow.DeterminantCurveForm.kEval sS s))
  haveI : IsIso ψ :=
    (Scheme.Spec.mapIso (asIso (CommRingCat.ofHom
      (MMP.Chow.DeterminantCurveForm.kEval sS s))).op).isIso_hom
  refine ⟨inv ψ ≫ S.fromSpecResidueField s, ?_, ?_⟩
  · rw [Category.assoc, MMP.Chow.DeterminantCurveForm.fromSpecResidueField_comp]
    exact IsIso.inv_hom_id ψ
  · rw [MMP.Chow.DeterminantCurveForm.fiber_structure_eq]
    refine (IsPullback.of_hasPullback π (S.fromSpecResidueField s)).of_iso (Iso.refl _)
      (Iso.refl _) (asIso ψ) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · erw [Iso.refl_hom, Iso.refl_hom, Category.comp_id]
      try erw [Category.id_comp]
      try rfl
    · erw [Iso.refl_hom, Category.id_comp]
      rfl

public theorem isProper_fiberι_comp {S 𝒞 : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType sS] (π : 𝒞 ⟶ S) [IsProper π] {s : S} (hs : IsClosed ({s} : Set S)) :
    IsProper (π.fiberι s ≫ π ≫ sS) := by
  have hiso : IsIso (CommRingCat.ofHom (MMP.Chow.DeterminantCurveForm.kEval sS s)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (MMP.Chow.DeterminantCurveForm.kEval_bijective sS s hs)
  haveI : IsProper (π.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback π (S.fromSpecResidueField s)) inferInstance
  haveI : IsIso (Spec.map (CommRingCat.ofHom (MMP.Chow.DeterminantCurveForm.kEval sS s))) :=
    (Scheme.Spec.mapIso (asIso (CommRingCat.ofHom
      (MMP.Chow.DeterminantCurveForm.kEval sS s))).op).isIso_hom
  rw [MMP.Chow.DeterminantCurveForm.fiber_structure_eq]
  exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _
    (Spec.map (CommRingCat.ofHom (MMP.Chow.DeterminantCurveForm.kEval sS s)))).mpr inferInstance

/-- **Degrees of fibre cycles in a flat proper family over a connected base are constant.** For
`π : 𝒞 ⟶ S` flat, proper and of finite presentation over a connected `S` of finite type over `k`,
with fibres of dimension at most one, and `q : 𝒞 ⟶ Y`, the degree of an invertible module on `Y`
on the push-forward of the fundamental cycle of the fibre is the same at all closed points: it is
`χ(𝒞_s, q^*L) - χ(𝒞_s, 𝒪)`, and both Euler characteristics are constant. -/
public theorem degree_fibreCyc_eq {S 𝒞 Y : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType sS] [ConnectedSpace S] (sY : Y ⟶ Spec (.of k)) [IsSeparated sY]
    [LocallyOfFiniteType sY] (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ Y) (hπq : π ≫ sS = q ≫ sY) [IsProper π]
    [Flat π] [LocallyOfFinitePresentation π]
    (hdim : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) ≤ 1)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    {s s' : S} (hs : IsClosed ({s} : Set S)) (hs' : IsClosed ({s'} : Set S)) :
    Mori.OneCycle.degree ℤ sY L (fibreCyc sS π q sY s) =
      Mori.OneCycle.degree ℤ sY L (fibreCyc sS π q sY s') := by
  have hval : ∀ t (ht : IsClosed ({t} : Set S)),
      Mori.OneCycle.degree ℤ sY L (fibreCyc sS π q sY t) =
        eulerSum k (π.fiberι t ≫ π ≫ sS)
            ((Scheme.Modules.pullback (π.fiberι t)).obj ((Scheme.Modules.pullback q).obj L)) -
          eulerSum k (π.fiberι t ≫ π ≫ sS)
            ((Scheme.Modules.pullback (π.fiberι t)).obj 𝒞.unitModule) := by
    intro t ht
    haveI := isProper_fiberι_comp sS π ht
    rw [degree_eq_eulerSum_sub (π.fiberι t ≫ π ≫ sS) (hdim t ht) sY (π.fiberι t ≫ q)
      (by rw [Category.assoc, hπq]) L]
    congr 1
    · exact eulerSum_congr _ _ ((Scheme.Modules.pullbackComp _ _).app L).symm
    · exact eulerSum_congr _ _ (Scheme.Modules.pullbackUnitIso _).symm
  obtain ⟨p, -, hp⟩ := exists_kPoint_isPullback sS π hs
  obtain ⟨p', -, hp'⟩ := exists_kPoint_isPullback sS π hs'
  rw [hval s hs, hval s' hs',
    eulerSum_eq_of_isPullback_of_isInvertible π ((Scheme.Modules.pullback q).obj L) p p' _ _ hp
      _ _ hp',
    eulerSum_eq_of_isPullback_of_isInvertible π 𝒞.unitModule p p' _ _ hp _ _ hp']

end FlatDegree

section Coordinates

open HomogeneousLocalization MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra awayAlgebra

/-- The closed point `ker e` of `Spec A` given by a `k`-point `e : A →ₐ[k] k`. -/
private def kPt {A : Type u} [CommRing A] [Algebra k A] (e : A →ₐ[k] k) : Spec (.of A) :=
  ⟨RingHom.ker e, RingHom.ker_isPrime _⟩

private theorem chartCoord_self {ι : Type*} (b₀ : ι) : chartCoord (k := k) b₀ b₀ = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [chartCoord, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self ⟨MvPolynomial.X b₀, _⟩

private theorem relation_mem_one {ι : Type*} (β β' : ι) (c c' : k) :
    c' • (MvPolynomial.X β : MvPolynomial ι k) - c • MvPolynomial.X β' ∈ homogeneousSubmodule ι k 1 := by
  rw [mem_homogeneousSubmodule, smul_eq_C_mul, smul_eq_C_mul]
  exact ((isHomogeneous_C _ _).mul (isHomogeneous_X k β)).sub
    ((isHomogeneous_C _ _).mul (isHomogeneous_X k β'))

private theorem mk_relation_eq {ι : Type*} (b₀ β β' : ι) (c c' : k) :
    HomogeneousLocalization.mk
      (⟨1, ⟨c' • MvPolynomial.X β - c • MvPolynomial.X β', relation_mem_one β β' c c'⟩, ⟨MvPolynomial.X b₀, X_mem_one' b₀⟩,
        Submonoid.mem_powers _⟩ :
        NumDenSameDeg (homogeneousSubmodule ι k) (Submonoid.powers (MvPolynomial.X b₀))) =
    algebraMap k (Away (homogeneousSubmodule ι k) (MvPolynomial.X b₀)) c' * chartCoord b₀ β -
      algebraMap k (Away (homogeneousSubmodule ι k) (MvPolynomial.X b₀)) c * chartCoord b₀ β' := by
  apply HomogeneousLocalization.val_injective
  have halg : ∀ c : k, (algebraMap k (Away (homogeneousSubmodule ι k) (MvPolynomial.X b₀)) c).val =
      Localization.mk (MvPolynomial.C c) 1 := fun c => by
    change (HomogeneousLocalization.mk _).val = _
    rw [HomogeneousLocalization.val_mk]
    simp [SetLike.GradeZero.coe_algebraMap]
    rfl
  simp only [chartCoord, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_sub,
    HomogeneousLocalization.val_mul, halg, Localization.mk_mul, one_mul]
  simp only [Localization.mk_eq_mk']
  rw [IsLocalization.mk'_eq_mul_mk'_one (c' • _ - c • _),
    IsLocalization.mk'_eq_mul_mk'_one (MvPolynomial.C c' * _),
    IsLocalization.mk'_eq_mul_mk'_one (MvPolynomial.C c * _), map_sub, sub_mul]
  simp only [smul_eq_C_mul]

/-- **Coordinates of a morphism to projective space near a point.** For a morphism
`ψ : Spec A ⟶ ℙ^ι_k` over `k` and a prime `𝔭` of `A`, there are `g ∉ 𝔭` and elements
`a_β ∈ A_g`, with `a_{β₀} = 1`, such that at every `k`-point `e` of `A_g` the value of `ψ`
is the point `[e(a)]`. -/
private theorem exists_coords {A : Type u} [CommRing A] [Algebra k A] {ι : Type u} [Fintype ι]
    (ψ : Spec (.of A) ⟶ Intersection.ProjSpace k ι)
    (hψ : ψ ≫ Intersection.ProjSpace.toSpec k ι = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (𝔭 : Ideal A) [h𝔭 : 𝔭.IsPrime] :
    ∃ (g : A) (_ : g ∉ 𝔭) (β₀ : ι) (a : ι → Localization.Away g), a β₀ = 1 ∧
      ∀ (e : Localization.Away g →ₐ[k] k) (β β' : ι),
        e (a β') • (MvPolynomial.X β : MvPolynomial ι k) - e (a β) • MvPolynomial.X β' ∈
          (ψ (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))) (kPt e))
            ).asHomogeneousIdeal := by
  classical
  obtain ⟨β₀, hβ₀⟩ := exists_X_notMem (ψ ⟨𝔭, h𝔭⟩)
  set 𝒜 := homogeneousSubmodule ι k
  have hxV : (⟨𝔭, h𝔭⟩ : Spec (.of A)) ∈ ψ ⁻¹ᵁ (Proj.basicOpen 𝒜 (MvPolynomial.X β₀)) := hβ₀
  obtain ⟨_, ⟨g, rfl⟩, hxg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxV
      (ψ ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X β₀)).isOpen
  have hg : g ∉ 𝔭 := hxg
  set j : Spec (.of (Localization.Away g)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))
  have hrange : Set.range (j ≫ ψ) ⊆ Set.range (Proj.awayι 𝒜 (MvPolynomial.X β₀) (X_mem_one' β₀) one_pos) := by
    rintro _ ⟨y, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    have hy : j y ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact ⟨y, rfl⟩
    exact hsub hy
  set θ := IsOpenImmersion.lift (Proj.awayι 𝒜 (MvPolynomial.X β₀) (X_mem_one' β₀) one_pos) (j ≫ ψ) hrange
  have hθ : θ ≫ Proj.awayι 𝒜 (MvPolynomial.X β₀) (X_mem_one' β₀) one_pos = j ≫ ψ :=
    IsOpenImmersion.lift_fac _ _ _
  set ρ := Spec.preimage θ
  have hρ : Spec.map ρ = θ := Spec.map_preimage θ
  have hρk : ∀ c : k, ρ.hom (algebraMap k (Away 𝒜 (MvPolynomial.X β₀)) c) =
      algebraMap k (Localization.Away g) c := by
    have h1 : Spec.map ρ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Away 𝒜 (MvPolynomial.X β₀)))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g))) := by
      rw [← awayι_comp_toSpec (X_mem_one' β₀) one_pos, ← Category.assoc, hρ, hθ, Category.assoc, hψ, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rw [← Spec.map_comp] at h1
    have h2 := Spec.map_injective h1
    intro c
    exact congrArg (fun φ : CommRingCat.of k ⟶ CommRingCat.of (Localization.Away g) => φ.hom c) h2
  refine ⟨g, hg, β₀, fun β => ρ.hom (chartCoord β₀ β), by simp only []; rw [chartCoord_self, map_one],
    fun e β β' => ?_⟩
  have hpt : ψ (j (kPt e)) = Proj.awayι 𝒜 (MvPolynomial.X β₀) (X_mem_one' β₀) one_pos (θ (kPt e)) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hθ]
  rw [hpt, ← MMP.Chow.mk_mem_iff_num_mem_awayι 𝒜 (X_mem_one' β₀) one_pos (θ (kPt e))
    ⟨1, ⟨_, relation_mem_one β β' (e (ρ.hom (chartCoord β₀ β))) (e (ρ.hom (chartCoord β₀ β')))⟩,
      ⟨MvPolynomial.X β₀, X_mem_one' β₀⟩, Submonoid.mem_powers _⟩, mk_relation_eq]
  rw [← hρ]
  change ρ.hom _ ∈ RingHom.ker e
  rw [RingHom.mem_ker, map_sub, map_mul, map_mul, hρk, hρk, map_sub, map_mul, map_mul,
    AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    RingHom.id_apply]
  ring

end Coordinates

section FibreEmbedding

/-- **The fibre of a closed subscheme of `S ×ₖ X'` over a closed point embeds into `X'`.** -/
public theorem isClosedImmersion_fiberι_comp {S 𝒞 X' : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType sS] (sX : X' ⟶ Spec (.of k)) (π : 𝒞 ⟶ S) (q : 𝒞 ⟶ X')
    (hπq : π ≫ sS = q ≫ sX) [IsClosedImmersion (pullback.lift π q hπq)] {s : S}
    (hs : IsClosed ({s} : Set S)) : IsClosedImmersion (π.fiberι s ≫ q) := by
  obtain ⟨p, hp1, hp⟩ := exists_kPoint_isPullback sS π hs
  set l := pullback.lift π q hπq
  let j : X' ⟶ pullback sS sX := pullback.lift (sX ≫ p) (𝟙 X') (by
    rw [Category.assoc, hp1, Category.comp_id, Category.id_comp])
  have hjf : j ≫ pullback.fst sS sX = sX ≫ p := pullback.lift_fst _ _ _
  have hjs : j ≫ pullback.snd sS sX = 𝟙 X' := pullback.lift_snd _ _ _
  have hbot : IsPullback j sX (pullback.fst sS sX) p := by
    refine IsPullback.of_right (h₁₁ := j) (h₁₂ := pullback.snd sS sX) (v₁₁ := sX)
      (v₁₂ := pullback.fst sS sX) (v₁₃ := sX) (h₂₁ := p) (h₂₂ := sS) ?_ hjf
      (IsPullback.of_hasPullback sS sX).flip
    rw [hjs, hp1]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hs' : IsPullback (π.fiberι s) ((π.fiberι s ≫ q) ≫ sX) (l ≫ pullback.fst sS sX) p := by
    rw [Category.assoc, ← hπq, pullback.lift_fst]
    exact hp
  have hcomm : π.fiberι s ≫ l = (π.fiberι s ≫ q) ≫ j := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, hjf, hp.w]
      simp only [Category.assoc, reassoc_of% hπq]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, hjs, Category.comp_id]
  have htop := IsPullback.of_bot hs' hcomm hbot
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) htop inferInstance

end FibreEmbedding

section FlatFamily

/-- A quasi-sober `T₀` space without chains `a ⤳ b ⤳ c` of distinct points has dimension at
most one. -/
private theorem topologicalKrullDim_le_one_of_no_chain {F : Type*} [TopologicalSpace F]
    [QuasiSober F] [T0Space F] (h : ∀ a b c : F, a ⤳ b → b ⤳ c → a ≠ b → b ≠ c → False) :
    topologicalKrullDim F ≤ 1 := by
  by_contra hlt
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim F := by
    generalize topologicalKrullDim F = x at hlt ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact absurd bot_le hlt
    | coe n =>
      induction n using ENat.recTopCoe with
      | top => exact WithBot.coe_le_coe.mpr le_top
      | coe m =>
        have hm : ¬ m ≤ 1 := fun h => hlt (by
          have : (m : ℕ∞) ≤ 1 := by exact_mod_cast h
          exact WithBot.coe_le_coe.mpr this)
        have : (2 : ℕ∞) ≤ (m : ℕ∞) := by exact_mod_cast (show 2 ≤ m by omega)
        exact WithBot.coe_le_coe.mpr this
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h2
  have hgen : ∀ i, ∃ g : F, closure {g} = (p i : Set F) := fun i =>
    let ⟨g, hg⟩ := QuasiSober.sober (p i).isIrreducible (p i).isClosed; ⟨g, hg.def⟩
  choose g hg using hgen
  have hlt : ∀ i j, p i < p j → g j ⤳ g i ∧ g j ≠ g i := by
    intro i j hij
    have hsub : (p i : Set F) ⊆ p j := hij.le
    refine ⟨specializes_iff_closure_subset.mpr (by rw [hg, hg]; exact hsub), fun he => ?_⟩
    have : (p i : Set F) = p j := by rw [← hg, ← hg, he]
    exact hij.ne (TopologicalSpace.IrreducibleCloseds.ext this)
  have h01 := hlt ⟨0, by omega⟩ ⟨1, by omega⟩ (p.strictMono (by simp [Fin.lt_def]))
  have h12 := hlt ⟨1, by omega⟩ ⟨2, by omega⟩ (p.strictMono (by simp [Fin.lt_def]))
  exact h _ _ _ h12.1 h01.1 h12.2 h01.2

/-- The local ring at the generic point of an irreducible component of a locally Noetherian scheme
has finite positive length. -/
public theorem toNat_length_stalk_pos {F : Scheme.{u}} [IsLocallyNoetherian F] {ξ : F}
    (hξ : closure ({ξ} : Set F) ∈ irreducibleComponents F) :
    0 < (Module.length (F.presheaf.stalk ξ) (F.presheaf.stalk ξ)).toNat := by
  have hne := (Stacks.Chow.length_stalk_ne_top_iff_mem_genericPoints ξ).mpr hξ
  have h0 : Module.length (F.presheaf.stalk ξ) (F.presheaf.stalk ξ) ≠ 0 := by
    rw [Ne, Module.length_eq_zero_iff]
    exact not_subsingleton _
  exact Nat.pos_of_ne_zero (fun h => (ENat.toNat_eq_zero.mp h).elim h0 hne)

/-- **The flat family of a component of the support incidence.** For a morphism `φ` from a normal
variety `S`, covered by spectra of Dedekind domains, to the Chow-form locus, and a closed point
`s₀`, the reduced structure on an irreducible component of the support incidence through a
vertical curve over `s₀` is a flat proper family of curves in `S ×ₖ X`. Its fibre cycles are
supported on the cycles `chowCycle (φ s)`, and the fibre cycle over `s₀` is nonzero. -/
private theorem exists_flatFamily (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)) (hS : Mori.IsNormalVariety k sS)
    (hDed : ∀ s : S, ∃ U : S.Opens, s ∈ (U : Set S) ∧ IsAffineOpen U ∧
      IsDedekindDomain Γ(S, U))
    (φ : S ⟶ FormSpace k N d) (hφ : φ ≫ ProjSpace.toSpec k _ = sS) (hφW : ∀ s, φ s ∈ W)
    {s₀ : S} (hs₀ : IsClosed ({s₀} : Set S)) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ S) (q : Y ⟶ X) (hπq : π ≫ sS = q ≫ (i ≫ projToSpecCoeff k N)),
      IsClosedImmersion (pullback.lift π q hπq) ∧ IsProper π ∧ Flat π ∧
      LocallyOfFinitePresentation π ∧
      (∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1) ∧
      (∀ s : S, IsClosed ({s} : Set S) →
        ∀ C ∈ (fibreCyc sS π q (i ≫ projToSpecCoeff k N) s).support,
          C ∈ (chowCycle i d (φ s)).support) ∧
      fibreCyc sS π q (i ≫ projToSpecCoeff k N) s₀ ≠ 0 := by
  classical
  haveI := hS.1
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set sX := i ≫ projToSpecCoeff k N with hsX
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  haveI := jacobsonSpace_proj k N
  haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : LocallyOfFiniteType (pullback.fst sS sX ≫ sS) := inferInstance
  haveI : JacobsonSpace (pullback sS sX : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst sS sX ≫ sS)
  haveI : IsLocallyNoetherian (pullback sS sX : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst sS sX ≫ sS)
  haveI : CompactSpace (pullback sS sX : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst sS sX ≫ sS)
  haveI : IsNoetherian (pullback sS sX : Scheme.{u}) := {}
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  haveI : IsProper (pullback.fst sS sX) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback sS sX).flip
      inferInstance
  obtain ⟨I, hI, hpin, hdom⟩ := exists_supportIncidence i d hd W hW S sS hS φ hφ hφW
  -- a curve of the cycle at `s₀`
  haveI : LocallyOfFiniteType (φ ≫ Intersection.ProjSpace.toSpec k _) := hφ ▸ inferInstance
  haveI := finite_bidegree N d
  haveI : LocallyOfFiniteType φ :=
    locallyOfFiniteType_of_comp φ (Intersection.ProjSpace.toSpec k _)
  haveI : JacobsonSpace (FormSpace k N d) :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k _)
  have hφc : ∀ s : S, IsClosed ({s} : Set S) → IsClosed ({φ s} : Set (FormSpace k N d)) :=
    fun s hs => Scheme.Hom.closePoints_subset_preimage_closedPoints φ hs
  have hch : ∀ s : S, IsClosed ({s} : Set S) → IsChowPointOf i d (chowCycle i d (φ s)) (φ s) :=
    fun s hs => isChowPointOf_chowCycle ((hW _ (hφc s hs)).mp (hφW s))
  obtain ⟨C₀, hC₀⟩ : (chowCycle i d (φ s₀)).support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at h
    have := (hch s₀ hs₀).2.1
    rw [h] at this
    simp only [cycleDegree, map_zero] at this
    omega
  -- the vertical curve over `s₀`
  obtain ⟨j, hj, hjs, hjf, hju⟩ := exists_section_of_isClosed sS sX hs₀
  haveI : LocallyOfFiniteType (j ≫ pullback.snd sS sX ≫ sX) := by
    rw [← Category.assoc, hj, Category.id_comp]; infer_instance
  haveI : LocallyOfFiniteType j := locallyOfFiniteType_of_comp j (pullback.snd sS sX ≫ sX)
  set V₀ := j '' closure {C₀.point}
  have hV₀I : V₀ ⊆ I := by
    have hpre : closure ({C₀.point} : Set X) ⊆ j ⁻¹' I := by
      refine subset_trans (JacobsonSpace.closure_inter_closedPoints isClosed_closure).symm.subset ?_
      refine (hI.preimage j.continuous).closure_subset_iff.mpr fun y ⟨hy, hyc⟩ => ?_
      have hjyc : IsClosed ({j y} : Set _) :=
        Scheme.Hom.closePoints_subset_preimage_closedPoints j hyc
      refine (hpin (j y) hjyc).mpr ?_
      rw [hjs, hjf]
      exact Set.mem_biUnion hC₀ hy
    rintro _ ⟨y, hy, rfl⟩
    exact hpre hy
  have hV₀irr : IsIrreducible V₀ :=
    isIrreducible_singleton.closure.image j j.continuous.continuousOn
  -- a maximal irreducible `Z ⊆ I` containing `V₀`
  obtain ⟨T, hTf, hTc, hTi, hT⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hI
  have hsubT : ∀ A : Set (pullback sS sX : Scheme.{u}), IsIrreducible A → A ⊆ I →
      ∃ t ∈ T, A ⊆ t := by
    intro A hA hAI
    obtain ⟨t, ht, h⟩ := (isIrreducible_iff_sUnion_isClosed.mp hA) hTf.toFinset
      (fun t ht => hTc t (hTf.mem_toFinset.mp ht)) (by rw [hTf.coe_toFinset, ← hT]; exact hAI)
    exact ⟨t, hTf.mem_toFinset.mp ht, h⟩
  obtain ⟨Z, ⟨hZT, hV₀Z⟩, hZmaxT⟩ := Set.Finite.exists_maximalFor id {t | t ∈ T ∧ V₀ ⊆ t}
    (hTf.subset fun t ht => ht.1) (let ⟨t, ht, h⟩ := hsubT V₀ hV₀irr hV₀I; ⟨t, ht, h⟩)
  have hZI : Z ⊆ I := hT ▸ Set.subset_sUnion_of_mem hZT
  have hZmax : Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Z := by
    refine ⟨⟨hTi Z hZT, hZI⟩, fun T' ⟨hT'i, hT'I⟩ hZT' => ?_⟩
    obtain ⟨t', ht', hT't'⟩ := hsubT T' hT'i hT'I
    have := hZmaxT ⟨ht', hV₀Z.trans (hZT'.trans hT't')⟩ (hZT'.trans hT't')
    exact hT't'.trans this
  have hZc : IsClosed Z := hTc Z hZT
  -- the reduced subscheme on `Z`
  let J := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZc⟩ : TopologicalSpace.Closeds _)
  haveI : IsReduced J.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hrange : Set.range J.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hemb := J.subschemeι.isClosedEmbedding
  haveI : IrreducibleSpace J.subscheme := by
    have h1 : IsIrreducible (Set.univ : Set (Set.range J.subschemeι)) :=
      (Subtype.irreducibleSpace (hrange ▸ hTi Z hZT : IsIrreducible (Set.range J.subschemeι))
        ).isIrreducible_univ
    have h2 := h1.image hemb.isEmbedding.toHomeomorph.symm
      hemb.isEmbedding.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ, Homeomorph.range_coe] at h2
    exact (irreducibleSpace_def _).mpr h2
  haveI : IsIntegral J.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  set l := J.subschemeι
  set π := l ≫ pullback.fst sS sX
  set q := l ≫ pullback.snd sS sX
  have hπq : π ≫ sS = q ≫ sX := by simp only [π, q, Category.assoc, pullback.condition]
  have hlift : pullback.lift π q hπq = l :=
    pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  haveI hli : IsClosedImmersion (pullback.lift π q hπq) := by rw [hlift]; infer_instance
  haveI : IsProper π := inferInstance
  haveI : LocallyOfFiniteType π := inferInstance
  -- the generic point of `J.subscheme` lies over that of `S`
  have hrangeπ : Set.range π = pullback.fst sS sX '' Z := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
  have hgen : π (genericPoint J.subscheme) ∈ genericPoints S := by
    have hcl : closure ({π (genericPoint J.subscheme)} : Set S) = Set.univ := by
      have hd := (hdom Z hZmax).closure_eq
      rw [← hrangeπ] at hd
      refine Set.eq_univ_of_univ_subset (hd ▸ closure_minimal ?_ isClosed_closure)
      rintro _ ⟨y, rfl⟩
      exact specializes_iff_mem_closure.mp ((genericPoint_specializes y).map π.continuous)
    show closure _ ∈ irreducibleComponents S
    rw [hcl, irreducibleComponents_eq_singleton]
    exact Set.mem_singleton _
  haveI hflat : Flat π := flat_of_mem_genericPoints_of_isDedekindDomain π hDed hgen
  haveI : LocallyOfFinitePresentation π := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
    inferInstance
  -- the closed fibres embed into `X`
  have hmimm : ∀ s : S, IsClosed ({s} : Set S) → IsClosedImmersion (π.fiberι s ≫ q) :=
    fun s hs => isClosedImmersion_fiberι_comp sS sX π q hπq hs
  have hfibemb : ∀ s : S, IsClosed ({s} : Set S) →
      Topology.IsClosedEmbedding (π.fiberι s) := fun s hs =>
    ⟨(π.fiberι s).isEmbedding, by rw [Scheme.Hom.range_fiberι]; exact hs.preimage π.continuous⟩
  -- the image of a closed fibre lies on the support of the cycle
  have hrangeS : ∀ s : S, IsClosed ({s} : Set S) → Set.range (π.fiberι s ≫ q) ⊆
      ⋃ C ∈ (chowCycle i d (φ s)).support, closure {C.point} := by
    intro s hs
    have hsupp : IsClosed (⋃ C ∈ (chowCycle i d (φ s)).support, closure ({C.point} : Set X)) :=
      isClosed_biUnion_finset fun _ _ => isClosed_closure
    haveI hFp : IsProper (π.fiberι s ≫ π ≫ sS) := isProper_fiberι_comp sS π hs
    haveI : LocallyOfFiniteType (π.fiberι s ≫ π ≫ sS) := hFp.toLocallyOfFiniteType
    haveI : JacobsonSpace (π.fiber s) :=
      LocallyOfFiniteType.jacobsonSpace (π.fiberι s ≫ π ≫ sS)
    have hpre := hsupp.preimage (π.fiberι s ≫ q).continuous
    have hcl : closedPoints (π.fiber s) ⊆ (π.fiberι s ≫ q) ⁻¹'
        ⋃ C ∈ (chowCycle i d (φ s)).support, closure ({C.point} : Set X) := by
      intro y hy
      have hy' : IsClosed ({π.fiberι s y} : Set J.subscheme) := by
        rw [← Set.image_singleton]; exact (hfibemb s hs).isClosedMap _ hy
      have hz : IsClosed ({l (π.fiberι s y)} : Set _) := by
        rw [← Set.image_singleton]; exact hemb.isClosedMap _ hy'
      have hzI : l (π.fiberι s y) ∈ I := hZI (hrange ▸ ⟨_, rfl⟩)
      have hf : pullback.fst sS sX (l (π.fiberι s y)) = s := by
        have : π.fiberι s y ∈ Set.range (π.fiberι s) := ⟨y, rfl⟩
        rw [Scheme.Hom.range_fiberι] at this
        rw [← Scheme.Hom.comp_apply]
        exact this
      have := (hpin _ hz).mp hzI
      rw [hf] at this
      rw [Set.mem_preimage, Scheme.Hom.comp_apply]
      exact this
    rintro _ ⟨y, rfl⟩
    have h2 : closure (closedPoints (π.fiber s)) ⊆ _ := hpre.closure_subset_iff.mpr hcl
    rw [closure_closedPoints] at h2
    exact h2 (Set.mem_univ y)
  -- closed fibres have dimension at most one
  have hdimle : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) ≤ 1 := by
    intro s hs
    haveI := hmimm s hs
    refine topologicalKrullDim_le_one_of_no_chain fun a b c hab hbc hab' hbc' => ?_
    have hminj := (π.fiberι s ≫ q).isClosedEmbedding.injective
    obtain ⟨C, -, haC⟩ := Set.mem_iUnion₂.mp (hrangeS s hs ⟨a, rfl⟩)
    have h1 : C.point ⤳ (π.fiberι s ≫ q) a := specializes_iff_mem_closure.mpr haC
    have h2 := hab.map (π.fiberι s ≫ q).continuous
    have h3 := hbc.map (π.fiberι s ≫ q).continuous
    by_cases hCa : C.point = (π.fiberι s ≫ q) a
    · exact ProperCurve.false_of_specializes_chain C (by rw [hCa]; exact h2) h3
        (fun h => hab' (hminj (hCa.symm.trans h))) (fun h => hbc' (hminj h))
    · exact ProperCurve.false_of_specializes_chain C h1 h2 hCa (fun h => hab' (hminj h))
  -- the vertical curve gives a point of the fibre over `s₀`
  obtain ⟨y₀, hy₀⟩ : j C₀.point ∈ Set.range l := hrange ▸ hV₀Z ⟨C₀.point, subset_closure rfl, rfl⟩
  have hπy₀ : π y₀ = s₀ := by
    rw [Scheme.Hom.comp_apply, hy₀, hjf]
  obtain ⟨ξ₀, hξ₀⟩ : y₀ ∈ Set.range (π.fiberι s₀) := by
    rw [Scheme.Hom.range_fiberι]; exact hπy₀
  have hmξ₀ : (π.fiberι s₀ ≫ q) ξ₀ = C₀.point := by
    rw [Scheme.Hom.comp_apply, hξ₀, Scheme.Hom.comp_apply, hy₀, hjs]
  have hdim₀ : topologicalKrullDim (π.fiber s₀) = 1 := by
    haveI := hmimm s₀ hs₀
    refine le_antisymm (hdimle s₀ hs₀) ?_
    obtain ⟨w, hw, hwne⟩ :=
      MMP.Chow.DeterminantCurveForm.exists_specializes_ne_of_isProperCurve sX C₀.point
        C₀.isProperCurve
    rw [← hmξ₀] at hw hwne
    obtain ⟨ξ', hξ', hξ'w⟩ :=
      MMP.Chow.DeterminantCurveForm.exists_specializes_lift (π.fiberι s₀ ≫ q).isClosedMap hw
    exact one_le_topologicalKrullDim_of_specializes hξ' (fun h => hwne (by rw [← hξ'w, h]))
  -- all closed fibres are one-dimensional
  have hrel := relativeDimension_of_ringKrullDim_stalk_le_one π
    (ringKrullDim_stalk_le_one_of_isDedekindDomain hDed) hgen
  have hsurj : Function.Surjective π := by
    have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hd := (hdom Z hZmax).closure_eq
    rw [← hrangeπ, hcl.closure_eq] at hd
    exact fun s => Set.eq_univ_iff_forall.mp hd s
  have hne : ∀ t, Nonempty (π.fiber t) := fun t => by
    obtain ⟨y, hy⟩ := hsurj t
    obtain ⟨ξ, -⟩ : y ∈ Set.range (π.fiberι t) := by rw [Scheme.Hom.range_fiberι]; exact hy
    exact ⟨ξ⟩
  have hdimall : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) = 1 := by
    intro s hs
    rw [(hrel s (hne s)).2, ← (hrel s₀ (hne s₀)).2, hdim₀]
  -- the support of the fibre cycles
  have hcycsupp : ∀ s : S, IsClosed ({s} : Set S) →
      ∀ C ∈ (fibreCyc sS π q sX s).support, C ∈ (chowCycle i d (φ s)).support := by
    intro s hs C hC
    have hCr : C.point ∈ Set.range (π.fiberι s ≫ q) := by
      by_contra hn
      apply Finsupp.mem_support_iff.mp hC
      refine MMP.Chow.DeterminantCurveForm.finsum_apply_eq_zero _ C fun C' => ?_
      rw [Finsupp.smul_apply]
      unfold Mori.cyclePushforwardOfPoint
      split_ifs with h
      · rw [Finsupp.single_apply, if_neg (fun he => hn ⟨C'.1.point, by rw [← he]⟩), smul_zero]
      · simp
    obtain ⟨C'', hC'', hCC''⟩ := Set.mem_iUnion₂.mp (hrangeS s hs hCr)
    by_cases he : C.point = C''.point
    · rwa [show C = C'' from Mori.ProperCurve.ext he]
    · exfalso
      have hcl := ProperCurve.isClosed_singleton_of_specializes C''
        (specializes_iff_mem_closure.mpr hCC'') (Ne.symm he)
      obtain ⟨w, hw, hwne⟩ :=
        MMP.Chow.DeterminantCurveForm.exists_specializes_ne_of_isProperCurve sX C.point
          C.isProperCurve
      have := specializes_iff_mem_closure.mp hw
      rw [hcl.closure_eq, Set.mem_singleton_iff] at this
      exact hwne this
  -- the fibre cycle over `s₀` is nonzero
  have hne₀ : fibreCyc sS π q sX s₀ ≠ 0 := by
    haveI := hmimm s₀ hs₀
    haveI hFp : IsProper (π.fiberι s₀ ≫ π ≫ sS) := isProper_fiberι_comp sS π hs₀
    haveI : LocallyOfFiniteType (π.fiberι s₀ ≫ π ≫ sS) := hFp.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (π.fiber s₀) :=
      LocallyOfFiniteType.isLocallyNoetherian (π.fiberι s₀ ≫ π ≫ sS)
    haveI : CompactSpace (π.fiber s₀) :=
      QuasiCompact.compactSpace_of_compactSpace (π.fiberι s₀ ≫ π ≫ sS)
    haveI : IsNoetherian (π.fiber s₀) := {}
    have hms : (π.fiberι s₀ ≫ q) ≫ sX = π.fiberι s₀ ≫ π ≫ sS := by
      simp only [Category.assoc, hπq]
    have hξc : Mori.IsProperCurve (π.fiberι s₀ ≫ π ≫ sS) ξ₀ := by
      rw [← hms]
      exact (isProperCurve_comp_iff (π.fiberι s₀ ≫ q) sX ξ₀).mpr (hmξ₀ ▸ C₀.isProperCurve)
    have hξirr : closure ({ξ₀} : Set (π.fiber s₀)) ∈ irreducibleComponents (π.fiber s₀) := by
      rw [MMP.Chow.DeterminantCurveForm.closure_singleton_mem_irreducibleComponents_iff]
      intro η hη
      by_contra hne'
      obtain ⟨w, hw, hwne⟩ :=
        MMP.Chow.DeterminantCurveForm.exists_specializes_ne_of_isProperCurve sX C₀.point
          C₀.isProperCurve
      rw [← hmξ₀] at hw hwne
      obtain ⟨ξ', hξ', hξ'w⟩ :=
        MMP.Chow.DeterminantCurveForm.exists_specializes_lift (π.fiberι s₀ ≫ q).isClosedMap hw
      exact MMP.Chow.DeterminantCurveForm.not_chain_of_topologicalKrullDim_le_one
        (hdimle s₀ hs₀) hη hξ' hne' (fun h => hwne (by rw [← hξ'w, h]))
    let ι' := {C : Mori.ProperCurve (π.fiberι s₀ ≫ π ≫ sS) //
      closure ({C.point} : Set (π.fiber s₀)) ∈ irreducibleComponents (π.fiber s₀)}
    haveI : Finite ι' := by
      haveI := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
        (α := π.fiber s₀)).to_subtype
      refine Finite.of_injective (fun C : ι' => (⟨_, C.2⟩ : irreducibleComponents (π.fiber s₀)))
        fun C₁ C₂ h => Subtype.ext (Mori.ProperCurve.ext ?_)
      exact (inseparable_iff_closure_eq.mpr (congrArg Subtype.val h)).eq
    letI : Fintype ι' := Fintype.ofFinite _
    let C₀' : ι' := ⟨⟨ξ₀, hξc⟩, hξirr⟩
    have hterm : ∀ C' : ι', 0 ≤ (((Module.length ((π.fiber s₀).presheaf.stalk C'.1.point)
        ((π.fiber s₀).presheaf.stalk C'.1.point)).toNat : ℤ) •
          Mori.cyclePushforwardOfPoint ℤ sX (π.fiberι s₀ ≫ q) C'.1.point) C₀ := by
      intro C'
      rw [Finsupp.smul_apply, smul_eq_mul]
      refine mul_nonneg (Int.natCast_nonneg _) ?_
      unfold Mori.cyclePushforwardOfPoint
      split_ifs
      · exact Finsupp.single_nonneg.mpr (Int.natCast_nonneg _) C₀
      · exact le_rfl
    have hpos : 0 < (((Module.length ((π.fiber s₀).presheaf.stalk C₀'.1.point)
        ((π.fiber s₀).presheaf.stalk C₀'.1.point)).toNat : ℤ) •
          Mori.cyclePushforwardOfPoint ℤ sX (π.fiberι s₀ ≫ q) C₀'.1.point) C₀ := by
      rw [Finsupp.smul_apply, smul_eq_mul]
      refine mul_pos (by exact_mod_cast toNat_length_stalk_pos hξirr) ?_
      unfold Mori.cyclePushforwardOfPoint
      rw [dif_pos (show Mori.IsProperCurve sX ((π.fiberι s₀ ≫ q) ξ₀) by
        rw [hmξ₀]; exact C₀.isProperCurve)]
      rw [show (⟨(π.fiberι s₀ ≫ q) ξ₀, _⟩ : Mori.ProperCurve sX) = C₀ from
        Mori.ProperCurve.ext hmξ₀, Finsupp.single_eq_same, residueFieldDegree_eq_one]
      norm_num
    intro h0
    have h2 : (fibreCyc sS π q sX s₀) C₀ = ∑ C' : ι', (((Module.length
        ((π.fiber s₀).presheaf.stalk C'.1.point) ((π.fiber s₀).presheaf.stalk C'.1.point)).toNat
          : ℤ) • Mori.cyclePushforwardOfPoint ℤ sX (π.fiberι s₀ ≫ q) C'.1.point) C₀ := by
      unfold fibreCyc
      rw [finsum_eq_sum_of_fintype, Finsupp.finset_sum_apply]
    rw [h0, Finsupp.coe_zero, Pi.zero_apply] at h2
    have := Finset.single_le_sum (fun C' _ => hterm C') (Finset.mem_univ C₀')
    linarith
  exact ⟨J.subscheme, π, q, hπq, hli, inferInstance, hflat, inferInstance, hdimall, hcycsupp,
    hne₀⟩

/-- The real-valued Cartier degree of the cast of an integral 1-cycle is the cast of its integral
degree. -/
public theorem cartierDegree_mapRange_cast {Y₀ : Scheme.{u}} {sY₀ : Y₀ ⟶ Spec (.of k)}
    (E : Y₀.CartierDivisor) (Z : Mori.OneCycle ℤ sY₀) :
    Mori.OneCycle.cartierDegree E (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero Z) =
      (Mori.OneCycle.degree ℤ sY₀ (MMP.CartierDivisor.sheaf E) Z : ℝ) := by
  unfold Mori.OneCycle.cartierDegree
  rw [Mori.OneCycle.degree_apply, Mori.OneCycle.degree_apply,
    Finsupp.sum_mapRange_index (fun _ => zero_mul _)]
  simp [Finsupp.sum]

/-- **The Chow morphism of the flat family of a component.** In the situation of
`exists_flatFamily`, over a connected base, the fibre cycles `cX s` of the family have Chow points
`ψ s` given by a morphism `ψ`, are supported on the cycles `chowCycle (φ s)`, and have constant
degree against every Cartier divisor of `X`. -/
private theorem exists_chowFamily (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)) (hS : Mori.IsNormalVariety k sS) [ConnectedSpace S]
    (hDed : ∀ s : S, ∃ U : S.Opens, s ∈ (U : Set S) ∧ IsAffineOpen U ∧
      IsDedekindDomain Γ(S, U))
    (φ : S ⟶ FormSpace k N d) (hφ : φ ≫ ProjSpace.toSpec k _ = sS) (hφW : ∀ s, φ s ∈ W)
    {s₀ : S} (hs₀ : IsClosed ({s₀} : Set S)) (E : X.CartierDivisor) :
    ∃ (e' : ℕ) (_ : 0 < e') (ψ : S ⟶ FormSpace k N e')
      (cX : S → Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)),
      ψ ≫ ProjSpace.toSpec k _ = sS ∧
      (∀ s : S, IsClosed ({s} : Set S) →
        IsClosed ({ψ s} : Set _) ∧ IsChowPointOf i e' (cX s) (ψ s)) ∧
      (∀ s : S, IsClosed ({s} : Set S) → ∀ C ∈ (cX s).support,
        C ∈ (chowCycle i d (φ s)).support) ∧
      (∀ s s' : S, IsClosed ({s} : Set S) → IsClosed ({s'} : Set S) →
        Mori.OneCycle.cartierDegree E (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (cX s)) =
          Mori.OneCycle.cartierDegree E
            (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (cX s'))) := by
  classical
  haveI := hS.1
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  haveI : IsProper (projToSpecCoeff k N) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff (R := k) N
  haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
  obtain ⟨Y, π, q, hπq, hli, hprop, hflat, hlofp, hdim, hsupp, hne₀⟩ :=
    exists_flatFamily i d hd W hW S sS hS hDed φ hφ hφW hs₀
  set sX := i ≫ projToSpecCoeff k N
  let cX : S → Mori.OneCycle ℤ sX := fibreCyc sS π q sX
  have hdimle : ∀ s : S, IsClosed ({s} : Set S) → topologicalKrullDim (π.fiber s) ≤ 1 :=
    fun s hs => (hdim s hs).le
  have hπq' : π ≫ sS = (q ≫ i) ≫ projToSpecCoeff k N := by rw [hπq, Category.assoc]
  -- the `𝒪(1)`-degree is constant
  have hcd : ∀ s : S, cycleDegree i (cX s) =
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
        (fibreCyc sS π (q ≫ i) (projToSpecCoeff k N) s) := fun s => by
    simp only [cycleDegree, cX]
    rw [pushforward_fiberCycle i sS π q s]
  have hdeg : ∀ s : S, IsClosed ({s} : Set S) → cycleDegree i (cX s) = cycleDegree i (cX s₀) :=
    fun s hs => by
      rw [hcd, hcd]
      exact degree_fibreCyc_eq sS (projToSpecCoeff k N) π (q ≫ i) hπq' hdimle _ hs hs₀
  have hnn : ∀ s, 0 ≤ cX s := fun s => by
    refine finsum_nonneg fun C => smul_nonneg (Int.natCast_nonneg _) ?_
    unfold Mori.cyclePushforwardOfPoint
    split_ifs
    · exact Finsupp.single_nonneg.mpr (Int.natCast_nonneg _)
    · exact le_rfl
  -- positivity of the degree
  have hpos : 0 < cycleDegree i (cX s₀) := by
    set Wp := Mori.OneCycle.pushforward ℤ sX (projToSpecCoeff k N) i (cX s₀)
    have hWnn : ∀ C, 0 ≤ Wp C := pushforward_nonneg i _ (hnn s₀)
    have hW0 : Wp ≠ 0 := fun h0 => hne₀ (pushforward_injective i _ (by rw [map_zero]; exact h0))
    obtain ⟨C, hC⟩ : Wp.support.Nonempty := Finsupp.support_nonempty_iff.mpr hW0
    simp only [cycleDegree]
    erw [Mori.OneCycle.degree_apply, Finsupp.sum]
    refine Finset.sum_pos' (fun C' _ => mul_nonneg (hWnn C')
      (MMP.Chow.DeterminantCurveForm.curveDeg_pos C').le) ⟨C, hC, mul_pos
        (lt_of_le_of_ne (hWnn C) (Ne.symm (Finsupp.mem_support_iff.mp hC)))
        (MMP.Chow.DeterminantCurveForm.curveDeg_pos C)⟩
  set e' := (cycleDegree i (cX s₀)).toNat
  have he' : (e' : ℤ) = cycleDegree i (cX s₀) := Int.toNat_of_nonneg hpos.le
  have he'pos : 0 < e' := by omega
  -- the Chow morphism
  obtain ⟨ψ, hψ, -⟩ := MMP.Chow.exists_chowFormMorphism sS sX hS
    (isProjectiveMorphism_comp_projToSpecCoeff k i) i
    (MMP.isProjectiveMorphism_of_isClosedImmersion i) rfl π q hπq hdim e' he'pos
    (fun s hs => by
      beta_reduce
      rw [← pushforward_fiberCycle i sS π q s]
      change cycleDegree i (cX s) = e'
      rw [hdeg s hs, he'])
  obtain ⟨hψS, hψC⟩ := (hψ ψ).mpr rfl
  haveI := finite_bidegree N e'
  haveI : LocallyOfFiniteType (ψ ≫ Intersection.ProjSpace.toSpec k _) := hψS ▸ inferInstance
  haveI : LocallyOfFiniteType ψ :=
    locallyOfFiniteType_of_comp ψ (Intersection.ProjSpace.toSpec k _)
  haveI : JacobsonSpace (FormSpace k N e') :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k _)
  refine ⟨e', he'pos, ψ, cX, hψS, fun s hs => ⟨Scheme.Hom.closePoints_subset_preimage_closedPoints ψ hs,
    hnn s, by rw [hdeg s hs, he'], ?_⟩, hsupp, fun s s' hs hs' => ?_⟩
  · intro G hG
    have := hψC s hs G
    beta_reduce at this
    rw [← pushforward_fiberCycle i sS π q s] at this
    exact this hG
  · haveI : IsSeparated sX := inferInstance
    haveI : LocallyOfFiniteType sX := inferInstance
    rw [cartierDegree_mapRange_cast, cartierDegree_mapRange_cast,
      degree_fibreCyc_eq sS sX π q hπq hdimle _ hs hs']

end FlatFamily

section Bases

/-- The closed point `ker e` of `Spec A` is closed. -/
private theorem isClosed_kPt {A : Type u} [CommRing A] [Algebra k A] (e : A →ₐ[k] k) :
    IsClosed ({kPt e} : Set (Spec (.of A))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    (RingHom.ker_isMaximal_of_surjective _ fun c => ⟨algebraMap k A c, by simp⟩)

private theorem specMap_kPt {A A' : Type u} [CommRing A] [CommRing A'] [Algebra k A]
    [Algebra k A'] (f : A →ₐ[k] A') (e : A' →ₐ[k] k) :
    Spec.map (CommRingCat.ofHom (f : A →+* A')) (kPt e) = kPt (e.comp f) := by
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  rfl

/-- Every closed point of `Spec A`, `A` of finite type over `k`, is `kPt e` for a `k`-point `e`. -/
private theorem exists_eq_kPt {A : Type u} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (x : Spec (.of A)) (hx : IsClosed ({x} : Set (Spec (.of A)))) : ∃ e : A →ₐ[k] k, x = kPt e := by
  haveI : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hx
  letI : Field (A ⧸ x.asIdeal) := Ideal.Quotient.field _
  haveI : Module.Finite k (A ⧸ x.asIdeal) := finite_of_finite_type_of_isJacobsonRing k _
  haveI : Algebra.IsIntegral k (A ⧸ x.asIdeal) := Algebra.IsIntegral.of_finite k _
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ x.asIdeal)
  refine ⟨((AlgEquiv.ofBijective (Algebra.ofId k _) hbij).symm.toAlgHom).comp
    (Ideal.Quotient.mkₐ k _), PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change a ∈ x.asIdeal ↔ (AlgEquiv.ofBijective (Algebra.ofId k _) hbij).symm
    (Ideal.Quotient.mk _ a) = 0
  rw [EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end Bases

section SubCycles

/-- A nonzero divisor of the Chow product of a 1-cycle `W` is associated to the Chow product of an
effective cycle supported in the support of `W`. -/
private theorem exists_associated_chowProd_of_dvd
    {G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    {n : Mori.ProperCurve (projToSpecCoeff k N) → ℕ} (hG : ∀ C, IsIncidenceForm C (G C) (n C))
    (W : Mori.OneCycle ℤ (projToSpecCoeff k N)) {P : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    (hP : P ≠ 0) (hdvd : P ∣ chowProd G W) :
    ∃ W' : Mori.OneCycle ℤ (projToSpecCoeff k N), (∀ C, 0 ≤ W' C) ∧ W'.support ⊆ W.support ∧
      Associated P (chowProd G W') := by
  classical
  letI := UniqueFactorizationMonoid.normalizationMonoid
    (α := MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
  set s := UniqueFactorizationMonoid.normalizedFactors P
  have hfactor : ∀ Q ∈ s, ∃ C ∈ W.support, Associated Q (G C) := by
    intro Q hQ
    have hQirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
    have hQp : Prime Q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hQirr
    have hQd : Q ∣ chowProd G W :=
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ).trans hdvd
    obtain ⟨C, hC, hQC⟩ := (Prime.dvd_finset_prod_iff hQp _).mp hQd
    exact ⟨C, hC, hQirr.associated_of_dvd (hG C).1 (hQp.dvd_of_dvd_pow hQC)⟩
  let cnt : Mori.ProperCurve (projToSpecCoeff k N) → ℕ := fun C => s.count (normalize (G C))
  let W' : Mori.OneCycle ℤ (projToSpecCoeff k N) := ∑ C ∈ W.support, (cnt C : ℤ) • Finsupp.single C 1
  have hW' : ∀ C, W' C = if C ∈ W.support then (cnt C : ℤ) else 0 := fun C => by
    simp [W', Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hsupp : W'.support ⊆ W.support := fun C hC => by
    by_contra h
    exact Finsupp.mem_support_iff.mp hC (by rw [hW', if_neg h])
  refine ⟨W', fun C => by rw [hW']; split_ifs <;> simp, hsupp, ?_⟩
  have hprod : chowProd G W' = ∏ C ∈ W.support, G C ^ cnt C := by
    unfold chowProd
    rw [Finset.prod_subset hsupp (fun C _ hC => by
      rw [Finsupp.notMem_support_iff.mp hC, Int.toNat_zero, pow_zero])]
    exact Finset.prod_congr rfl fun C hC => by rw [hW', if_pos hC, Int.toNat_natCast]
  have h1 : Associated s.prod P := UniqueFactorizationMonoid.prod_normalizedFactors hP
  have hinj : Set.InjOn (fun C => normalize (G C)) W.support := fun C _ C' _ h =>
    eq_of_associated_incidenceForm (hG C).2.1 (hG C').2.1
      (normalize_eq_normalize_iff_associated.mp h)
  have h2 : s.prod = ∏ C ∈ W.support, normalize (G C) ^ cnt C := by
    rw [Finset.prod_multiset_count, ← Finset.prod_image (f := fun q => q ^ s.count q) hinj]
    refine Finset.prod_subset ?_ ?_
    · intro q hq
      obtain ⟨C, hC, hPC⟩ := hfactor q (Multiset.mem_toFinset.mp hq)
      refine Finset.mem_image.mpr ⟨C, hC, ?_⟩
      rw [← UniqueFactorizationMonoid.normalize_normalized_factor q (Multiset.mem_toFinset.mp hq)]
      exact normalize_eq_normalize_iff_associated.mpr hPC.symm
    · intro q _ hq
      rw [Multiset.count_eq_zero_of_notMem (fun h => hq (Multiset.mem_toFinset.mpr h)), pow_zero]
  rw [hprod]
  refine h1.symm.trans ?_
  rw [h2]
  exact Associated.prod _ _ _ fun C _ => (normalize_associated (G C)).pow_pow

/-- A closed point whose form divides the Chow product of an effective cycle on `X` is the Chow
point of an effective cycle on `X`. -/
private theorem exists_isChowPointOf_of_dvd (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d' : ℕ) [Fintype (ULift.{u} (Bidegree N d'))] (b : FormSpace k N d')
    (c : ULift.{u} (Bidegree N d') → k) {β₀ : ULift.{u} (Bidegree N d')} (hc0 : c β₀ ≠ 0)
    (hc : ∀ β β', c β' • (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N d')) k) -
      c β • MvPolynomial.X β' ∈ b.asHomogeneousIdeal)
    {G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    {n : Mori.ProperCurve (projToSpecCoeff k N) → ℕ} (hG : ∀ C, IsIncidenceForm C (G C) (n C))
    (Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N))
    (hdvd : formPoly (fun β : ULift.{u} (Bidegree N d') => β.down.1) c ∣
      chowProd G (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z)) :
    ∃ Z', IsChowPointOf i d' Z' b := by
  classical
  have hm : Function.Injective (fun β : ULift.{u} (Bidegree N d') => β.down.1) :=
    fun β β' h => ULift.ext (Subtype.ext h)
  have hP0 : formPoly (fun β : ULift.{u} (Bidegree N d') => β.down.1) c ≠ 0 := fun h0 => by
    have := coeff_formPoly hm c β₀
    rw [h0, MvPolynomial.coeff_zero] at this
    exact hc0 this.symm
  obtain ⟨W', hW'nn, hW'supp, hassoc⟩ := exists_associated_chowProd_of_dvd hG _ hP0 hdvd
  have hpre : ∀ C ∈ W'.support, ∃ C₀ : Mori.ProperCurve (i ≫ projToSpecCoeff k N),
      ProperCurve.mapClosedImmersion i _ C₀ = C := by
    intro C hC
    have := hW'supp hC
    rw [pushforward_eq_mapDomain] at this
    obtain ⟨C₀, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support this)
    exact ⟨C₀, rfl⟩
  choose pre hpre using hpre
  let Z' : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N) :=
    ∑ C ∈ W'.support.attach, W' C.1 • Finsupp.single (pre C.1 C.2) 1
  have hZW : Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z' = W' := by
    rw [pushforward_eq_mapDomain, Finsupp.mapDomain_finset_sum]
    conv_rhs => rw [← Finsupp.sum_single W', Finsupp.sum, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single, hpre, Finsupp.smul_single, smul_eq_mul,
      mul_one]
  have hZ'nn : 0 ≤ Z' := Finset.sum_nonneg fun C _ =>
    smul_nonneg (hW'nn C.1) (Finsupp.single_nonneg.mpr zero_le_one)
  exact ⟨Z', isChowPointOf_of_associated i d' b c hc hG hZ'nn (by rw [hZW]; exact hassoc)⟩

end SubCycles

section PointHelpers

private theorem kPt_injective {A : Type u} [CommRing A] [Algebra k A] {e e' : A →ₐ[k] k}
    (h : kPt e = kPt e') : e = e' := by
  ext a
  have hker : RingHom.ker e = RingHom.ker e' := congrArg PrimeSpectrum.asIdeal h
  have h0 : a - algebraMap k A (e a) ∈ RingHom.ker e' := by
    rw [← hker, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at h0
  exact h0.symm

/-- The relations of the values of the coefficients hold at the image of a `k`-point under
`formsToProjSpace`. -/
private theorem formsToProjSpace_relations {A : Type u} [CommRing A] [Algebra k A] {ι : Type u}
    (c : ι → A) (hc : Ideal.span (Set.range c) = ⊤) (e : A →ₐ[k] k) (β β' : ι) :
    e (c β') • (MvPolynomial.X β : MvPolynomial ι k) - e (c β) • MvPolynomial.X β' ∈
      ((MMP.Chow.formsToProjSpace (k := k) c hc).base (kPt e)).asHomogeneousIdeal := by
  rw [MMP.Chow.mem_asHomogeneousIdeal_formsToProjSpace_iff c hc (kPt e)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mp (relation_mem_one β β' _ _))]
  change _ ∈ RingHom.ker e
  rw [RingHom.mem_ker, MvPolynomial.aeval_def]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, map_sub, map_mul, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- The image of a polynomial with coefficients `∑_β monomial (m β) (a β)` under a `k`-point. -/
private theorem map_sum_monomial {A : Type*} [CommRing A] [Algebra k A] {ι σ : Type*} [Fintype ι]
    (m : ι → σ →₀ ℕ) (a : ι → A) (e : A →ₐ[k] k) :
    MvPolynomial.map e.toRingHom (∑ β, MvPolynomial.monomial (m β) (a β)) =
      formPoly m (fun β => e (a β)) := by
  simp only [formPoly, map_sum, MvPolynomial.map_monomial, MvPolynomial.C_mul_monomial, mul_one]
  rfl

private theorem coeff_sum_monomial {A : Type*} [CommRing A] {ι σ : Type*} [Fintype ι]
    {m : ι → σ →₀ ℕ} (hm : Function.Injective m) (a : ι → A) (β : ι) :
    (∑ β', MvPolynomial.monomial (m β') (a β')).coeff (m β) = a β := by
  classical
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single β]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro b _ hb; rw [MvPolynomial.coeff_monomial, if_neg (fun h => hb (hm h))]
  · simp

/-- The zeros of a Chow product are the pairs of hyperplanes meeting a curve of the support. -/
private theorem eval_chowProd_eq_zero_iff
    {G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    {n : Mori.ProperCurve (projToSpecCoeff k N) → ℕ} (hG : ∀ C, IsIncidenceForm C (G C) (n C))
    (W : Mori.OneCycle ℤ (projToSpecCoeff k N)) (hW : ∀ C, 0 ≤ W C)
    (x : Fin (N + 1) ⊕ Fin (N + 1) → k) :
    MvPolynomial.eval x (chowProd G W) = 0 ↔
      ∃ C ∈ W.support, IncidenceLocus C (x ∘ Sum.inl) (x ∘ Sum.inr) := by
  unfold chowProd
  rw [map_prod, Finset.prod_eq_zero_iff]
  refine exists_congr fun C => and_congr_right fun hC => ?_
  have hpos : (W C).toNat ≠ 0 := by
    have := Finsupp.mem_support_iff.mp hC
    have := hW C
    omega
  rw [map_pow, pow_eq_zero_iff hpos, ← (hG C).2.1, Sum.elim_comp_inl_inr]

private theorem eval_eq_zero_iff_of_associated {σ : Type*} {P Q : MvPolynomial σ k}
    (h : Associated P Q) (x : σ → k) :
    MvPolynomial.eval x P = 0 ↔ MvPolynomial.eval x Q = 0 := by
  obtain ⟨u, rfl⟩ := h
  rw [map_mul, mul_eq_zero, or_iff_left ((u.isUnit.map (MvPolynomial.eval x)).ne_zero)]

end PointHelpers

section FactorDegree

open MvPolynomial in
private theorem chowProd_nsmul
    (G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
    (W : Mori.OneCycle ℤ (projToSpecCoeff k N)) (hW : ∀ C, 0 ≤ W C) (s : ℕ) :
    chowProd G (s • W) = chowProd G W ^ s := by
  have := chowProd_sum (Finset.univ : Finset Unit) G (fun _ => W) (fun _ _ C => hW C) (fun _ => s)
  simpa using this

private theorem cartierDegree_cast_nsmul {sX' : X ⟶ Spec (.of k)} (E : X.CartierDivisor)
    (Z : Mori.OneCycle ℤ sX') (s : ℕ) :
    Mori.OneCycle.cartierDegree E (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (s • Z)) =
      s * Mori.OneCycle.cartierDegree E (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero Z) := by
  rw [cartierDegree_mapRange_cast, cartierDegree_mapRange_cast, map_nsmul, nsmul_eq_mul]
  push_cast
  ring

private theorem support_pushforward_subset (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] {Z Z' : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)}
    (h : Z.support ⊆ Z'.support) :
    (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z).support ⊆
      (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z').support := by
  classical
  rw [pushforward_eq_mapDomain, pushforward_eq_mapDomain,
    Finsupp.mapDomain_support_of_injective (ProperCurve.mapClosedImmersion_injective i _),
    Finsupp.mapDomain_support_of_injective (ProperCurve.mapClosedImmersion_injective i _)]
  exact Finset.image_subset_image h

/-- **The degree on the Chow cycle of a prime factor is locally constant.** Let `P` be a
bihomogeneous polynomial over a Dedekind `k`-algebra `B` (an open of a normal curve `Γ`), prime over
the local ring at `𝔪`, with a unit coefficient, whose values at the `k`-points divide Chow products.
Near the point `𝔪`, the Cartier degree of the Chow cycle of the forms `P(e)` is constant. -/
private theorem exists_isOpen_cartierDegree_factor
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N)) [IsClosedImmersion i] (E : X.CartierDivisor)
    {Γ : Scheme.{u}} (sΓ : Γ ⟶ Spec (.of k)) (hΓ : Mori.IsNormalVariety k sΓ)
    {B : Type u} [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (jB : Spec (.of B) ⟶ Γ) [IsOpenImmersion jB]
    (𝔪 : Ideal B) [𝔪.IsPrime] (h𝔪 : 𝔪 ≠ ⊥) (d' : ℕ) (hd' : 0 < d')
    (P : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) B)
    (hP : Prime (MvPolynomial.map (algebraMap B (Localization.AtPrime 𝔪)) P))
    (hPdeg : ∀ e ∈ P.support, (∑ j, e (Sum.inl j)) = d' ∧ (∑ j, e (Sum.inr j)) = d')
    {e₀ : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ} (hPu : IsUnit (P.coeff e₀))
    {G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    {n : Mori.ProperCurve (projToSpecCoeff k N) → ℕ} (hG : ∀ C, IsIncidenceForm C (G C) (n C))
    (hdvd : ∀ e : B →ₐ[k] k, ∃ Z : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N),
      MvPolynomial.map e.toRingHom P ∣
        chowProd G (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i Z)) :
    ∃ (hc : Ideal.span (Set.range fun β : ULift.{u} (Bidegree N d') => P.coeff β.down.1) = ⊤)
      (O : Set (Spec (.of B))) (D : ℝ), IsOpen O ∧ (⟨𝔪, ‹_›⟩ : Spec (.of B)) ∈ O ∧
      ∀ e : B →ₐ[k] k, kPt e ∈ O → ∀ Z' : Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N),
        IsChowPointOf i d' Z' ((MMP.Chow.formsToProjSpace (k := k)
          (fun β : ULift.{u} (Bidegree N d') => P.coeff β.down.1) hc).base (kPt e)) →
        Mori.OneCycle.cartierDegree E (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero Z') =
          D := by
  classical
  haveI := finite_bidegree N d'
  haveI := Fintype.ofFinite (ULift.{u} (Bidegree N d'))
  haveI : IsNormal Γ := hΓ.2
  have h𝔪max : 𝔪.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔪 ‹_›
  set m' : ULift.{u} (Bidegree N d') → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ := fun β => β.down.1
  have hm' : Function.Injective m' := fun β β' h => ULift.ext (Subtype.ext h)
  set c : ULift.{u} (Bidegree N d') → B := fun β => P.coeff β.down.1
  have he₀mem : e₀ ∈ P.support := MvPolynomial.mem_support_iff.mpr hPu.ne_zero
  set β₁ : ULift.{u} (Bidegree N d') := ⟨⟨e₀, hPdeg e₀ he₀mem⟩⟩
  have hc : Ideal.span (Set.range c) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨β₁, rfl⟩) hPu
  refine ⟨hc, ?_⟩
  set φj := MMP.Chow.formsToProjSpace (k := k) c hc
  have hφj : φj ≫ ProjSpace.toSpec k _ = Spec.map (CommRingCat.ofHom (algebraMap k B)) :=
    MMP.Chow.formsToProjSpace_toSpec c hc
  have hPe : ∀ e : B →ₐ[k] k, MvPolynomial.map e.toRingHom P = formPoly m' (fun β => e (c β)) := by
    intro e
    have hsupp : ∀ e' ∈ (MvPolynomial.map e.toRingHom P).support,
        (∑ j, e' (Sum.inl j)) = d' ∧ (∑ j, e' (Sum.inr j)) = d' := fun e' he' =>
      hPdeg e' (MvPolynomial.support_map_subset _ _ he')
    rw [← formPoly_coeff (d := d') hsupp]
    congr 1
  have hce : ∀ e : B →ₐ[k] k, e (c β₁) ≠ 0 := fun e => (hPu.map e).ne_zero
  obtain ⟨W', hW'⟩ := exists_closeds_chowPoints i d' hd'
  -- the base `Spec B`
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  haveI : JacobsonSpace (Spec (.of B)) :=
    LocallyOfFiniteType.jacobsonSpace (Spec.map (CommRingCat.ofHom (algebraMap k B)))
  haveI : JacobsonSpace (FormSpace k N d') :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k _)
  haveI : LocallyOfFiniteType (φj ≫ ProjSpace.toSpec k _) := hφj ▸ inferInstance
  haveI : LocallyOfFiniteType φj := locallyOfFiniteType_of_comp φj (ProjSpace.toSpec k _)
  have hφjc : ∀ e : B →ₐ[k] k, IsClosed ({φj (kPt e)} : Set (FormSpace k N d')) := fun e =>
    Scheme.Hom.closePoints_subset_preimage_closedPoints φj (isClosed_kPt e)
  have hφjW : ∀ s, φj s ∈ W' := by
    have hcl : ∀ s : Spec (.of B), IsClosed ({s} : Set (Spec (.of B))) → φj s ∈ W' := by
      intro s hs
      obtain ⟨e, rfl⟩ := exists_eq_kPt (k := k) s hs
      obtain ⟨Z, hZ⟩ := hdvd e
      rw [hPe] at hZ
      exact (hW' _ (hφjc e)).mpr (exists_isChowPointOf_of_dvd i d' _ _ (hce e)
        (formsToProjSpace_relations c hc e) hG Z hZ)
    have hpre : IsClosed (φj ⁻¹' (W' : Set (FormSpace k N d'))) := W'.isClosed.preimage φj.continuous
    have h2 : closure (closedPoints (Spec (.of B))) ⊆ φj ⁻¹' (W' : Set (FormSpace k N d')) :=
      hpre.closure_subset_iff.mpr fun s hs => hcl s hs
    rw [closure_closedPoints] at h2
    exact fun s => h2 (Set.mem_univ s)
  have hchj : ∀ e : B →ₐ[k] k, IsChowPointOf i d' (chowCycle i d' (φj (kPt e))) (φj (kPt e)) :=
    fun e => isChowPointOf_chowCycle ((hW' _ (hφjc e)).mp (hφjW _))
  -- `Spec B` is a normal variety with a Dedekind cover
  haveI : IsNormal (Spec (.of B)) := isNormal_of_isOpenImmersion jB
  have hS : Mori.IsNormalVariety k (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    ⟨⟨⟩, inferInstance⟩
  have hDed : ∀ s : Spec (.of B), ∃ U : (Spec (.of B)).Opens, s ∈ (U : Set (Spec (.of B))) ∧
      IsAffineOpen U ∧ IsDedekindDomain Γ(Spec (.of B), U) := fun s =>
    ⟨⊤, trivial, isAffineOpen_top _,
      isDedekindDomain_of_ringEquiv (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv⟩
  set x₀ : Spec (.of B) := ⟨𝔪, ‹_›⟩
  have hx₀ : IsClosed ({x₀} : Set (Spec (.of B))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr h𝔪max
  obtain ⟨e', he', ψ, cX, hψS, hψc, hcXsupp, hcXdeg⟩ :=
    exists_chowFamily i d' hd' W' hW' (Spec (.of B)) _ hS hDed φj hφj hφjW hx₀ E
  haveI := finite_bidegree N e'
  haveI := Fintype.ofFinite (ULift.{u} (Bidegree N e'))
  obtain ⟨g, hg, β₂, b, hb1, hbrel⟩ := exists_coords (k := k) (A := B) ψ hψS 𝔪
  haveI := isDomain_away 𝔪 hg
  haveI : Algebra.FiniteType k (Localization.Away g) := finiteType_away g
  have hg0 : g ≠ 0 := fun h0 => hg (h0 ▸ 𝔪.zero_mem)
  haveI : IsDedekindDomain (Localization.Away g) := IsLocalization.isDedekindDomain B
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg0) (Localization.Away g)
  haveI h𝔪₂ := isPrime_map_away 𝔪 hg
  set 𝔪₂ := Ideal.map (algebraMap B (Localization.Away g)) 𝔪
  have h𝔪₂ne : 𝔪₂ ≠ ⊥ := fun h0 => h𝔪 (by
    rw [← comap_map_away 𝔪 hg]
    change Ideal.comap _ 𝔪₂ = ⊥
    rw [h0, Ideal.comap_bot_of_injective _ (IsLocalization.injective (Localization.Away g)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg0))])
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (Localization.Away g) h𝔪₂ne (Localization.AtPrime 𝔪₂)
  set m'' : ULift.{u} (Bidegree N e') → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ := fun β => β.down.1
  have hm'' : Function.Injective m'' := fun β β' h => ULift.ext (Subtype.ext h)
  set Ψ : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (Localization.Away g) :=
    ∑ β, MvPolynomial.monomial (m'' β) (b β)
  have hΨcoeff : Ψ.coeff (m'' β₂) = 1 := by rw [coeff_sum_monomial hm'', hb1]
  set P₂ := MvPolynomial.map (algebraMap B (Localization.Away g)) P
  have hP₂ := prime_map_atPrime_away 𝔪 hg P hP
  have hΨne : MvPolynomial.map (algebraMap (Localization.Away g) (Localization.AtPrime 𝔪₂)) Ψ ≠ 0 :=
    fun h0 => by
      have := congrArg (fun p : MvPolynomial _ _ => p.coeff (m'' β₂)) h0
      rw [MvPolynomial.coeff_map, hΨcoeff, map_one, MvPolynomial.coeff_zero] at this
      exact one_ne_zero this
  -- the relations of the coordinates of `ψ` at the `k`-points of `B_g`
  have hrelψ : ∀ e₂ : Localization.Away g →ₐ[k] k, ∀ β β',
      e₂ (b β') • (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N e')) k) -
        e₂ (b β) • MvPolynomial.X β' ∈
          (ψ (kPt (e₂.comp (IsScalarTower.toAlgHom k B (Localization.Away g))))).asHomogeneousIdeal :=
    fun e₂ β β' => by
      have := hbrel e₂ β β'
      rwa [show Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) (kPt e₂) =
        kPt (e₂.comp (IsScalarTower.toAlgHom k B (Localization.Away g))) from
          specMap_kPt (IsScalarTower.toAlgHom k B (Localization.Away g)) e₂] at this
  -- zeros of `Ψ` are zeros of `P`
  have hpt : ∀ (e₂ : Localization.Away g →ₐ[k] k) (x : Fin (N + 1) ⊕ Fin (N + 1) → k),
      MvPolynomial.eval x (MvPolynomial.map e₂.toRingHom Ψ) = 0 →
        MvPolynomial.eval x (MvPolynomial.map e₂.toRingHom P₂) = 0 := by
    intro e₂ x hx
    set e := e₂.comp (IsScalarTower.toAlgHom k B (Localization.Away g))
    have hψch := (hψc (kPt e) (isClosed_kPt e)).2
    have hass1 := associated_of_isChowPointOf i e' (ψ (kPt e)) (fun β => e₂ (b β)) (β₀ := β₂)
      (by rw [hb1, map_one]; exact one_ne_zero) (hrelψ e₂) hG hψch
    rw [map_sum_monomial, eval_eq_zero_iff_of_associated hass1,
      eval_chowProd_eq_zero_iff hG _ (pushforward_nonneg i _ hψch.1)] at hx
    obtain ⟨C, hC, hI⟩ := hx
    have hass2 := associated_of_isChowPointOf i d' (φj (kPt e)) (fun β => e (c β)) (hce e)
      (formsToProjSpace_relations c hc e) hG (hchj e)
    rw [show MvPolynomial.map e₂.toRingHom P₂ = MvPolynomial.map e.toRingHom P from by
      rw [MvPolynomial.map_map]; rfl, hPe, eval_eq_zero_iff_of_associated hass2,
      eval_chowProd_eq_zero_iff hG _ (pushforward_nonneg i _ (hchj e).1)]
    exact ⟨C, support_pushforward_subset i (fun C' hC' => hcXsupp _ (isClosed_kPt e) C' hC') hC,
      hI⟩
  obtain ⟨h₃, hh₃, s, c₃, hc₃u, hΨeq⟩ := exists_eq_C_mul_pow (k := k) 𝔪₂ P₂ Ψ hP₂ hΨne hpt
  haveI := isDomain_away 𝔪₂ hh₃
  haveI : Algebra.FiniteType k (Localization.Away h₃) := finiteType_away h₃
  -- the exponent is positive
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · exfalso
      rw [hs0, pow_zero, mul_one] at hΨeq
      have := congrArg (fun p : MvPolynomial _ _ => p.coeff (m'' β₂)) hΨeq
      rw [MvPolynomial.coeff_map, hΨcoeff, map_one, MvPolynomial.coeff_C, if_neg] at this
      · exact one_ne_zero this
      · intro h0
        have h1 := β₂.down.2.1
        change (∑ j, (m'' β₂) (Sum.inl j)) = e' at h1
        rw [← h0] at h1
        simp at h1
        omega
    · exact hs0
  -- the open set
  let j₃ : Spec (.of (Localization.Away h₃)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g) (Localization.Away h₃))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  haveI : IsOpenImmersion j₃ := inferInstance
  have hj₃ : ∀ e₃ : Localization.Away h₃ →ₐ[k] k, j₃ (kPt e₃) =
      kPt ((e₃.comp (IsScalarTower.toAlgHom k (Localization.Away g) (Localization.Away h₃))).comp
        (IsScalarTower.toAlgHom k B (Localization.Away g))) := fun e₃ => by
    rw [Scheme.Hom.comp_apply]
    erw [specMap_kPt (IsScalarTower.toAlgHom k (Localization.Away g) (Localization.Away h₃)) e₃,
      specMap_kPt (IsScalarTower.toAlgHom k B (Localization.Away g))]
  refine ⟨Set.range j₃, Mori.OneCycle.cartierDegree E
      (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (cX x₀)) / s,
    j₃.isOpenEmbedding.isOpen_range, ?_, ?_⟩
  · haveI h𝔪₃ := isPrime_map_away 𝔪₂ hh₃
    refine ⟨⟨Ideal.map (algebraMap (Localization.Away g) (Localization.Away h₃)) 𝔪₂, h𝔪₃⟩, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap B (Localization.Away g))
      (Ideal.comap (algebraMap (Localization.Away g) (Localization.Away h₃))
        (Ideal.map (algebraMap (Localization.Away g) (Localization.Away h₃)) 𝔪₂)) = 𝔪
    rw [comap_map_away 𝔪₂ hh₃, comap_map_away 𝔪 hg]
  · intro e he Z' hZ'
    obtain ⟨y, hy⟩ := he
    have hyc : IsClosed ({y} : Set (Spec (.of (Localization.Away h₃)))) := by
      have hyeq : ({y} : Set (Spec (.of (Localization.Away h₃)))) = j₃ ⁻¹' {kPt e} := by
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_preimage, ← hy]
        exact ⟨fun h => h ▸ rfl, fun h => j₃.isOpenEmbedding.injective h⟩
      rw [hyeq]
      exact (isClosed_kPt e).preimage j₃.continuous
    obtain ⟨e₃, rfl⟩ := exists_eq_kPt (k := k) y hyc
    set e₂ := e₃.comp (IsScalarTower.toAlgHom k (Localization.Away g) (Localization.Away h₃))
    have he_eq : e = e₂.comp (IsScalarTower.toAlgHom k B (Localization.Away g)) := by
      apply kPt_injective
      rw [← hy, hj₃]
    subst he_eq
    have hEq := congrArg (MvPolynomial.map e₃.toRingHom) hΨeq
    rw [MvPolynomial.map_map, map_mul, MvPolynomial.map_C, map_pow, MvPolynomial.map_map,
      MvPolynomial.map_map] at hEq
    have h1 : MvPolynomial.map (e₃.toRingHom.comp
        (algebraMap (Localization.Away g) (Localization.Away h₃))) Ψ =
          formPoly m'' (fun β => e₂ (b β)) := by
      rw [← map_sum_monomial m'' b e₂]
      rfl
    have h2 : MvPolynomial.map ((e₃.toRingHom.comp
        (algebraMap (Localization.Away g) (Localization.Away h₃))).comp
          (algebraMap B (Localization.Away g))) P =
          formPoly m' (fun β => (e₂.comp (IsScalarTower.toAlgHom k B (Localization.Away g))) (c β)) := by
      rw [← hPe]
      rfl
    rw [h1, h2] at hEq
    have hassZ := associated_of_isChowPointOf i d' _ _ (hce _) (formsToProjSpace_relations c hc _)
      hG hZ'
    have hcu : IsUnit (MvPolynomial.C (e₃.toRingHom c₃) :
        MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k) := (hc₃u.map _).map _
    have hass : Associated (formPoly m'' (fun β => e₂ (b β)))
        (chowProd G (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i (s • Z'))) := by
      rw [hEq, map_nsmul, chowProd_nsmul G _ (pushforward_nonneg i _ hZ'.1)]
      exact (associated_unit_mul_left _ _ hcu).trans hassZ.pow_pow
    have hZs : IsChowPointOf i e' (s • Z')
        (ψ (kPt (e₂.comp (IsScalarTower.toAlgHom k B (Localization.Away g))))) :=
      isChowPointOf_of_associated i e' _ _ (hrelψ e₂) hG (nsmul_nonneg hZ'.1 s) hass
    have hcXeq := eq_of_isChowPointOf_of_isChowPointOf i e' he' (hψc _ (isClosed_kPt _)).1
      (hψc _ (isClosed_kPt _)).2 hZs
    have hdeg := hcXdeg _ x₀
      (isClosed_kPt (k := k) (e₂.comp (IsScalarTower.toAlgHom k B (Localization.Away g)))) hx₀
    rw [hcXeq, cartierDegree_cast_nsmul] at hdeg
    rw [eq_div_iff (by exact_mod_cast hspos.ne'), ← hdeg]
    ring

end FactorDegree

section PrimeAway

/-- Primality over `B_𝔪` of a polynomial over `B_h`, `h ∉ 𝔪`, is primality over the localization of
`B_h` at `𝔪 B_h`. -/
private theorem prime_map_atPrime_of_awayToAtPrime {B : Type*} [CommRing B] [IsDomain B]
    (𝔪 : Ideal B) [𝔪.IsPrime] {σ : Type*} {h : B} (hh : h ∉ 𝔪)
    (P : MvPolynomial σ (Localization.Away h))
    (hP : Prime (MvPolynomial.map (awayToAtPrime 𝔪 hh) P)) :
    haveI := isPrime_map_away 𝔪 hh
    Prime (MvPolynomial.map (algebraMap (Localization.Away h)
      (Localization.AtPrime (Ideal.map (algebraMap B (Localization.Away h)) 𝔪))) P) := by
  haveI := isPrime_map_away 𝔪 hh
  set 𝔪' := Ideal.map (algebraMap B (Localization.Away h)) 𝔪
  haveI : IsLocalization 𝔪.primeCompl (Localization.AtPrime 𝔪') := by
    have h1 := IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers h) 𝔪'
    have hc : (Ideal.comap (algebraMap B (Localization (Submonoid.powers h))) 𝔪').primeCompl =
        𝔪.primeCompl := by
      ext x
      rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff]
      exact not_congr (by rw [comap_map_away 𝔪 hh])
    unfold IsLocalization.AtPrime at h1
    rwa [hc] at h1
  let e : Localization.AtPrime 𝔪 ≃ₐ[B] Localization.AtPrime 𝔪' :=
    IsLocalization.algEquiv 𝔪.primeCompl _ _
  have he : (e : Localization.AtPrime 𝔪 →+* Localization.AtPrime 𝔪').comp
      (awayToAtPrime 𝔪 hh) = algebraMap (Localization.Away h) (Localization.AtPrime 𝔪') := by
    refine IsLocalization.ringHom_ext (Submonoid.powers h) (RingHom.ext fun b => ?_)
    simp only [RingHom.comp_apply, awayToAtPrime_algebraMap]
    simp [IsScalarTower.algebraMap_apply B (Localization.Away h) (Localization.AtPrime 𝔪')]
  rw [← he, ← MvPolynomial.map_map]
  exact (MulEquiv.prime_iff (MvPolynomial.mapAlgEquiv σ e).toMulEquiv).mpr hP

end PrimeAway

section FactorAssembly

/-- A divisor, after an injective change of coefficients, of a nonzero weighted homogeneous
polynomial has all its monomials of one weight. -/
private theorem exists_weight_eq_of_map_dvd {S R σ : Type*} [CommRing S] [CommRing R] [IsDomain R]
    {f : S →+* R} (hf : Function.Injective f) {w : σ → ℕ} {F : MvPolynomial σ R} {n : ℕ}
    (hF : MvPolynomial.IsWeightedHomogeneous w F n) (hF0 : F ≠ 0) {Q : MvPolynomial σ S}
    (hQ : MvPolynomial.map f Q ∣ F) : ∃ D, ∀ e ∈ Q.support, Finsupp.weight w e = D :=
  ⟨_, fun e he => isWeightedHomogeneous_of_dvd hF hF0 hQ
    (MvPolynomial.mem_support_iff.mp (by rwa [MvPolynomial.support_map_of_injective Q hf]))⟩

/-- A nonzero divisor of a Chow product is bihomogeneous of an equal bidegree `(D, D)`. -/
private theorem exists_bidegree_of_dvd_chowProd
    {G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    {n : Mori.ProperCurve (projToSpecCoeff k N) → ℕ} (hG : ∀ C, IsIncidenceForm C (G C) (n C))
    (W : Mori.OneCycle ℤ (projToSpecCoeff k N)) {Q : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    (hQ : Q ≠ 0) (hdvd : Q ∣ chowProd G W) :
    ∃ D, ∀ e ∈ Q.support, (∑ j, e (Sum.inl j)) = D ∧ (∑ j, e (Sum.inr j)) = D := by
  obtain ⟨W', -, -, u, hu⟩ := exists_associated_chowProd_of_dvd hG W hQ hdvd
  obtain ⟨r, hr, hur⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have h1 : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0))
      (chowProd G W') (∑ C ∈ W'.support, (W' C).toNat • n C) :=
    MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun C _ => (hG C).2.2.2.1.pow _
  have h2 : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 0) (fun _ => 1))
      (chowProd G W') (∑ C ∈ W'.support, (W' C).toNat • n C) :=
    MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun C _ => (hG C).2.2.2.2.pow _
  refine ⟨∑ C ∈ W'.support, (W' C).toNat • n C, fun e he => ?_⟩
  have hce : (chowProd G W').coeff e ≠ 0 := by
    rw [← hu, hur, mul_comm, MvPolynomial.coeff_C_mul]
    exact mul_ne_zero hr.ne_zero (MvPolynomial.mem_support_iff.mp he)
  exact ⟨(weight_sumElim_one_zero e).symm.trans (h1 hce),
    (weight_sumElim_zero_one e).symm.trans (h2 hce)⟩

/-- A polynomial of bidegree `(0, 0)` with a unit coefficient is a unit. -/
private theorem isUnit_of_bidegree_zero {S : Type*} [CommRing S] [Nontrivial S]
    {P : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) S}
    (hP : ∀ e ∈ P.support, (∑ j, e (Sum.inl j)) = 0 ∧ (∑ j, e (Sum.inr j)) = 0)
    {e₀ : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ} (hu : IsUnit (P.coeff e₀)) : IsUnit P := by
  have h0 : ∀ e ∈ P.support, e = 0 := fun e he => by
    obtain ⟨h1, h2⟩ := hP e he
    ext x
    rcases x with x | x
    · exact Nat.eq_zero_of_le_zero
        (h1 ▸ Finset.single_le_sum (fun j _ => Nat.zero_le (e (Sum.inl j))) (Finset.mem_univ x))
    · exact Nat.eq_zero_of_le_zero
        (h2 ▸ Finset.single_le_sum (fun j _ => Nat.zero_le (e (Sum.inr j))) (Finset.mem_univ x))
  obtain rfl : e₀ = 0 := h0 e₀ (MvPolynomial.mem_support_iff.mpr hu.ne_zero)
  have : P = MvPolynomial.C (P.coeff 0) := by
    ext e
    rw [MvPolynomial.coeff_C]
    split_ifs with h
    · rw [h]
    · by_contra hne
      exact h (h0 e (MvPolynomial.mem_support_iff.mpr hne)).symm
  rw [this]
  exact hu.map MvPolynomial.C

/-- **The Chow point of a sum.** If the form of a closed point is a nonzero constant times
`∏ⱼ Qⱼ^{nⱼ}`, with `Qⱼ` associated to the Chow product of an effective cycle `Zⱼ`, the point is
the Chow point of `∑ⱼ nⱼ Zⱼ`. -/
private theorem isChowPointOf_sum (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) [Fintype (ULift.{u} (Bidegree N d))] (b : FormSpace k N d)
    (c : ULift.{u} (Bidegree N d) → k)
    (hc : ∀ β β', c β' • (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N d)) k) -
      c β • MvPolynomial.X β' ∈ b.asHomogeneousIdeal)
    {G : Mori.ProperCurve (projToSpecCoeff k N) → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k}
    {n : Mori.ProperCurve (projToSpecCoeff k N) → ℕ} (hG : ∀ C, IsIncidenceForm C (G C) (n C))
    {r : ℕ} (Z : Fin r → Mori.OneCycle ℤ (i ≫ projToSpecCoeff k N)) (hZ : ∀ j, 0 ≤ Z j)
    (Q : Fin r → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) k)
    (hQ : ∀ j, Associated (Q j) (chowProd G (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N)
      i (Z j))))
    (nexp : Fin r → ℕ) {u : k} (hu : u ≠ 0)
    (hform : formPoly (fun β : ULift.{u} (Bidegree N d) => β.down.1) c =
      MvPolynomial.C u * ∏ j, Q j ^ nexp j) :
    IsChowPointOf i d (∑ j, nexp j • Z j) b := by
  refine isChowPointOf_of_associated i d b c hc hG
    (Finset.sum_nonneg fun j _ => nsmul_nonneg (hZ j) _) ?_
  rw [hform, map_sum]
  simp only [map_nsmul]
  rw [chowProd_sum _ G _ (fun j _ C => pushforward_nonneg i _ (hZ j) C) nexp]
  exact (associated_unit_mul_left _ _ ((IsUnit.mk0 u hu).map MvPolynomial.C)).trans
    (Associated.prod _ _ _ fun j _ => (hQ j).pow_pow)

/-- Cartier degrees of integral cycles are additive. -/
private theorem cartierDegree_cast_sum {sX' : X ⟶ Spec (.of k)} (E : X.CartierDivisor) {r : ℕ}
    (Z : Fin r → Mori.OneCycle ℤ sX') (nexp : Fin r → ℕ) :
    Mori.OneCycle.cartierDegree E
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (∑ j, nexp j • Z j)) =
      ∑ j, (nexp j : ℝ) * Mori.OneCycle.cartierDegree E
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (Z j)) := by
  simp only [cartierDegree_mapRange_cast, map_sum, map_nsmul, nsmul_eq_mul]
  push_cast
  rfl

end FactorAssembly

/-- Polynomials in any number of variables over a discrete valuation ring form a unique
factorization monoid. -/
private theorem uniqueFactorizationMonoid_mvPolynomial_dvr (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (σ : Type*) : UniqueFactorizationMonoid (MvPolynomial σ R) :=
  inferInstance

/-- **The factors of a bihomogeneous form are bihomogeneous of positive degree.** Let `F` be a
form of bidegree `(d, d)` over a domain `B` with a coefficient `1`, factored over `B_h` as a unit
times `∏ⱼ Pⱼ^{nⱼ}` with each `Pⱼ` prime over the local ring at `𝔪` and with a unit coefficient. If
the image of each `Pⱼ` under some `ψ : B_h ⟶ K` is bihomogeneous whenever it is nonzero, then
each `Pⱼ` is bihomogeneous of some bidegree `(Dⱼ, Dⱼ)` with `Dⱼ > 0`. -/
private theorem exists_bidegree_factors {B : Type*} [CommRing B] [IsDomain B] (𝔪 : Ideal B)
    [𝔪.IsPrime] [IsDomain (Localization.AtPrime 𝔪)] {K : Type*} [CommRing K] [Nontrivial K]
    {F : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) B} {d : ℕ}
    {e' : (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ} (hF1 : F.coeff e' = 1)
    (hFdeg : ∀ e ∈ F.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d)
    {h : B} (hh : h ∉ 𝔪) {r : ℕ}
    (P : Fin r → MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (Localization.Away h))
    (nexp : Fin r → ℕ) (c : Localization.Away h)
    (hfac : MvPolynomial.map (algebraMap B _) F = MvPolynomial.C c * ∏ j, P j ^ nexp j)
    (hPj : ∀ j, 0 < nexp j ∧ Prime (MvPolynomial.map (awayToAtPrime 𝔪 hh) (P j)) ∧
      ∃ e, IsUnit ((P j).coeff e))
    (ψ : Localization.Away h →+* K)
    (hψ : ∀ j, MvPolynomial.map ψ (P j) ≠ 0 → ∃ D, ∀ e ∈ (MvPolynomial.map ψ (P j)).support,
      (∑ l, e (Sum.inl l)) = D ∧ (∑ l, e (Sum.inr l)) = D) :
    ∃ D1 : Fin r → ℕ,
      (∀ j, ∀ e ∈ (P j).support, (∑ l, e (Sum.inl l)) = D1 j ∧ (∑ l, e (Sum.inr l)) = D1 j) ∧
        ∀ j, 0 < D1 j := by
  classical
  haveI := isDomain_away 𝔪 hh
  have hFR0 : MvPolynomial.map (algebraMap B (Localization.AtPrime 𝔪)) F ≠ 0 :=
    fun h0 => by
      have := congrArg (fun p : MvPolynomial _ _ => p.coeff e') h0
      rw [MvPolynomial.coeff_map, hF1, map_one, MvPolynomial.coeff_zero] at this
      exact one_ne_zero this
  have hFR1 : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 1) (fun _ => 0))
      (MvPolynomial.map (algebraMap B (Localization.AtPrime 𝔪)) F) d := by
    intro e he
    rw [weight_sumElim_one_zero]
    exact (hFdeg e (MvPolynomial.support_map_subset _ _ (MvPolynomial.mem_support_iff.mpr he))).1
  have hFR2 : MvPolynomial.IsWeightedHomogeneous (Sum.elim (fun _ => 0) (fun _ => 1))
      (MvPolynomial.map (algebraMap B (Localization.AtPrime 𝔪)) F) d := by
    intro e he
    rw [weight_sumElim_zero_one]
    exact (hFdeg e (MvPolynomial.support_map_subset _ _ (MvPolynomial.mem_support_iff.mpr he))).2
  have hdvdR : ∀ j, MvPolynomial.map (awayToAtPrime 𝔪 hh) (P j) ∣
      MvPolynomial.map (algebraMap B (Localization.AtPrime 𝔪)) F := by
    intro j
    have := congrArg (MvPolynomial.map (awayToAtPrime 𝔪 hh)) hfac
    rw [MvPolynomial.map_map, awayToAtPrime_comp_algebraMap, map_mul, map_prod] at this
    simp only [map_pow] at this
    rw [this]
    exact Dvd.dvd.mul_left ((dvd_pow_self _ (hPj j).1.ne').trans
      (Finset.dvd_prod_of_mem (fun j => (MvPolynomial.map (awayToAtPrime 𝔪 hh) (P j)) ^ nexp j)
        (Finset.mem_univ j))) _
  choose D1 hD1 using fun j => exists_weight_eq_of_map_dvd (awayToAtPrime_injective 𝔪 hh) hFR1
    hFR0 (hdvdR j)
  choose D2 hD2 using fun j => exists_weight_eq_of_map_dvd (awayToAtPrime_injective 𝔪 hh) hFR2
    hFR0 (hdvdR j)
  choose e₀ he₀ using fun j => (hPj j).2.2
  have he₀mem : ∀ j, e₀ j ∈ (P j).support := fun j =>
    MvPolynomial.mem_support_iff.mpr (he₀ j).ne_zero
  have hPdeg : ∀ j, ∀ e ∈ (P j).support, (∑ l, e (Sum.inl l)) = D1 j ∧
      (∑ l, e (Sum.inr l)) = D1 j := by
    intro j
    have hQ0 : MvPolynomial.map ψ (P j) ≠ 0 := fun h0 => by
      have := congrArg (fun p : MvPolynomial _ _ => p.coeff (e₀ j)) h0
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
      exact ((he₀ j).map ψ).ne_zero this
    obtain ⟨D, hD⟩ := hψ j hQ0
    have hmem : e₀ j ∈ (MvPolynomial.map ψ (P j)).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
      exact ((he₀ j).map ψ).ne_zero
    have h12 : D1 j = D2 j := by
      rw [← hD1 j _ (he₀mem j), ← hD2 j _ (he₀mem j), weight_sumElim_one_zero,
        weight_sumElim_zero_one, (hD _ hmem).1, (hD _ hmem).2]
    intro e he
    refine ⟨(weight_sumElim_one_zero e).symm.trans (hD1 j e he), ?_⟩
    rw [h12]
    exact (weight_sumElim_zero_one e).symm.trans (hD2 j e he)
  refine ⟨D1, hPdeg, fun j => ?_⟩
  by_contra h0
  have h0' : D1 j = 0 := by omega
  refine (hPj j).2.1.not_unit ((isUnit_of_bidegree_zero (fun e he => ?_) (he₀ j)).map _)
  rw [← h0']
  exact hPdeg j e he

/-- **Local constancy of Cartier degrees along a normal curve.** Near a closed point `t₀` of a
normal curve `Γ ⟶ W`, the form `F = ∑ a_b x^b` of `φ` factors over the local ring at `t₀` as a
unit times `∏ⱼ Pⱼ^{nⱼ}` with `Pⱼ` prime; the Chow cycle of `φ t` is `∑ⱼ nⱼ Z⁽ʲ⁾_t`, and the degree
of `E` on each `Z⁽ʲ⁾_t` is constant near `t₀` (`exists_isOpen_cartierDegree_factor`). -/
private theorem exists_isOpen_cartierDegree_eq
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (E : X.CartierDivisor) (Γ : Scheme.{u}) (sΓ : Γ ⟶ Spec (.of k))
    (hΓ : Mori.IsNormalVariety k sΓ) (hΓ1 : topologicalKrullDim Γ = 1)
    (φ : Γ ⟶ FormSpace k N d) (hφ : φ ≫ ProjSpace.toSpec k _ = sΓ) (hφW : ∀ t, φ t ∈ W)
    {t₀ : Γ} (ht₀ : IsClosed ({t₀} : Set Γ)) :
    ∃ O : Set Γ, IsOpen O ∧ t₀ ∈ O ∧ ∀ t ∈ O, IsClosed ({t} : Set Γ) →
      Mori.OneCycle.cartierDegree E
          (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d (φ t))) =
        Mori.OneCycle.cartierDegree E
          (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d (φ t₀))) := by
  classical
  haveI := hΓ.1
  haveI : IsNormal Γ := hΓ.2
  haveI := finite_bidegree N d
  haveI := Fintype.ofFinite (ULift.{u} (Bidegree N d))
  haveI : JacobsonSpace Γ := LocallyOfFiniteType.jacobsonSpace sΓ
  choose G n hG using fun C : Mori.ProperCurve (projToSpecCoeff k N) => exists_incidenceForm C
  have hG' : ∀ C, IsIncidenceForm C (G C) (n C) := hG
  set m : ULift.{u} (Bidegree N d) → (Fin (N + 1) ⊕ Fin (N + 1)) →₀ ℕ := fun β => β.down.1
  have hm : Function.Injective m := fun β β' h => ULift.ext (Subtype.ext h)
  haveI : LocallyOfFiniteType (φ ≫ Intersection.ProjSpace.toSpec k _) := hφ ▸ inferInstance
  haveI : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ (Intersection.ProjSpace.toSpec k _)
  haveI : JacobsonSpace (FormSpace k N d) :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k _)
  have hφc : ∀ t : Γ, IsClosed ({t} : Set Γ) → IsClosed ({φ t} : Set (FormSpace k N d)) :=
    fun t ht => Scheme.Hom.closePoints_subset_preimage_closedPoints φ ht
  have hch : ∀ t : Γ, IsClosed ({t} : Set Γ) → IsChowPointOf i d (chowCycle i d (φ t)) (φ t) :=
    fun t ht => isChowPointOf_chowCycle ((hW _ (hφc t ht)).mp (hφW t))
  -- an affine chart `Spec A ⟶ Γ` around `t₀`
  obtain ⟨_, ⟨V, hV, rfl⟩, ht₀V, -⟩ :=
    Γ.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t₀) isOpen_univ
  haveI : Nonempty V := ⟨⟨t₀, ht₀V⟩⟩
  haveI : IsOpenImmersion hV.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hV
  haveI : LocallyOfFiniteType (hV.fromSpec ≫ sΓ) := inferInstance
  letI : Algebra k Γ(Γ, V) := (Spec.preimage (hV.fromSpec ≫ sΓ)).hom.toAlgebra
  have hjA : hV.fromSpec ≫ sΓ = Spec.map (CommRingCat.ofHom (algebraMap k Γ(Γ, V))) :=
    (Spec.map_preimage _).symm
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k Γ(Γ, V)))) :=
    hjA ▸ inferInstance
  haveI : Algebra.FiniteType k Γ(Γ, V) :=
    RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp ‹_›)
  haveI : IsNormal (Spec Γ(Γ, V)) := isNormal_of_isOpenImmersion hV.fromSpec
  haveI : IsIntegrallyClosed Γ(Γ, V) := isIntegrallyClosed_of_isNormal_spec Γ(Γ, V)
  haveI : IsNoetherianRing Γ(Γ, V) := Algebra.FiniteType.isNoetherianRing k _
  haveI : Ring.DimensionLEOne Γ(Γ, V) := dimensionLEOne_of_ringKrullDim_le (by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hV.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hΓ1.le)
  haveI : IsDedekindDomain Γ(Γ, V) := isDedekindDomain_of_isIntegrallyClosed
  obtain ⟨x₀, hx₀⟩ : t₀ ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact ht₀V
  have hx₀c : IsClosed ({x₀} : Set (Spec Γ(Γ, V))) := by
    rw [← hV.fromSpec.isOpenEmbedding.injective.preimage_image {x₀}, Set.image_singleton, hx₀]
    exact ht₀.preimage hV.fromSpec.continuous
  have h𝔭₀max : x₀.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hx₀c
  have h𝔭₀ne : x₀.asIdeal ≠ ⊥ := by
    intro h0
    have hall : ∀ y : Spec Γ(Γ, V), y = x₀ := fun y => by
      have := h𝔭₀max.eq_of_le y.isPrime.ne_top (by rw [h0]; exact bot_le)
      exact PrimeSpectrum.ext this.symm
    have hV1 : (V : Set Γ) = {t₀} := by
      rw [← hV.range_fromSpec]
      ext t
      constructor
      · rintro ⟨y, rfl⟩
        rw [hall y, hx₀]
        rfl
      · intro h
        rw [Set.mem_singleton_iff.mp h]
        exact ⟨x₀, hx₀⟩
    have hopen : IsOpen ({t₀} : Set Γ) := hV1 ▸ V.isOpen
    have huniv : (Set.univ : Set Γ) = {t₀} := by
      have hd := hopen.dense ⟨t₀, rfl⟩
      rw [← hd.closure_eq, ht₀.closure_eq]
    have h1 : ((1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim Γ := by rw [hΓ1]; norm_num
    obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h1
    have hT : ∀ T : TopologicalSpace.IrreducibleCloseds Γ, (T : Set Γ) = {t₀} := fun T =>
      (Set.Nonempty.subset_singleton_iff T.isIrreducible.nonempty).mp
        (fun x _ => huniv ▸ Set.mem_univ x)
    have hlt := p.strictMono (show (⟨0, by omega⟩ : Fin (p.length + 1)) < ⟨1, by omega⟩ by
      simp [Fin.lt_def])
    exact hlt.ne (TopologicalSpace.IrreducibleCloseds.ext (by rw [hT, hT]))
  -- coordinates of `φ` near `t₀`
  obtain ⟨g, hg, β₀, a, ha1, hrel⟩ := exists_coords (k := k) (A := Γ(Γ, V)) (hV.fromSpec ≫ φ)
    (by rw [Category.assoc, hφ, hjA]) x₀.asIdeal
  haveI := isDomain_away x₀.asIdeal hg
  haveI : Algebra.FiniteType k (Localization.Away g) := finiteType_away g
  have hg0 : g ≠ 0 := fun h0 => hg (h0 ▸ x₀.asIdeal.zero_mem)
  haveI : IsDedekindDomain (Localization.Away g) := IsLocalization.isDedekindDomain Γ(Γ, V)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg0) (Localization.Away g)
  haveI h𝔪 := isPrime_map_away x₀.asIdeal hg
  set 𝔪 := Ideal.map (algebraMap Γ(Γ, V) (Localization.Away g)) x₀.asIdeal
  have h𝔪ne : 𝔪 ≠ ⊥ := fun h0 => h𝔭₀ne (by
    rw [← comap_map_away x₀.asIdeal hg]
    change Ideal.comap _ 𝔪 = ⊥
    rw [h0, Ideal.comap_bot_of_injective _ (IsLocalization.injective (Localization.Away g)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg0))])
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Localization.Away g) h𝔪ne
    (Localization.AtPrime 𝔪)
  haveI := uniqueFactorizationMonoid_mvPolynomial_dvr (Localization.AtPrime 𝔪)
    (Fin (N + 1) ⊕ Fin (N + 1))
  -- the relations of the coordinates
  have hrelφ : ∀ e : (Localization.Away g) →ₐ[k] k, ∀ β β',
      e (a β') • (MvPolynomial.X β : MvPolynomial (ULift.{u} (Bidegree N d)) k) -
        e (a β) • MvPolynomial.X β' ∈
          (φ (hV.fromSpec (kPt (e.comp (IsScalarTower.toAlgHom k Γ(Γ, V) (Localization.Away g)))))).asHomogeneousIdeal :=
    fun e β β' => by
      have := hrel e β β'
      rwa [Scheme.Hom.comp_apply, show Spec.map (CommRingCat.ofHom (algebraMap Γ(Γ, V) (Localization.Away g))) (kPt e) =
        kPt (e.comp (IsScalarTower.toAlgHom k Γ(Γ, V) (Localization.Away g))) from
          specMap_kPt (IsScalarTower.toAlgHom k Γ(Γ, V) (Localization.Away g)) e] at this
  -- the form over `(Localization.Away g)`
  set F : MvPolynomial (Fin (N + 1) ⊕ Fin (N + 1)) (Localization.Away g) := ∑ β, MvPolynomial.monomial (m β) (a β)
  have hF1 : F.coeff (m β₀) = 1 := by rw [coeff_sum_monomial hm, ha1]
  have hFdeg : ∀ e ∈ F.support, (∑ j, e (Sum.inl j)) = d ∧ (∑ j, e (Sum.inr j)) = d := by
    intro e he
    by_contra hne
    apply MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact hne β.down.2
  -- the point of `Γ` of a `k`-point of `(Localization.Away g)`, and its Chow cycle
  set ptΓ : ((Localization.Away g) →ₐ[k] k) → Γ := fun e => hV.fromSpec (kPt (e.comp (IsScalarTower.toAlgHom k Γ(Γ, V) (Localization.Away g))))
  have hptc : ∀ e, IsClosed ({ptΓ e} : Set Γ) := fun e =>
    Scheme.Hom.closePoints_subset_preimage_closedPoints hV.fromSpec (isClosed_kPt _)
  have hassF : ∀ e : (Localization.Away g) →ₐ[k] k, Associated (MvPolynomial.map e.toRingHom F)
      (chowProd G (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i
        (chowCycle i d (φ (ptΓ e))))) := by
    intro e
    rw [map_sum_monomial]
    exact associated_of_isChowPointOf i d (φ (ptΓ e)) (fun β => e (a β)) (β₀ := β₀)
      (by rw [ha1, map_one]; exact one_ne_zero) (hrelφ e) hG' (hch _ (hptc e))
  -- factorization over the local ring
  obtain ⟨h, hh, r, P, nexp, c, hcu, hfac, hPj⟩ := exists_away_factorization 𝔪 F hF1
  haveI := isDomain_away 𝔪 hh
  haveI : Algebra.FiniteType k (Localization.Away h) := finiteType_away h
  have hh0 : h ≠ 0 := fun h0 => hh (h0 ▸ 𝔪.zero_mem)
  haveI : IsDedekindDomain (Localization.Away h) := IsLocalization.isDedekindDomain (Localization.Away g)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hh0) (Localization.Away h)
  haveI h𝔪' := isPrime_map_away 𝔪 hh
  set 𝔪' := Ideal.map (algebraMap (Localization.Away g) (Localization.Away h)) 𝔪
  have h𝔪'ne : 𝔪' ≠ ⊥ := fun h0 => h𝔪ne (by
    rw [← comap_map_away 𝔪 hh]
    change Ideal.comap _ 𝔪' = ⊥
    rw [h0, Ideal.comap_bot_of_injective _ (IsLocalization.injective (Localization.Away h)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hh0))])
  let jB' : Spec (.of (Localization.Away h)) ⟶ Γ := Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g) (Localization.Away h))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Γ, V) (Localization.Away g))) ≫ hV.fromSpec
  haveI : IsOpenImmersion jB' := inferInstance
  set ptB : ((Localization.Away h) →ₐ[k] k) → ((Localization.Away g) →ₐ[k] k) := fun e => e.comp (IsScalarTower.toAlgHom k (Localization.Away g) (Localization.Away h))
  have hjB' : ∀ e : (Localization.Away h) →ₐ[k] k, jB' (kPt e) = ptΓ (ptB e) := fun e => by
    simp only [jB', Scheme.Hom.comp_apply, ptΓ, ptB]
    erw [specMap_kPt (IsScalarTower.toAlgHom k (Localization.Away g) (Localization.Away h)) e,
      specMap_kPt (IsScalarTower.toAlgHom k Γ(Γ, V) (Localization.Away g))]
  -- the factorization at `k`-points
  have hFe : ∀ e : (Localization.Away h) →ₐ[k] k, MvPolynomial.map (ptB e).toRingHom F =
      MvPolynomial.C (e c) * ∏ j, (MvPolynomial.map e.toRingHom (P j)) ^ nexp j := by
    intro e
    have := congrArg (MvPolynomial.map e.toRingHom) hfac
    rw [MvPolynomial.map_map, map_mul, MvPolynomial.map_C, map_prod] at this
    simp only [map_pow] at this
    exact this
  have hdvdP : ∀ (j : Fin r) (e : (Localization.Away h) →ₐ[k] k), MvPolynomial.map e.toRingHom (P j) ∣
      chowProd G (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i
        (chowCycle i d (φ (ptΓ (ptB e))))) := by
    intro j e
    refine Dvd.dvd.trans ?_ (hassF (ptB e)).dvd
    rw [hFe]
    exact Dvd.dvd.mul_left ((dvd_pow_self _ (hPj j).1.ne').trans
      (Finset.dvd_prod_of_mem (fun j => (MvPolynomial.map e.toRingHom (P j)) ^ nexp j)
        (Finset.mem_univ j))) _
  -- the bidegrees of the factors
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Localization.Away h)
  obtain ⟨e₁, -⟩ := exists_eq_kPt (k := k)
    (⟨M, hM.isPrime⟩ : Spec (.of (Localization.Away h)))
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hM)
  obtain ⟨D1, hPdeg, hpos⟩ := exists_bidegree_factors 𝔪 hF1 hFdeg hh P nexp c hfac hPj
    e₁.toRingHom fun j hQ0 => exists_bidegree_of_dvd_chowProd hG' _ hQ0 (hdvdP j e₁)
  choose e₀ he₀ using fun j => (hPj j).2.2
  have he₀mem : ∀ j, e₀ j ∈ (P j).support := fun j =>
    MvPolynomial.mem_support_iff.mpr (he₀ j).ne_zero
  -- the factorwise constancy
  choose hc O D hO hO₀ hOD using fun j => exists_isOpen_cartierDegree_factor i E sΓ hΓ jB' 𝔪'
    h𝔪'ne (D1 j) (hpos j) (P j) (prime_map_atPrime_of_awayToAtPrime 𝔪 hh (P j) (hPj j).2.1)
    (hPdeg j) (he₀ j) hG' (fun e => ⟨_, hdvdP j e⟩)
  have hfin : ∀ j, Fintype (ULift.{u} (Bidegree N (D1 j))) := fun j =>
    haveI := finite_bidegree N (D1 j)
    Fintype.ofFinite _
  -- the degree at a `k`-point of `Spec B'` lying in every `O j`
  have hval : ∀ e : Localization.Away h →ₐ[k] k, (∀ j, kPt e ∈ O j) →
      Mori.OneCycle.cartierDegree E
          (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d (φ (jB' (kPt e))))) =
        ∑ j, (nexp j : ℝ) * D j := by
    intro e he
    have hPe : ∀ j, MvPolynomial.map e.toRingHom (P j) =
        @formPoly k _ _ _ (hfin j) (fun β : ULift.{u} (Bidegree N (D1 j)) => β.down.1)
          (fun β => e ((P j).coeff β.down.1)) := by
      intro j
      letI := hfin j
      have hsupp : ∀ e' ∈ (MvPolynomial.map e.toRingHom (P j)).support,
          (∑ l, e' (Sum.inl l)) = D1 j ∧ (∑ l, e' (Sum.inr l)) = D1 j := fun e' he' =>
        hPdeg j e' (MvPolynomial.support_map_subset _ _ he')
      rw [← formPoly_coeff (d := D1 j) hsupp]
      congr 1
    have hZ : ∀ j, ∃ Z', IsChowPointOf i (D1 j) Z' ((MMP.Chow.formsToProjSpace (k := k)
        (fun β : ULift.{u} (Bidegree N (D1 j)) => (P j).coeff β.down.1) (hc j)).base (kPt e)) :=
      fun j => by
        letI := hfin j
        refine exists_isChowPointOf_of_dvd i (D1 j) _ (fun β => e ((P j).coeff β.down.1))
          (β₀ := ⟨⟨e₀ j, hPdeg j _ (he₀mem j)⟩⟩) ((he₀ j).map e).ne_zero
          (formsToProjSpace_relations _ (hc j) e) hG' (chowCycle i d (φ (ptΓ (ptB e)))) ?_
        rw [← hPe j]
        exact hdvdP j e
    choose Z hZ using hZ
    have hass : ∀ j, Associated (MvPolynomial.map e.toRingHom (P j))
        (chowProd G (Mori.OneCycle.pushforward ℤ _ (projToSpecCoeff k N) i (Z j))) := fun j => by
      letI := hfin j
      rw [hPe j]
      exact associated_of_isChowPointOf i (D1 j) _ _ (β₀ := ⟨⟨e₀ j, hPdeg j _ (he₀mem j)⟩⟩)
        ((he₀ j).map e).ne_zero (formsToProjSpace_relations _ (hc j) e) hG' (hZ j)
    have htc : IsClosed ({jB' (kPt e)} : Set Γ) :=
      Scheme.Hom.closePoints_subset_preimage_closedPoints jB' (isClosed_kPt e)
    have hsum : IsChowPointOf i d (∑ j, nexp j • Z j) (φ (jB' (kPt e))) := by
      refine isChowPointOf_sum i d _ (fun β => (ptB e) (a β)) ?_ hG' Z (fun j => (hZ j).1)
        _ hass nexp (hcu.map e).ne_zero ?_
      · rw [hjB' e]
        exact hrelφ (ptB e)
      · rw [← map_sum_monomial, hFe e]
    rw [eq_of_isChowPointOf_of_isChowPointOf i d hd (hφc _ htc) (hch _ htc) hsum,
      cartierDegree_cast_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hOD j e (he j) (Z j) (hZ j)]
  -- the neighbourhood
  have hy₀ : jB' ⟨𝔪', h𝔪'⟩ = t₀ := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g) (Localization.Away h)))
        ⟨𝔪', h𝔪'⟩ = (⟨𝔪, h𝔪⟩ : Spec (.of (Localization.Away g))) :=
      PrimeSpectrum.ext (comap_map_away 𝔪 hh)
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap Γ(Γ, V) (Localization.Away g)))
        ⟨𝔪, h𝔪⟩ = x₀ :=
      PrimeSpectrum.ext (comap_map_away x₀.asIdeal hg)
    simp only [jB']
    erw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1, h2, hx₀]
  have hgood : ∀ t ∈ Set.range jB' ∩ ⋂ j, jB' '' O j, IsClosed ({t} : Set Γ) →
      Mori.OneCycle.cartierDegree E
          (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d (φ t))) =
        ∑ j, (nexp j : ℝ) * D j := by
    rintro t ⟨⟨y, rfl⟩, hyO⟩ htc
    have hyc : IsClosed ({y} : Set (Spec (.of (Localization.Away h)))) := by
      rw [← jB'.isOpenEmbedding.injective.preimage_image {y}, Set.image_singleton]
      exact htc.preimage jB'.continuous
    obtain ⟨e, rfl⟩ := exists_eq_kPt (k := k) y hyc
    refine hval e fun j => ?_
    obtain ⟨y', hy', hy'e⟩ := Set.mem_iInter.mp hyO j
    rwa [← jB'.isOpenEmbedding.injective hy'e]
  refine ⟨Set.range jB' ∩ ⋂ j, jB' '' O j,
    jB'.isOpenEmbedding.isOpen_range.inter (isOpen_iInter_of_finite fun j =>
      jB'.isOpenEmbedding.isOpenMap _ (hO j)), ?_, fun t ht htc => ?_⟩
  · exact ⟨⟨_, hy₀⟩, Set.mem_iInter.mpr fun j => ⟨_, hO₀ j, hy₀⟩⟩
  · have ht₀O : t₀ ∈ Set.range jB' ∩ ⋂ j, jB' '' O j :=
      ⟨⟨_, hy₀⟩, Set.mem_iInter.mpr fun j => ⟨_, hO₀ j, hy₀⟩⟩
    rw [hgood t ht htc, hgood t₀ ht₀O ht₀]

/-- **Cartier degrees are constant along a normal curve in the Chow-form locus.** For a morphism
`φ` from a normal curve `Γ` to the Chow-form locus, the degree of a Cartier divisor `E` on the
cycles `chowCycle (φ t)` is the same at all closed points `t`: the support incidence over `Γ` is
flat over the Dedekind curve, and the degree is a difference of Euler characteristics of its
fibres. -/
private theorem cartierDegree_chowCycle_eq_of_curve
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (E : X.CartierDivisor) (Γ : Scheme.{u}) (sΓ : Γ ⟶ Spec (.of k))
    (hΓ : Mori.IsNormalVariety k sΓ) (hΓ1 : topologicalKrullDim Γ = 1)
    (φ : Γ ⟶ FormSpace k N d) (hφ : φ ≫ ProjSpace.toSpec k _ = sΓ) (hφW : ∀ t, φ t ∈ W)
    {t t' : Γ} (ht : IsClosed ({t} : Set Γ)) (ht' : IsClosed ({t'} : Set Γ)) :
    Mori.OneCycle.cartierDegree E
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d (φ t))) =
      Mori.OneCycle.cartierDegree E
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d (φ t'))) := by
  haveI := hΓ.1
  haveI : IsIntegral Γ := hΓ.1.toIsIntegral
  haveI : JacobsonSpace Γ := LocallyOfFiniteType.jacobsonSpace sΓ
  obtain ⟨O, hO, htO, hOt⟩ := exists_isOpen_cartierDegree_eq i d hd W hW E Γ sΓ hΓ hΓ1 φ hφ hφW ht
  obtain ⟨O', hO', htO', hOt'⟩ :=
    exists_isOpen_cartierDegree_eq i d hd W hW E Γ sΓ hΓ hΓ1 φ hφ hφW ht'
  obtain ⟨s, hs⟩ := nonempty_preirreducible_inter hO hO' ⟨t, htO⟩ ⟨t', htO'⟩
  have hcl := subset_closure_inter_closedPoints isClosed_univ (hO.inter hO') ⟨Set.mem_univ s, hs⟩
  obtain ⟨u, ⟨-, huO, huO'⟩, huc⟩ := closure_nonempty_iff.mp ⟨s, hcl⟩
  exact (hOt u huO huc).symm.trans (hOt' u huO' huc)

/-- **Cartier degrees are constant on an irreducible closed subset of the Chow-form locus**: two
of its closed points lie on a curve, whose normalization maps to the locus. -/
private theorem cartierDegree_chowCycle_eq_of_isIrreducible
    (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (E : X.CartierDivisor) {T : Set (FormSpace k N d)} (hTc : IsClosed T) (hTi : IsIrreducible T)
    (hTW : T ⊆ W) {q q' : FormSpace k N d} (hq : IsClosed ({q} : Set _))
    (hq' : IsClosed ({q'} : Set _)) (hqT : q ∈ T) (hq'T : q' ∈ T) :
    Mori.OneCycle.cartierDegree E
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d q)) =
      Mori.OneCycle.cartierDegree E
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d q')) := by
  classical
  by_cases hqq : q = q'
  · rw [hqq]
  haveI := finite_bidegree N d
  -- the reduced subscheme on `T`, a variety
  let J := Scheme.IdealSheafData.vanishingIdeal (⟨T, hTc⟩ : TopologicalSpace.Closeds _)
  haveI : IsReduced J.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hrange : Set.range J.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hemb := J.subschemeι.isClosedEmbedding
  haveI : IrreducibleSpace J.subscheme := by
    have h1 : IsIrreducible (Set.univ : Set (Set.range J.subschemeι)) :=
      (Subtype.irreducibleSpace (hrange ▸ hTi : IsIrreducible (Set.range J.subschemeι))
        ).isIrreducible_univ
    have h2 := h1.image hemb.isEmbedding.toHomeomorph.symm
      hemb.isEmbedding.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ, Homeomorph.range_coe] at h2
    exact (irreducibleSpace_def _).mpr h2
  haveI : IsIntegral J.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : Mori.IsVariety k (J.subschemeι ≫ Intersection.ProjSpace.toSpec k _) := {}
  obtain ⟨c, hcq⟩ : q ∈ Set.range J.subschemeι := hrange ▸ hqT
  obtain ⟨c', hcq'⟩ : q' ∈ Set.range J.subschemeι := hrange ▸ hq'T
  have hcc : IsClosed ({c} : Set J.subscheme) := hemb.isClosed_iff_image_isClosed.mpr
    (by rw [Set.image_singleton, hcq]; exact hq)
  have hcc' : IsClosed ({c'} : Set J.subscheme) := hemb.isClosed_iff_image_isClosed.mpr
    (by rw [Set.image_singleton, hcq']; exact hq')
  have hdim : 0 < topologicalKrullDim J.subscheme := by
    obtain ⟨η, hη⟩ := QuasiSober.sober (IrreducibleSpace.isIrreducible_univ J.subscheme)
      isClosed_univ
    have hne : η ≠ c := by
      rintro rfl
      have h1 : (Set.univ : Set J.subscheme) = {η} := by rw [← hη.def, hcc.closure_eq]
      have h2 : c' ∈ ({η} : Set J.subscheme) := h1 ▸ Set.mem_univ c'
      rw [Set.mem_singleton_iff] at h2
      exact hqq (by rw [← hcq, ← hcq', h2])
    have h1 := one_le_topologicalKrullDim_of_specializes (hη.specializes (Set.mem_univ c)) hne
    exact lt_of_lt_of_le (by exact_mod_cast zero_lt_one) h1
  -- a curve through `c` and `c'`, and its normalization
  obtain ⟨C, iC, hiC, hCcurve, ⟨e, he⟩, ⟨e', he'⟩, -⟩ :=
    MMP.exists_isClosedImmersion_isCurve_and_isProper_of_isClosed_singleton
      (J.subschemeι ≫ Intersection.ProjSpace.toSpec k _) hdim hcc hcc'
  haveI := hiC
  haveI : IsCurve k (iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _) := hCcurve
  have hC := finite_irreducibleComponents_of_locallyOfFiniteType k
    (iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _)
  set ν := normalizationOverField k (iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _)
  have hΓc : IsCurve k (ν ≫ iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _) :=
    AlgebraicGeometry.isCurve_normalizationOverField_comp k _
  haveI : LocallyOfFiniteType (ν ≫ iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _) :=
    hΓc.toIsVariety.toLocallyOfFiniteType
  haveI : IsNormal (normalizationSchemeOverField k
      (iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _)) :=
    Scheme.isNormal_normalizationScheme C hC
  have hΓ : Mori.IsNormalVariety k (ν ≫ iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _) :=
    ⟨hΓc.toIsVariety, inferInstance⟩
  haveI : Surjective ν := Scheme.surjective_normalization C hC
  haveI : JacobsonSpace (normalizationSchemeOverField k
      (iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _)) :=
    LocallyOfFiniteType.jacobsonSpace (ν ≫ iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _)
  set g := ν ≫ iC ≫ J.subschemeι
  -- closed points of the normalization over `q` and `q'`
  have hlift : ∀ {x : C} {y : FormSpace k N d}, J.subschemeι (iC x) = y →
      IsClosed ({y} : Set (FormSpace k N d)) →
      ∃ t, g t = y ∧ IsClosed ({t} : Set (normalizationSchemeOverField k
        (iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _))) := by
    intro x y hxy hy
    obtain ⟨t, ht⟩ := ν.surjective x
    have hne : (g ⁻¹' {y}).Nonempty := ⟨t, by simp [g, ht, hxy]⟩
    obtain ⟨t₀, ht₀, ht₀c⟩ : (g ⁻¹' {y} ∩ closedPoints _).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty] at hem
      have h2 := JacobsonSpace.closure_inter_closedPoints (hy.preimage g.continuous)
      rw [hem, closure_empty] at h2
      exact hne.ne_empty h2.symm
    exact ⟨t₀, ht₀, ht₀c⟩
  obtain ⟨t, htq, htc⟩ := hlift (by rw [he, hcq]) hq
  obtain ⟨t', htq', htc'⟩ := hlift (by rw [he', hcq']) hq'
  have hgφ : g ≫ ProjSpace.toSpec k _ = ν ≫ iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _ := by
    simp only [g, Category.assoc]
  have hgW : ∀ s, g s ∈ W := fun s => hTW (hrange ▸ ⟨_, rfl⟩)
  have := cartierDegree_chowCycle_eq_of_curve i d hd W hW E _ _ hΓ
    (IsCurve.topologicalKrullDim_eq_one (k := k)
      (f := ν ≫ iC ≫ J.subschemeι ≫ Intersection.ProjSpace.toSpec k _)) g hgφ hgW htc htc'
  rwa [htq, htq'] at this

/-- **Cartier degrees are locally constant on the Chow-form locus.** The locus is a finite union of
irreducible closed subsets, on each of which the degree is constant; the union of those on which it
takes the value at `p` is open and closed in the locus. -/
private theorem cartierDegree_chowCycle_eq (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) (W : TopologicalSpace.Closeds (FormSpace k N d))
    (hW : ∀ p, IsClosed ({p} : Set _) → (p ∈ W ↔ ∃ Z, IsChowPointOf i d Z p))
    (E : X.CartierDivisor) {p p' : FormSpace k N d} (hp : IsClosed ({p} : Set _))
    (hp' : IsClosed ({p'} : Set _)) (hpW : p ∈ W) (h : p' ∈ connectedComponentIn W p) :
    Mori.OneCycle.cartierDegree E
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d p)) =
      Mori.OneCycle.cartierDegree E
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d p')) := by
  classical
  haveI := finite_bidegree N d
  haveI : JacobsonSpace (FormSpace k N d) :=
    LocallyOfFiniteType.jacobsonSpace (Intersection.ProjSpace.toSpec k _)
  haveI : IsLocallyNoetherian (FormSpace k N d) :=
    LocallyOfFiniteType.isLocallyNoetherian (Intersection.ProjSpace.toSpec k _)
  haveI : CompactSpace (FormSpace k N d) :=
    QuasiCompact.compactSpace_of_compactSpace (Intersection.ProjSpace.toSpec k _)
  haveI : IsNoetherian (FormSpace k N d) := {}
  set δ : FormSpace k N d → ℝ := fun q => Mori.OneCycle.cartierDegree E
    (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (chowCycle i d q))
  change δ p = δ p'
  obtain ⟨T, hTf, hTc, hTi, hT⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible W.isClosed
  have htW : ∀ t ∈ T, t ⊆ W := fun t ht => hT ▸ Set.subset_sUnion_of_mem ht
  -- every irreducible closed set contains a closed point
  have hcp : ∀ t ∈ T, ∃ q ∈ t, IsClosed ({q} : Set (FormSpace k N d)) := fun t ht => by
    by_contra hall
    push Not at hall
    have : t ∩ closedPoints (FormSpace k N d) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun q ⟨hqt, hqc⟩ => hall q hqt hqc
    have h2 := JacobsonSpace.closure_inter_closedPoints (hTc t ht)
    rw [this, closure_empty] at h2
    exact (hTi t ht).nonempty.ne_empty h2.symm
  have hconst : ∀ t ∈ T, ∀ q ∈ t, ∀ q' ∈ t, IsClosed ({q} : Set (FormSpace k N d)) →
      IsClosed ({q'} : Set (FormSpace k N d)) → δ q = δ q' := fun t ht q hq q' hq' hqc hq'c =>
    cartierDegree_chowCycle_eq_of_isIrreducible i d hd W hW E (hTc t ht) (hTi t ht) (htW t ht)
      hqc hq'c hq hq'
  set K₁ := ⋃₀ {t ∈ T | ∀ q ∈ t, IsClosed ({q} : Set (FormSpace k N d)) → δ q = δ p}
  set K₂ := ⋃₀ {t ∈ T | ∀ q ∈ t, IsClosed ({q} : Set (FormSpace k N d)) → δ q ≠ δ p}
  have hK₁ : IsClosed K₁ := (hTf.subset fun t ht => ht.1).isClosed_sUnion fun t ht => hTc t ht.1
  have hK₂ : IsClosed K₂ := (hTf.subset fun t ht => ht.1).isClosed_sUnion fun t ht => hTc t ht.1
  have hcover : (W : Set (FormSpace k N d)) ⊆ K₁ ∪ K₂ := by
    intro x hx
    rw [hT] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨q₀, hq₀t, hq₀c⟩ := hcp t ht
    by_cases h0 : δ q₀ = δ p
    · exact Or.inl ⟨t, ⟨ht, fun q hq hqc => (hconst t ht q hq q₀ hq₀t hqc hq₀c).trans h0⟩, hxt⟩
    · exact Or.inr ⟨t, ⟨ht, fun q hq hqc => by
        rw [hconst t ht q hq q₀ hq₀t hqc hq₀c]; exact h0⟩, hxt⟩
  have hdisj : K₁ ∩ K₂ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x ⟨⟨t₁, ht₁, hx₁⟩, ⟨t₂, ht₂, hx₂⟩⟩ => ?_
    have hne : (t₁ ∩ t₂ ∩ closedPoints (FormSpace k N d)).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty] at hem
      have h2 := JacobsonSpace.closure_inter_closedPoints ((hTc t₁ ht₁.1).inter (hTc t₂ ht₂.1))
      rw [hem, closure_empty] at h2
      exact (Set.eq_empty_iff_forall_notMem.mp h2.symm) x ⟨hx₁, hx₂⟩
    obtain ⟨q, ⟨hq₁, hq₂⟩, hqc⟩ := hne
    exact ht₂.2 q hq₂ hqc (ht₁.2 q hq₁ hqc)
  have hpK₂ : p ∉ K₂ := fun ⟨t, ht, hpt⟩ => ht.2 p hpt hp rfl
  have hsub : connectedComponentIn (W : Set (FormSpace k N d)) p ⊆ K₁ := by
    have hcc : _root_.IsPreconnected (connectedComponentIn (W : Set (FormSpace k N d)) p) :=
      isPreconnected_connectedComponentIn
    have hpre := (isPreconnected_iff_subset_of_disjoint_closed.mp hcc) K₁ K₂ hK₁ hK₂
      ((connectedComponentIn_subset _ _).trans hcover) (by rw [hdisj, Set.inter_empty])
    rcases hpre with h1 | h2
    · exact h1
    · exact absurd (h2 (mem_connectedComponentIn hpW)) hpK₂
  obtain ⟨t, ht, hp't⟩ := hsub h
  exact (ht.2 p' hp't hp').symm

end ChowForms

/-- The Chow variety of curves of degree `d`, with degree constancy stated for Cartier
divisors. -/
private theorem exists_chowVariety_cartier {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {N : ℕ} (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) :
    haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
    let sX : X ⟶ Spec (.of k) := i ≫ projToSpecCoeff k N
    -- the `𝒪(1)`-degree of a 1-cycle on `X`, computed on its push-forward to `ℙᴺ_k`
    let deg : Mori.OneCycle ℤ sX → ℤ := fun Z =>
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
        (Mori.OneCycle.pushforward ℤ sX (projToSpecCoeff k N) i Z)
    -- the support `⋃ᵢ Cᵢ ⊆ X` of a 1-cycle `∑ᵢ mᵢ Cᵢ`
    let supp : Mori.OneCycle ℤ sX → Set X := fun Z =>
      ⋃ C ∈ Z.support, closure {C.point}
    -- the fundamental cycle `∑ᵢ mᵢ q_*[Cᵢ]` of the fibre over `s` of a family `ρ : 𝒟 ⟶ T`
    let cyc : ∀ {T 𝒟 : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (ρ : 𝒟 ⟶ T) (r : 𝒟 ⟶ X) (s : T),
        Mori.OneCycle ℤ sX := fun sT ρ r s =>
      ∑ᶠ C : {C : Mori.ProperCurve (ρ.fiberι s ≫ ρ ≫ sT) //
              closure {C.point} ∈ irreducibleComponents (ρ.fiber s)},
        ((Module.length ((ρ.fiber s).presheaf.stalk C.1.point)
            ((ρ.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
          Mori.cyclePushforwardOfPoint ℤ sX (ρ.fiberι s ≫ r) C.1.point
    ∃ (𝒞 : Scheme.{u}) (s𝒞 : 𝒞 ⟶ Spec (.of k)) (cycOf : 𝒞 → Mori.OneCycle ℤ sX),
      IsProjectiveMorphism s𝒞 ∧ IsReduced 𝒞 ∧
      Set.BijOn cycOf {c | IsClosed ({c} : Set 𝒞)} {Z | 0 ≤ Z ∧ deg Z = d} ∧
      (∀ (S 𝒞' : Scheme.{u}) (sS : S ⟶ Spec (.of k)), Mori.IsNormalVariety k sS →
        ∀ (π : 𝒞' ⟶ S) (q : 𝒞' ⟶ X) (hπq : π ≫ sS = q ≫ sX),
          IsClosedImmersion (pullback.lift π q hπq) → IsProper π → Flat π →
          (∀ s : S, IsClosed ({s} : Set S) → ∀ x : π.fiber s,
            closure {x} ∈ irreducibleComponents (π.fiber s) →
              topologicalKrullDim (Mori.curveSubschemeAt x) = 1) →
          (∀ s : S, IsClosed ({s} : Set S) → deg (cyc sS π q s) = d) →
          ∃ φ : S ⟶ 𝒞, φ ≫ s𝒞 = sS ∧
            ∀ s : S, IsClosed ({s} : Set S) → cycOf (φ s) = cyc sS π q s) ∧
      (∀ (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)), Mori.IsNormalVariety k sS →
        ∀ φ : S ⟶ 𝒞, φ ≫ s𝒞 = sS →
          ∃ I : Set (pullback sS sX : Scheme.{u}), IsClosed I ∧
            (∀ p : (pullback sS sX : Scheme.{u}), IsClosed {p} →
              (p ∈ I ↔ pullback.snd sS sX p ∈ supp (cycOf (φ (pullback.fst sS sX p))))) ∧
            ∀ Z, Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Z → Dense (pullback.fst sS sX '' Z)) ∧
      ∀ E : X.CartierDivisor, ∀ c c' : 𝒞, IsClosed ({c} : Set 𝒞) →
        IsClosed ({c'} : Set 𝒞) → c' ∈ connectedComponent c →
          Mori.OneCycle.cartierDegree E
              (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (cycOf c)) =
            Mori.OneCycle.cartierDegree E
              (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero (cycOf c')) := by
  intro sX deg supp cyc
  haveI := finite_bidegree N d
  haveI := nonempty_bidegree N d
  obtain ⟨W, hW⟩ := exists_closeds_chowPoints i d hd
  let J := Scheme.IdealSheafData.vanishingIdeal W
  haveI : IsReduced J.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal W
  have hrange : Set.range J.subschemeι = W := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal W
  have hmemW : ∀ c, J.subschemeι c ∈ W := fun c => by
    rw [← SetLike.mem_coe, ← hrange]
    exact Set.mem_range_self c
  have hclosed : ∀ c : J.subscheme, IsClosed ({c} : Set J.subscheme) ↔
      IsClosed ({J.subschemeι c} : Set (FormSpace k N d)) := by
    intro c
    rw [J.subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed, Set.image_singleton]
  have hinj : Function.Injective J.subschemeι := J.subschemeι.isClosedEmbedding.injective
  refine ⟨J.subscheme, J.subschemeι ≫ Intersection.ProjSpace.toSpec k _, fun c => chowCycle i d (J.subschemeι c),
    isProjectiveMorphism_comp_toSpec k J.subschemeι, inferInstance, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- maps closed points to effective degree-`d` cycles
    intro c hc
    obtain h := isChowPointOf_chowCycle ((hW _ ((hclosed c).mp hc)).mp (hmemW c))
    exact ⟨h.1, h.2.1⟩
  · -- injective on closed points
    intro c hc c' hc' hcc
    have h := isChowPointOf_chowCycle ((hW _ ((hclosed c).mp hc)).mp (hmemW c))
    have h' := isChowPointOf_chowCycle ((hW _ ((hclosed c').mp hc')).mp (hmemW c'))
    simp only at hcc
    rw [hcc] at h
    exact hinj (eq_of_isChowPointOf i d hd ((hclosed c).mp hc) ((hclosed c').mp hc') h h')
  · -- surjective onto effective degree-`d` cycles
    rintro Z ⟨hZ, hZd⟩
    obtain ⟨p, hp, hZp⟩ := exists_isChowPointOf i d hd Z hZ hZd
    obtain ⟨c, rfl⟩ : p ∈ Set.range J.subschemeι := by
      rw [hrange]
      exact (hW p hp).mpr ⟨Z, hZp⟩
    refine ⟨c, (hclosed c).mpr hp, ?_⟩
    exact eq_of_isChowPointOf_of_isChowPointOf i d hd hp
      (isChowPointOf_chowCycle ⟨Z, hZp⟩) hZp
  · -- the family clause
    intro S 𝒞' sS hS π q hπq himm hprop hflat hpure hdeg
    obtain ⟨φ₀, hφ₀, hφ₀Z⟩ := exists_chowPoint_family i d hd S 𝒞' sS hS π q hπq himm hprop
      hflat hpure (fun s => cyc sS π q s) (fun s => rfl) hdeg
    haveI := hS.1
    haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
    haveI : QuasiCompact φ₀ := by
      haveI : QuasiCompact (φ₀ ≫ Intersection.ProjSpace.toSpec k _) := hφ₀ ▸ inferInstance
      exact QuasiCompact.of_comp φ₀ (Intersection.ProjSpace.toSpec k _)
    obtain ⟨φ, hφ⟩ := exists_comp_subschemeι_eq φ₀ W fun s hs =>
      (hW _ (hφ₀Z s hs).1).mpr ⟨_, (hφ₀Z s hs).2⟩
    refine ⟨φ, by rw [← Category.assoc, hφ, hφ₀], fun s hs => ?_⟩
    have hs' : φ₀ s = J.subschemeι (φ s) := by rw [← hφ]; rfl
    have h₀ := (hφ₀Z s hs).2
    rw [hs'] at h₀
    have hcl : IsClosed ({J.subschemeι (φ s)} : Set (FormSpace k N d)) := hs' ▸ (hφ₀Z s hs).1
    exact eq_of_isChowPointOf_of_isChowPointOf i d hd hcl (isChowPointOf_chowCycle ⟨_, h₀⟩) h₀
  · -- the support incidence
    intro S sS hS φ hφ
    exact exists_supportIncidence i d hd W hW S sS hS (φ ≫ J.subschemeι)
      (by rw [Category.assoc, hφ]) (fun s => hmemW (φ s))
  · -- Cartier degrees are constant on connected components
    intro E c c' hc hc' hcc
    refine (cartierDegree_chowCycle_eq i d hd W hW E ((hclosed c).mp hc) ((hclosed c').mp hc')
      (hmemW c) ?_)
    refine (isPreconnected_connectedComponent.image _
      J.subschemeι.continuous.continuousOn).subset_connectedComponentIn
      ⟨c, mem_connectedComponent, rfl⟩ ?_ ⟨c', hcc, rfl⟩
    rintro _ ⟨x, -, rfl⟩
    exact hmemW x

/-- Existence of the Chow variety of degree-`d` curve cycles on `X`; see
`MMP.Chow.exists_chowVariety`. -/
theorem solution {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {N : ℕ} (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) :
    haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
    let sX : X ⟶ Spec (.of k) := i ≫ projToSpecCoeff k N
    -- the `𝒪(1)`-degree of a 1-cycle on `X`, computed on its push-forward to `ℙᴺ_k`
    let deg : Mori.OneCycle ℤ sX → ℤ := fun Z =>
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
        (Mori.OneCycle.pushforward ℤ sX (projToSpecCoeff k N) i Z)
    -- the support `⋃ᵢ Cᵢ ⊆ X` of a 1-cycle `∑ᵢ mᵢ Cᵢ`
    let supp : Mori.OneCycle ℤ sX → Set X := fun Z =>
      ⋃ C ∈ Z.support, closure {C.point}
    -- the fundamental cycle `∑ᵢ mᵢ q_*[Cᵢ]` of the fibre over `s` of a family `ρ : 𝒟 ⟶ T`
    let cyc : ∀ {T 𝒟 : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (ρ : 𝒟 ⟶ T) (r : 𝒟 ⟶ X) (s : T),
        Mori.OneCycle ℤ sX := fun sT ρ r s =>
      ∑ᶠ C : {C : Mori.ProperCurve (ρ.fiberι s ≫ ρ ≫ sT) //
              closure {C.point} ∈ irreducibleComponents (ρ.fiber s)},
        ((Module.length ((ρ.fiber s).presheaf.stalk C.1.point)
            ((ρ.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
          Mori.cyclePushforwardOfPoint ℤ sX (ρ.fiberι s ≫ r) C.1.point
    ∃ (𝒞 : Scheme.{u}) (s𝒞 : 𝒞 ⟶ Spec (.of k)) (cycOf : 𝒞 → Mori.OneCycle ℤ sX),
      IsProjectiveMorphism s𝒞 ∧ IsReduced 𝒞 ∧
      Set.BijOn cycOf {c | IsClosed ({c} : Set 𝒞)} {Z | 0 ≤ Z ∧ deg Z = d} ∧
      (∀ (S 𝒞' : Scheme.{u}) (sS : S ⟶ Spec (.of k)), Mori.IsNormalVariety k sS →
        ∀ (π : 𝒞' ⟶ S) (q : 𝒞' ⟶ X) (hπq : π ≫ sS = q ≫ sX),
          IsClosedImmersion (pullback.lift π q hπq) → IsProper π → Flat π →
          (∀ s : S, IsClosed ({s} : Set S) → ∀ x : π.fiber s,
            closure {x} ∈ irreducibleComponents (π.fiber s) →
              topologicalKrullDim (Mori.curveSubschemeAt x) = 1) →
          (∀ s : S, IsClosed ({s} : Set S) → deg (cyc sS π q s) = d) →
          ∃ φ : S ⟶ 𝒞, φ ≫ s𝒞 = sS ∧
            ∀ s : S, IsClosed ({s} : Set S) → cycOf (φ s) = cyc sS π q s) ∧
      (∀ (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)), Mori.IsNormalVariety k sS →
        ∀ φ : S ⟶ 𝒞, φ ≫ s𝒞 = sS →
          ∃ I : Set (pullback sS sX : Scheme.{u}), IsClosed I ∧
            (∀ p : (pullback sS sX : Scheme.{u}), IsClosed {p} →
              (p ∈ I ↔ pullback.snd sS sX p ∈ supp (cycOf (φ (pullback.fst sS sX p))))) ∧
            ∀ Z, Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Z → Dense (pullback.fst sS sX '' Z)) ∧
      ∀ L : Mori.KCartierDivisor ℚ X, ∀ c c' : 𝒞, IsClosed ({c} : Set 𝒞) →
        IsClosed ({c'} : Set 𝒞) → c' ∈ connectedComponent c →
          Mori.OneCycle.intersectionNumber (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
              (cycOf c)) (Fourfold.KCartierDivisor.toReal L) =
            Mori.OneCycle.intersectionNumber (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
              (cycOf c')) (Fourfold.KCartierDivisor.toReal L) := by
  intro sX deg supp cyc
  obtain ⟨𝒞, s𝒞, cycOf, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_chowVariety_cartier i d hd
  refine ⟨𝒞, s𝒞, cycOf, h₁, h₂, h₃, h₄, h₅, fun L c c' hc hc' hcc => ?_⟩
  rw [intersectionNumber_toReal, intersectionNumber_toReal]
  exact Finsupp.sum_congr fun E _ => by rw [h₆ E c c' hc hc' hcc]

end MMP.Chow.FixedDegreeCurveCyclesProof

/-!
## Main statement

Let `k` be an algebraically closed field of characteristic zero, `X ⊆ ℙᴺ_k` a projective
`k`-scheme and `d > 0`. An *effective curve cycle of degree `d`* on `X` is a 1-cycle
`Z = ∑ᵢ mᵢ Cᵢ` with `mᵢ ≥ 0` whose push-forward to `ℙᴺ_k` has degree `d` against `𝒪(1)`.
There is a reduced projective `k`-scheme `𝒞_d(X)` together with an assignment `c ↦ Z_c` of a
1-cycle to each point, which is a bijection from the closed points of `𝒞_d(X)` onto the effective
curve cycles of degree `d`, with three properties:

* every proper flat family `𝒞 ⊆ S ×ₖ X` of pure one-dimensional fibres over a normal variety `S`
  whose fibre cycles have degree `d` is classified by a `k`-morphism `S ⟶ 𝒞_d(X)` sending each
  closed point `s` to the point whose cycle is the fundamental cycle of the fibre `𝒞_s`;
* for every `k`-morphism `φ : S ⟶ 𝒞_d(X)` from a normal variety, the support incidence
  `{(s, x) | x ∈ Supp Z_{φ(s)}} ⊆ S ×ₖ X` is closed and each of its irreducible components
  dominates `S`;
* for every `ℚ`-Cartier divisor `L` on `X`, the degree `(Z_c · L)` is constant on each connected
  component of `𝒞_d(X)`.

## Main results

* `MMP.Chow.exists_chowVariety`: the existence of `𝒞_d(X)` with these properties.

## Implementation notes

* The source works over `ℂ`; the statement is made over an algebraically closed field of
  characteristic zero.
* `ℙᴺ_k` is `Proj k[T₀, …, T_N]` with structure morphism `projToSpecCoeff` and hyperplane sheaf
  `𝒪(1)`, and `X ⊆ ℙᴺ_k` is a closed immersion `i`; a scheme is projective over `k` when its
  structure morphism is an `IsProjectiveMorphism`.
* The points of `𝒞_d(X)` are related to cycles through a function `cyc : 𝒞_d(X) → Z₁(X)`, of
  which only the values at closed points carry meaning. A closed subset of a scheme of finite
  type over a field is determined by its closed points, so the support incidence is described by
  its closed points.
* The fundamental cycle of a fibre `𝒞_s` is `∑ᵢ mᵢ [Cᵢ]`, the sum over the irreducible components
  `Cᵢ` of `𝒞_s`, with `mᵢ` the length of the local ring of `𝒞_s` at the generic point of `Cᵢ`,
  pushed forward to `X`.

## References

* [J. Kollár, *Rational curves on algebraic varieties*][Kollar1996], I.3–I.4
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Stacks.AlgebraicGeometry.ProjPolyChart

namespace MMP.Chow

/-- **The Chow variety of curves of degree `d`.** Let `k` be an algebraically closed field of
characteristic zero, `i : X ⟶ ℙᴺ_k` a closed immersion of `k`-schemes and `d > 0`. There is a
reduced projective `k`-scheme `𝒞` with a function `cyc : 𝒞 → Z₁(X)` such that

* `cyc` maps the closed points of `𝒞` bijectively onto the effective 1-cycles on `X` whose
  push-forward to `ℙᴺ_k` has `𝒪(1)`-degree `d`;
* for a normal `k`-variety `S` and a closed subscheme `𝒞' ⊆ S ×ₖ X`, proper and flat over `S`,
  with pure one-dimensional closed fibres whose fundamental cycles have degree `d`, there is a
  `k`-morphism `φ : S ⟶ 𝒞` with `cyc (φ s)` the fundamental cycle of the fibre over each closed
  point `s`;
* for a normal `k`-variety `S` and a `k`-morphism `φ : S ⟶ 𝒞`, there is a closed subset of
  `S ×ₖ X` whose closed points are the `(s, x)` with `x ∈ Supp (cyc (φ s))`, and each of its
  irreducible components (maximal irreducible subsets) has dense image in `S`;
* for every `ℚ`-Cartier divisor `L` on `X`, the intersection number `(cyc c · L)` takes the same
  value at any two closed points `c, c'` in the same connected component of `𝒞`. -/
@[mmp "thm_mmp_projective_fixed_degree_curve_cycles"]
public theorem exists_chowVariety {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {N : ℕ} (i : X ⟶ AlgebraicGeometry.Proj (polyGrading k N))
    [IsClosedImmersion i] (d : ℕ) (hd : 0 < d) :
    haveI := Stacks.PicardUFD.isInvertible_twistingSheaf k N 1
    let sX : X ⟶ Spec (.of k) := i ≫ projToSpecCoeff k N
    -- the `𝒪(1)`-degree of a 1-cycle on `X`, computed on its push-forward to `ℙᴺ_k`
    let deg : Mori.OneCycle ℤ sX → ℤ := fun Z =>
      Mori.OneCycle.degree ℤ (projToSpecCoeff k N)
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k N) 1)
        (Mori.OneCycle.pushforward ℤ sX (projToSpecCoeff k N) i Z)
    -- the support `⋃ᵢ Cᵢ ⊆ X` of a 1-cycle `∑ᵢ mᵢ Cᵢ`
    let supp : Mori.OneCycle ℤ sX → Set X := fun Z =>
      ⋃ C ∈ Z.support, closure {C.point}
    -- the fundamental cycle `∑ᵢ mᵢ q_*[Cᵢ]` of the fibre over `s` of a family `ρ : 𝒟 ⟶ T`
    let cyc : ∀ {T 𝒟 : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (ρ : 𝒟 ⟶ T) (r : 𝒟 ⟶ X) (s : T),
        Mori.OneCycle ℤ sX := fun sT ρ r s =>
      ∑ᶠ C : {C : Mori.ProperCurve (ρ.fiberι s ≫ ρ ≫ sT) //
              closure {C.point} ∈ irreducibleComponents (ρ.fiber s)},
        ((Module.length ((ρ.fiber s).presheaf.stalk C.1.point)
            ((ρ.fiber s).presheaf.stalk C.1.point)).toNat : ℤ) •
          Mori.cyclePushforwardOfPoint ℤ sX (ρ.fiberι s ≫ r) C.1.point
    ∃ (𝒞 : Scheme.{u}) (s𝒞 : 𝒞 ⟶ Spec (.of k)) (cycOf : 𝒞 → Mori.OneCycle ℤ sX),
      IsProjectiveMorphism s𝒞 ∧ IsReduced 𝒞 ∧
      Set.BijOn cycOf {c | IsClosed ({c} : Set 𝒞)} {Z | 0 ≤ Z ∧ deg Z = d} ∧
      (∀ (S 𝒞' : Scheme.{u}) (sS : S ⟶ Spec (.of k)), Mori.IsNormalVariety k sS →
        ∀ (π : 𝒞' ⟶ S) (q : 𝒞' ⟶ X) (hπq : π ≫ sS = q ≫ sX),
          IsClosedImmersion (pullback.lift π q hπq) → IsProper π → Flat π →
          (∀ s : S, IsClosed ({s} : Set S) → ∀ x : π.fiber s,
            closure {x} ∈ irreducibleComponents (π.fiber s) →
              topologicalKrullDim (Mori.curveSubschemeAt x) = 1) →
          (∀ s : S, IsClosed ({s} : Set S) → deg (cyc sS π q s) = d) →
          ∃ φ : S ⟶ 𝒞, φ ≫ s𝒞 = sS ∧
            ∀ s : S, IsClosed ({s} : Set S) → cycOf (φ s) = cyc sS π q s) ∧
      (∀ (S : Scheme.{u}) (sS : S ⟶ Spec (.of k)), Mori.IsNormalVariety k sS →
        ∀ φ : S ⟶ 𝒞, φ ≫ s𝒞 = sS →
          ∃ I : Set (pullback sS sX : Scheme.{u}), IsClosed I ∧
            (∀ p : (pullback sS sX : Scheme.{u}), IsClosed {p} →
              (p ∈ I ↔ pullback.snd sS sX p ∈ supp (cycOf (φ (pullback.fst sS sX p))))) ∧
            ∀ Z, Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ I) Z → Dense (pullback.fst sS sX '' Z)) ∧
      ∀ L : Mori.KCartierDivisor ℚ X, ∀ c c' : 𝒞, IsClosed ({c} : Set 𝒞) →
        IsClosed ({c'} : Set 𝒞) → c' ∈ connectedComponent c →
          Mori.OneCycle.intersectionNumber (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
              (cycOf c)) (Fourfold.KCartierDivisor.toReal L) =
            Mori.OneCycle.intersectionNumber (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero
              (cycOf c')) (Fourfold.KCartierDivisor.toReal L) :=
  MMP.Chow.FixedDegreeCurveCyclesProof.solution i d hd

end MMP.Chow
