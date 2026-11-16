module

public import MMP.AlgebraicTopology.ThomClass.OfRank
public import MMP.AlgebraicTopology.ComplexVectorBundle.OfStacksBundle
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSectionConormal

/-!
# The Thom class of a Stacks vector bundle (Fulton, §19.1)

Let `X` be a scheme over `ℂ` and `ℰ` a quasi-coherent `𝒪_X`-module, finite locally free of rank
`r`, with vector bundle `π : 𝐕(ℰ) ⟶ X` (`MMP.Modules.totalSpace`, `MMP.Modules.proj`) and zero
section `0 : X ⟶ 𝐕(ℰ)` (`AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection`). As in
Fulton, §19.1, `𝐕(ℰ)(ℂ) → X(ℂ)` is regarded as a complex topological vector bundle: the fibre
over `x ∈ V(ℂ)` is a complex vector space through the coordinates `p ↦ (bᵢ(p))ᵢ` of a chart
`(V, b)` (`MMP.Modules.coord`), and the transitions are linear.

A *complex frame* of a fibre is a map `f : ℂʳ → 𝐕(ℰ)(ℂ)` onto the fibre over a point `x ∈ V(ℂ)`
that is a complex-linear isomorphism in the coordinates of a chart: `coord c (f w) = A w` for
some `A ∈ GL(r, ℂ)`. The coordinates of the zero section vanish, so `f` carries `ℂʳ - 0` into
`𝐕(ℰ)(ℂ) - 0(X(ℂ))`. A *Thom class* is a class
`u ∈ H^{2r}(𝐕(ℰ)(ℂ), 𝐕(ℰ)(ℂ) - 0(X(ℂ)); R)` with `⟨u, f_* μ⟩ = 1` for every complex frame `f` and
every simplex `μ` around `0` in `ℂʳ` oriented by the complex structure.

The bundle `𝐕(ℰ)(ℂ) → X(ℂ)` is a Mathlib vector bundle with fibre `ℂʳ`
(`MMP.Modules.instVectorBundleFibre`), with total space homeomorphic to `𝐕(ℰ)(ℂ)`
(`MMP.Modules.totalSpaceHomeomorph`). Pulling back along that homeomorphism identifies Thom
classes with those of the topological bundle (`MMP.IsThomClass`), and Thom's theorem for
topological bundles (`MMP.ThomClass.existsUnique_isThomClass`) gives exactly one.

## Main definitions

* `MMP.Modules.zeroSection E`: the zero section `X ⟶ 𝐕(ℰ)`.
* `MMP.Modules.IsComplexFrame E r f`: complex frames of the fibres of `𝐕(ℰ)(ℂ)`.
* `MMP.Modules.IsThomClass R E r u`: Thom classes of `𝐕(ℰ)`.
* `MMP.Modules.thomClass R E r`: the Thom class `u_ℰ`.
* `MMP.Modules.pullbackTop R E r`, `MMP.Modules.pullbackAlg R E r`: the pull-backs between the
  cohomology of `𝐕(ℰ)(ℂ)` and of the total space of the topological bundle.

## Main results

* `MMP.Modules.mapFun_proj_mapFun_zeroSection`: `π ∘ 0 = id` on points.
* `MMP.Modules.coord_mapFun_zeroSection`: the chart coordinates of the zero section vanish.
* `MMP.Modules.IsComplexFrame.notMem_range_zeroSection`: a complex frame carries `ℂʳ - 0` off the
  zero section.
* `MMP.Modules.isThomClass_iff_isThomClassOfRank`: a class is a Thom class iff its pull-back is
  a Thom class of the topological bundle.
* `MMP.Modules.existsUnique_isThomClass`: Thom's theorem: there is exactly one Thom class.
* `MMP.Modules.pullbackTop_thomClass`, `MMP.Modules.thomClass_eq_pullbackAlg`: `u_ℰ` is the Thom
  class of the topological bundle.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], Thm. 10.4.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Finsupp Opposite
open scoped Matrix

namespace MMP.Modules

open UnderlyingSpace SingularChain SingularCochain

variable (R : Type) [CommRing R] {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent] {r : ℕ}

/-! ### The zero section -/

/-- The zero section `0 : X ⟶ 𝐕(ℰ)` of the vector bundle of `ℰ`. -/
abbrev zeroSection : X ⟶ totalSpace E :=
  Scheme.Modules.vectorBundleZeroSection X E

/-- The zero section is a section of the projection: `0 ≫ π = 𝟙 X`. -/
@[reassoc (attr := simp)]
lemma zeroSection_proj : zeroSection E ≫ proj E = 𝟙 X :=
  Scheme.Modules.vectorBundleZeroSection_comp_vectorBundleToBase X E

/-- Over a base scheme `S` of `X`, the zero section `X ⟶ 𝐕(ℰ)` is a morphism over `S`. -/
instance isOver_zeroSection {S : Scheme.{0}} [X.Over S] : (zeroSection E).IsOver S :=
  ⟨by
    change zeroSection E ≫ proj E ≫ X ↘ S = X ↘ S
    rw [zeroSection_proj_assoc]⟩

/-- The augmentation `Γ(V, Sym ℰ) → Γ(X, V)` kills the degree-one sections. -/
@[simp]
lemma symmetricAlgebraSheafAugmentation_app_generator {V : X.Opens} (hV : IsAffineOpen V)
    (m : Γ(E, V)) :
    (Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V) (generator E hV m) = 0 := by
  rw [generator_apply]
  exact (Stacks.SymAlgSections.symmetricAlgebraSheafAugmentation_app_symSectionsRingEquiv E hV
    _).trans (SymmetricAlgebra.algebraMapInv_ι m)

variable [X.Over (Spec (.of ℂ))]

/-- The projection of the point of the zero section over `x` is `x`. -/
@[simp]
lemma mapFun_proj_mapFun_zeroSection (x : UnderlyingSpace ℂ X) :
    mapFun (proj E) (mapFun (zeroSection E) x) = x :=
  UnderlyingSpace.ext (by
    simp only [toHom_mapFun, Category.assoc, zeroSection_proj, Category.comp_id])

/-- Over an affine open `V`, the point of the zero section over `x ∈ V(ℂ)`, as a point of
`Spec Γ(V, Sym ℰ)`, is `x` followed by the spectrum of the augmentation `Γ(V, Sym ℰ) → Γ(X, V)`. -/
lemma liftSpec_mapFun_zeroSection (V : X.affineOpens) (x : UnderlyingSpace ℂ X)
    (hx : ⊤ ≤ x.toHom ⁻¹ᵁ V.1)
    (hp : ⊤ ≤ (mapFun (zeroSection E) x).toHom ⁻¹ᵁ (proj E ⁻¹ᵁ V.1)) :
    liftSpec E V (mapFun (zeroSection E) x) hp =
      openLift V.1 x.toHom hx ≫ V.1.toSpecΓ ≫
        Spec.map ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)) := by
  have h : V.1.toSpecΓ ≫
      Spec.map ((Scheme.Modules.symmetricAlgebraSheafAugmentation X E).app (op V.1)) ≫
        specSectionsι E V = V.1.ι ≫ zeroSection E :=
    (Scheme.Modules.ι_vectorBundleZeroSection X E V).symm
  rw [← cancel_mono (specSectionsι E V), liftSpec_ι, toHom_mapFun, Category.assoc,
    Category.assoc, h, openLift_ι_assoc]

/-- **The chart coordinates of the points of the zero section vanish.** -/
@[simp]
lemma coord_mapFun_zeroSection (c : Chart E r) (x : UnderlyingSpace ℂ X) :
    coord c (mapFun (zeroSection E) x) = 0 := by
  funext i
  by_cases hp : ⊤ ≤ (mapFun (zeroSection E) x).toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)
  · have hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1 := mapFun_proj_mapFun_zeroSection E x ▸ mapFun_proj_mem hp
    rw [coord_apply c hp, chartCoordSection, eval_totalSections,
      liftSpec_mapFun_zeroSection E c.1 x hx hp]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, specMap_appTop_ΓSpecIso_inv,
      symmetricAlgebraSheafAugmentation_app_generator, map_zero, Pi.zero_apply]
  · change evalExt _ (chartCoordSection c i) _ = 0
    exact dite_eq_right_of_eq_false (eq_false hp)

/-! ### Complex frames -/

variable (r) in
/-- A *complex frame* of a fibre of `𝐕(ℰ)(ℂ)`: a map `f : ℂʳ → 𝐕(ℰ)(ℂ)` onto the fibre over a
point `x ∈ V(ℂ)` of the domain of a chart `c = (V, b)` which, in the coordinates of `c`, is a
complex-linear isomorphism: `coord c (f w) = A w` for some `A ∈ GL(r, ℂ)`. -/
def IsComplexFrame (f : (Fin r → ℂ) → UnderlyingSpace ℂ (totalSpace E)) : Prop :=
  ∃ (x : UnderlyingSpace ℂ X) (c : Chart E r) (A : Matrix.GeneralLinearGroup (Fin r) ℂ),
    x ∈ chartBase c ∧
      ∀ w, mapFun (proj E) (f w) = x ∧ coord c (f w) = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ w

variable {E} in
/-- A complex frame carries `ℂʳ - 0` into `𝐕(ℰ)(ℂ) - 0(X(ℂ))`. -/
lemma IsComplexFrame.notMem_range_zeroSection
    {f : (Fin r → ℂ) → UnderlyingSpace ℂ (totalSpace E)} (hf : IsComplexFrame E r f)
    {w : Fin r → ℂ} (hw : w ≠ 0) :
    f w ∈ (range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ := by
  rintro ⟨y, hy⟩
  obtain ⟨x, c, A, -, h⟩ := hf
  have hAw : (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ w = 0 := by
    rw [← (h w).2, ← hy]
    exact coord_mapFun_zeroSection E c y
  apply hw
  simpa [Matrix.mulVec_mulVec] using congrArg (((A⁻¹ : Matrix.GeneralLinearGroup (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ) *ᵥ ·) hAw

/-! ### Thom classes -/

variable (r) in
/-- A *Thom class* of the vector bundle `𝐕(ℰ)` of `ℰ`, finite locally free of rank `r`, on a
scheme `X` over `ℂ`, regarded as a complex topological vector bundle on `X(ℂ)` (Fulton, §19.1):
a class `u ∈ H^{2r}(𝐕(ℰ)(ℂ), 𝐕(ℰ)(ℂ) - 0(X(ℂ)); R)` with `⟨u, f_* μ⟩ = 1` for every complex
frame `f : ℂʳ → 𝐕(ℰ)(ℂ)` of a fibre and every simplex `μ` around `0` oriented by
`e₁, i e₁, …, e_r, i e_r`. By Thom's theorem there is exactly one
(`MMP.Modules.existsUnique_isThomClass`, `MMP.Modules.thomClass`). -/
def IsThomClass (u : cohomologyWithSupports R (ModuleCat.of R R)
    (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
    (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)) : Prop :=
  ∀ (f : C(Fin r → ℂ, UnderlyingSpace ℂ (totalSpace E))) (hf : IsComplexFrame E r f)
    (v : Fin (2 * r + 1) → (Fin r → ℂ))
    (hv : ThomClass.IsOrientedSimplexAroundZero (ThomClass.complexOrientationBasis r) v),
    relEval (R := R) (single (f.comp (ThomClass.affineSimplex v)) 1)
      (eval_single_eq_zero_of_mem_relCoboundaries _ fun t ht ↦
        hf.notMem_range_zeroSection (hv.affineSimplex_ne_zero t ht))
      (relativeSingularCohomologyEquiv R
        (Y := TopCat.of (UnderlyingSpace ℂ (totalSpace E))) _ _ u) = 1

/-! ### The comparison with the topological bundle -/

section Topological

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- The zero of the fibre over `x` is the point of the zero section over `x`. -/
lemma zero_fibre_val (x : UnderlyingSpace ℂ X) :
    (0 : Fibre E r x).1 = mapFun (zeroSection E) x := by
  have hc := mem_chartBase_chartAt E r x
  have h0 : coord (chartAt E r x) (0 : Fibre E r x).1 = 0 :=
    Equiv.apply_symm_apply (fibreEquiv (chartAt E r x) x hc) 0
  exact congrArg Subtype.val (fibre_ext (chartAt E r x) hc (y := 0)
    (y' := ⟨mapFun (zeroSection E) x, mapFun_proj_mapFun_zeroSection E x⟩)
    (h0.trans (coord_mapFun_zeroSection E (chartAt E r x) x).symm))

variable (r)

/-- The zero section of the topological bundle is the zero section `0(X(ℂ))` of `𝐕(ℰ)(ℂ)`. -/
lemma totalSpaceHomeomorph_preimage_range_zeroSection :
    totalSpaceHomeomorph E r ⁻¹' range (UnderlyingSpace.map (K := ℂ) (zeroSection E)) =
      range (Bundle.zeroSection (Fin r → ℂ) (Fibre E r)) := by
  ext ⟨x, q⟩
  constructor
  · rintro ⟨y, hy⟩
    have hy' : mapFun (zeroSection E) y = q.1 := hy
    have hyx : y = x := by
      rw [← q.2, ← hy', mapFun_proj_mapFun_zeroSection]
    subst hyx
    refine ⟨y, ?_⟩
    change Bundle.TotalSpace.mk y 0 = Bundle.TotalSpace.mk y q
    congr 1
    exact Subtype.ext ((zero_fibre_val E y).trans hy')
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have h1 : y = x := congrArg Bundle.TotalSpace.proj hy
    subst h1
    have h2 : (0 : Fibre E r y) = q := (Bundle.TotalSpace.mk_inj).1 hy
    change mapFun (zeroSection E) y = q.1
    rw [← zero_fibre_val (r := r) E y, h2]

variable {r}

/-- A continuous linear frame `ψ : ℂʳ ≅ π⁻¹(x)` of the topological bundle is a complex frame. -/
lemma isComplexFrame_of_continuousLinearEquiv (x : UnderlyingSpace ℂ X)
    (ψ : (Fin r → ℂ) ≃L[ℂ] Fibre E r x) :
    IsComplexFrame E r fun w ↦ (ψ w).1 := by
  let L : (Fin r → ℂ) ≃ₗ[ℂ] (Fin r → ℂ) := ψ.toLinearEquiv.trans (fibreLinearEquiv E r x)
  let A : Matrix.GeneralLinearGroup (Fin r) ℂ :=
    ⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩
  refine ⟨x, chartAt E r x, A, mem_chartBase_chartAt E r x, fun w ↦ ⟨(ψ w).2, ?_⟩⟩
  change coord (chartAt E r x) (ψ w).1 = LinearMap.toMatrix' L.toLinearMap *ᵥ w
  rw [LinearMap.toMatrix'_mulVec]
  rfl

variable {E}

/-- The point `f w` of the fibre over `x`, for a complex frame `f` of the fibre over `x`. -/
def framePoint (f : C(Fin r → ℂ, UnderlyingSpace ℂ (totalSpace E))) (x : UnderlyingSpace ℂ X)
    (c : Chart E r) (A : Matrix.GeneralLinearGroup (Fin r) ℂ)
    (h : ∀ w, mapFun (proj E) (f w) = x ∧ coord c (f w) = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
    (w : Fin r → ℂ) : Fibre E r x :=
  ⟨f w, (h w).1⟩

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
/-- The chart coordinates of `MMP.Modules.framePoint f x c A h w` are `A w`. -/
lemma coord_framePoint (f : C(Fin r → ℂ, UnderlyingSpace ℂ (totalSpace E)))
    (x : UnderlyingSpace ℂ X) (c : Chart E r) (A : Matrix.GeneralLinearGroup (Fin r) ℂ)
    (h : ∀ w, mapFun (proj E) (f w) = x ∧ coord c (f w) = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ w)
    (w : Fin r → ℂ) :
    coord c (framePoint f x c A h w).1 = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ w :=
  (h w).2

/-- A complex frame `f : ℂʳ → 𝐕(ℰ)(ℂ)` of the fibre over `x`, as a continuous linear
isomorphism `ℂʳ ≅ π⁻¹(x)`. -/
def frameEquiv (f : C(Fin r → ℂ, UnderlyingSpace ℂ (totalSpace E))) (x : UnderlyingSpace ℂ X)
    (c : Chart E r) (A : Matrix.GeneralLinearGroup (Fin r) ℂ) (hx : x ∈ chartBase c)
    (h : ∀ w, mapFun (proj E) (f w) = x ∧ coord c (f w) = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) :
    (Fin r → ℂ) ≃L[ℂ] Fibre E r x :=
  have hval : ∀ y : Fibre E r x, coord c y.1 = fibreCoord c x y := fun y ↦
    (fibreCoord_apply c x hx y).symm
  { toFun := framePoint f x c A h
    invFun := fun y ↦ ((A⁻¹ : Matrix.GeneralLinearGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ
      coord c y.1
    map_add' := fun w w' ↦ fibre_ext c hx (by
      rw [coord_framePoint, hval, map_add, ← hval, ← hval, coord_framePoint, coord_framePoint,
        Matrix.mulVec_add])
    map_smul' := fun a w ↦ fibre_ext c hx (by
      rw [coord_framePoint, hval, map_smul, ← hval, coord_framePoint, Matrix.mulVec_smul]
      rfl)
    left_inv := fun w ↦ by
      change _ *ᵥ coord c (framePoint f x c A h w).1 = w
      rw [coord_framePoint, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    right_inv := fun y ↦ fibre_ext c hx (by
      rw [coord_framePoint, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec])
    continuous_toFun := f.continuous.subtype_mk _
    continuous_invFun := by
      refine Continuous.matrix_mulVec continuous_const ?_
      refine (continuousOn_coord c).comp_continuous continuous_subtype_val fun y ↦ ?_
      change ⊤ ≤ (mapFun (proj E) y.1).toHom ⁻¹ᵁ c.1.1
      rw [y.2]
      exact hx }

/-- The point of `𝐕(ℰ)(ℂ)` underlying `MMP.Modules.frameEquiv f x c A hx h w` is `f w`. -/
@[simp]
lemma frameEquiv_apply (f : C(Fin r → ℂ, UnderlyingSpace ℂ (totalSpace E)))
    (x : UnderlyingSpace ℂ X) (c : Chart E r) (A : Matrix.GeneralLinearGroup (Fin r) ℂ)
    (hx : x ∈ chartBase c)
    {h : ∀ w, mapFun (proj E) (f w) = x ∧ coord c (f w) = (A : Matrix (Fin r) (Fin r) ℂ) *ᵥ w}
    (w : Fin r → ℂ) :
    (frameEquiv f x c A hx h w).1 = f w :=
  rfl

variable (E r)

/-- The homeomorphism `Σ x, π⁻¹(x) ≅ 𝐕(ℰ)(ℂ)`, as a map of spaces. -/
def totalSpaceHom :
    TopCat.of (Bundle.TotalSpace (Fin r → ℂ) (Fibre E r)) ⟶
      TopCat.of (UnderlyingSpace ℂ (totalSpace E)) :=
  TopCat.ofHom ⟨totalSpaceHomeomorph E r, (totalSpaceHomeomorph E r).continuous⟩

/-- The inverse homeomorphism `𝐕(ℰ)(ℂ) ≅ Σ x, π⁻¹(x)`, as a map of spaces. -/
def totalSpaceInv :
    TopCat.of (UnderlyingSpace ℂ (totalSpace E)) ⟶
      TopCat.of (Bundle.TotalSpace (Fin r → ℂ) (Fibre E r)) :=
  TopCat.ofHom ⟨(totalSpaceHomeomorph E r).symm, (totalSpaceHomeomorph E r).symm.continuous⟩

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
/-- `MMP.Modules.totalSpaceInv` is a left inverse of `MMP.Modules.totalSpaceHom`. -/
@[reassoc (attr := simp)]
lemma totalSpaceHom_totalSpaceInv : totalSpaceHom E r ≫ totalSpaceInv E r = 𝟙 _ :=
  ConcreteCategory.hom_ext _ _ (totalSpaceHomeomorph E r).symm_apply_apply

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
/-- `MMP.Modules.totalSpaceInv` is a right inverse of `MMP.Modules.totalSpaceHom`. -/
@[reassoc (attr := simp)]
lemma totalSpaceInv_totalSpaceHom : totalSpaceInv E r ≫ totalSpaceHom E r = 𝟙 _ :=
  ConcreteCategory.hom_ext _ _ (totalSpaceHomeomorph E r).apply_symm_apply

/-- `MMP.Modules.totalSpaceHom` carries the complement of the zero section of the topological
bundle into `𝐕(ℰ)(ℂ) - 0(X(ℂ))`. -/
lemma compl_range_zeroSection_subset_preimage_totalSpaceHom :
    (range (Bundle.zeroSection (Fin r → ℂ) (Fibre E r)))ᶜ ⊆
      totalSpaceHom E r ⁻¹' (range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ := by
  intro p hp h
  exact hp ((totalSpaceHomeomorph_preimage_range_zeroSection E r) ▸ h)

/-- `MMP.Modules.totalSpaceInv` carries `𝐕(ℰ)(ℂ) - 0(X(ℂ))` into the complement of the zero
section of the topological bundle. -/
lemma compl_range_zeroSection_subset_preimage_totalSpaceInv :
    (range (UnderlyingSpace.map (K := ℂ) (zeroSection E)))ᶜ ⊆
      totalSpaceInv E r ⁻¹' (range (Bundle.zeroSection (Fin r → ℂ) (Fibre E r)))ᶜ := by
  intro q hq h
  rw [← totalSpaceHomeomorph_preimage_range_zeroSection E r] at h
  exact hq ((totalSpaceHomeomorph E r).apply_symm_apply q ▸ h)

/-- The pull-back `H^{2r}(𝐕(ℰ)(ℂ), 𝐕(ℰ)(ℂ) - 0) → H^{2r}(Σ x, π⁻¹(x), - 0)` to the topological
bundle, along the homeomorphism of total spaces. -/
abbrev pullbackTop :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ) ⟶
      cohomologyWithSupports R (ModuleCat.of R R)
        (TopCat.of (Bundle.TotalSpace (Fin r → ℂ) (Fibre E r)))
        (range (Bundle.zeroSection (Fin r → ℂ) (Fibre E r))) (2 * r : ℕ) :=
  relativeSingularCohomology.map R _ (totalSpaceHom E r)
    (compl_range_zeroSection_subset_preimage_totalSpaceHom E r) _

/-- The inverse of `MMP.Modules.pullbackTop`. -/
abbrev pullbackAlg :
    cohomologyWithSupports R (ModuleCat.of R R)
        (TopCat.of (Bundle.TotalSpace (Fin r → ℂ) (Fibre E r)))
        (range (Bundle.zeroSection (Fin r → ℂ) (Fibre E r))) (2 * r : ℕ) ⟶
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
        (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ) :=
  relativeSingularCohomology.map R _ (totalSpaceInv E r)
    (compl_range_zeroSection_subset_preimage_totalSpaceInv E r) _

/-- `MMP.Modules.pullbackAlg` is a left inverse of `MMP.Modules.pullbackTop`. -/
@[simp]
lemma pullbackAlg_pullbackTop (u) :
    (pullbackAlg R E r).hom ((pullbackTop R E r).hom u) = u := by
  change (pullbackTop R E r ≫ pullbackAlg R E r).hom u = u
  rw [← relativeSingularCohomology.map_comp]
  simp only [totalSpaceInv_totalSpaceHom]
  rw [relativeSingularCohomology.map_id]
  rfl

/-- `MMP.Modules.pullbackAlg` is a right inverse of `MMP.Modules.pullbackTop`. -/
@[simp]
lemma pullbackTop_pullbackAlg (u) :
    (pullbackTop R E r).hom ((pullbackAlg R E r).hom u) = u := by
  change (pullbackAlg R E r ≫ pullbackTop R E r).hom u = u
  rw [← relativeSingularCohomology.map_comp]
  simp only [totalSpaceHom_totalSpaceInv]
  rw [relativeSingularCohomology.map_id]
  rfl

/-- A class is a Thom class of `𝐕(ℰ)` iff its pull-back is a Thom class of the topological
bundle `𝐕(ℰ)(ℂ) → X(ℂ)`. -/
theorem isThomClass_iff_isThomClassOfRank
    (u : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
      (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)) :
    IsThomClass R E r u ↔
      ThomClass.IsThomClassOfRank (Fin r → ℂ) (Fibre E r) r ((pullbackTop R E r).hom u) := by
  refine ⟨fun hu x ψ v hv ↦ ?_, fun hu f hf v hv ↦ ?_⟩
  · have e : (totalSpaceHom E r).hom.comp (ThomClass.fibreSimplex (Fin r → ℂ) x ψ v) =
        (⟨fun w ↦ (ψ w).1,
          continuous_subtype_val.comp ψ.continuous⟩ : C(Fin r → ℂ, _)).comp
          (ThomClass.affineSimplex v) := ContinuousMap.ext fun _ ↦ rfl
    rw [relEval_single_map (totalSpaceHom E r) _ _ _
      (by
        rw [e]
        exact eval_single_eq_zero_of_mem_relCoboundaries _ fun t ht ↦
          (isComplexFrame_of_continuousLinearEquiv E x ψ).notMem_range_zeroSection
            (hv.affineSimplex_ne_zero t ht))]
    exact (LinearMap.congr_fun (relEval_congr (by rw [e]) _ _) _).trans
      (hu _ (isComplexFrame_of_continuousLinearEquiv E x ψ) v hv)
  · obtain ⟨x, c, A, hx, h⟩ := hf
    have e : (totalSpaceHom E r).hom.comp
        (ThomClass.fibreSimplex (Fin r → ℂ) x (frameEquiv f x c A hx h) v) =
          f.comp (ThomClass.affineSimplex v) :=
      ContinuousMap.ext fun _ ↦ rfl
    have key := hu x (frameEquiv f x c A hx h) v hv
    rw [relEval_single_map (totalSpaceHom E r) _ _ _ (by
      rw [e]
      exact eval_single_eq_zero_of_mem_relCoboundaries _ fun t ht ↦
        IsComplexFrame.notMem_range_zeroSection ⟨x, c, A, hx, h⟩
          (hv.affineSimplex_ne_zero t ht))] at key
    exact (LinearMap.congr_fun (relEval_congr (by rw [e]) _ _) _).symm.trans key

/-- **Thom's theorem for Stacks vector bundles** (Fulton, §19.1; Milnor–Stasheff, Thm. 10.4):
the vector bundle of a quasi-coherent module, finite locally free of rank `r`, on a scheme over
`ℂ`, regarded as a complex topological vector bundle on `X(ℂ)`, has exactly one Thom class. -/
theorem existsUnique_isThomClass :
    ∃! u : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
      (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ),
      IsThomClass R E r u := by
  obtain ⟨w, hw, hw'⟩ := ThomClass.existsUnique_isThomClassOfRank (R := R) (Fin r → ℂ)
    (Fibre E r) (Module.finrank_fin_fun ℂ)
  refine ⟨(pullbackAlg R E r).hom w, (isThomClass_iff_isThomClassOfRank R E r _).2 ?_,
    fun u hu ↦ ?_⟩
  · rwa [pullbackTop_pullbackAlg]
  · rw [← pullbackAlg_pullbackTop R E r u,
      hw' _ ((isThomClass_iff_isThomClassOfRank R E r u).1 hu)]

/-- **The Thom class** `u_ℰ ∈ H^{2r}(𝐕(ℰ)(ℂ), 𝐕(ℰ)(ℂ) - 0(X(ℂ)); R)` of the vector bundle of a
quasi-coherent module `ℰ`, finite locally free of rank `r`, on a scheme over `ℂ` (Fulton, §19.1):
the unique class satisfying `MMP.Modules.IsThomClass`. -/
def thomClass : cohomologyWithSupports R (ModuleCat.of R R)
    (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
    (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ) :=
  (existsUnique_isThomClass R E r).exists.choose

/-- `MMP.Modules.thomClass` is a Thom class of `𝐕(ℰ)`. -/
lemma isThomClass_thomClass : IsThomClass R E r (thomClass R E r) :=
  (existsUnique_isThomClass R E r).exists.choose_spec

variable {E r R} in
/-- A Thom class of `𝐕(ℰ)` is the Thom class. -/
lemma eq_thomClass {u : cohomologyWithSupports R (ModuleCat.of R R)
    (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
    (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)}
    (hu : IsThomClass R E r u) : u = thomClass R E r :=
  (existsUnique_isThomClass R E r).unique hu (isThomClass_thomClass R E r)

variable {E r R} in
/-- A class is a Thom class of `𝐕(ℰ)` iff it is the Thom class. -/
lemma isThomClass_iff_eq_thomClass {u : cohomologyWithSupports R (ModuleCat.of R R)
    (TopCat.of (UnderlyingSpace ℂ (totalSpace E)))
    (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * r : ℕ)} :
    IsThomClass R E r u ↔ u = thomClass R E r :=
  ⟨eq_thomClass, fun h ↦ h ▸ isThomClass_thomClass R E r⟩

/-- The Thom class of `𝐕(ℰ)` is the Thom class of the complex topological vector bundle
`𝐕(ℰ)(ℂ) → X(ℂ)`: its pull-back along the homeomorphism of total spaces is
`MMP.ThomClass.thomClass` (transported along `H^{2 dim ℂʳ} = H^{2r}`). -/
theorem pullbackTop_thomClass :
    (pullbackTop R E r).hom (thomClass R E r) =
      cast (ThomClass.cohomology_rank_eq R (Fin r → ℂ) (Fibre E r) (Module.finrank_fin_fun ℂ))
        (ThomClass.thomClass R (Fin r → ℂ) (Fibre E r)) :=
  (ThomClass.existsUnique_isThomClassOfRank (R := R) (Fin r → ℂ) (Fibre E r)
    (Module.finrank_fin_fun ℂ)).unique
    ((isThomClass_iff_isThomClassOfRank R E r _).1 (isThomClass_thomClass R E r))
    ((ThomClass.isThomClassOfRank_cast_iff (Module.finrank_fin_fun ℂ) _).2
      (ThomClass.isThomClass_thomClass (Fin r → ℂ) (Fibre E r)))

/-- The Thom class of `𝐕(ℰ)` is the pull-back of the Thom class of the topological bundle
`𝐕(ℰ)(ℂ) → X(ℂ)` along `𝐕(ℰ)(ℂ) ≅ Σ x, π⁻¹(x)`. -/
theorem thomClass_eq_pullbackAlg :
    thomClass R E r = (pullbackAlg R E r).hom
      (cast (ThomClass.cohomology_rank_eq R (Fin r → ℂ) (Fibre E r) (Module.finrank_fin_fun ℂ))
        (ThomClass.thomClass R (Fin r → ℂ) (Fibre E r))) := by
  rw [← pullbackTop_thomClass R E r, pullbackAlg_pullbackTop]

end Topological

end MMP.Modules
