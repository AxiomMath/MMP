module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyAffine
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalBasisSections
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapSections
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# Charts of the complex points of a Stacks vector bundle

Let `X` be a scheme over `ℂ` and `ℰ` a quasi-coherent `𝒪_X`-module, finite locally free of rank
`r`, with vector bundle `π : 𝐕(ℰ) = Spec_X(Sym ℰ) ⟶ X`
(`AlgebraicGeometry.Scheme.Modules.vectorBundle`). A *chart* is an affine open `V ⊆ X` with a
basis `b` of `Γ(ℰ, V)` over `Γ(X, V)`; the charts cover `X`. The basis elements
`bᵢ ∈ Γ(ℰ, V) ⊆ Γ(V, Sym ℰ) = Γ(π⁻¹V, 𝒪)` are regular functions on `π⁻¹V`, and evaluating them
gives coordinates `π⁻¹V(ℂ) → ℂʳ`. These are canonical, so on an overlap the coordinates of two
charts differ by the change-of-basis matrix of the two bases, evaluated at the base point.

The chart map `π⁻¹V(ℂ) → V(ℂ) × ℂʳ`, `p ↦ (π p, (bᵢ(p))ᵢ)`, is a homeomorphism. Its inverse
comes from an explicit isomorphism `π⁻¹V ≅ 𝔸ʳ_V` that pulls the coordinate `Tᵢ` back to `bᵢ`.

## Main definitions

* `MMP.Modules.Chart E r`: the charts `(V, b)` of `ℰ`.
* `MMP.Modules.chartCoordSection c i`: the function `bᵢ ∈ Γ(π⁻¹V, 𝒪_{𝐕(ℰ)})`.
* `MMP.Modules.coord c`: the coordinates `𝐕(ℰ)(ℂ) → ℂʳ` of a chart (`0` off `π⁻¹V(ℂ)`).
* `MMP.Modules.chartIso c`: the isomorphism `π⁻¹V ≅ 𝔸ʳ_V` over `V`.
* `MMP.Modules.chartInv c x hx w`: the point over `x ∈ V(ℂ)` with coordinates `w`.
* `MMP.Modules.chartHomeomorph c`: the homeomorphism `π⁻¹V(ℂ) ≃ₜ V(ℂ) × ℂʳ`.
* `MMP.Modules.transition c c' x`: the transition matrix of two charts at `x`.

## Main results

* `MMP.Modules.exists_chart_mem`: the charts cover `X`.
* `MMP.Modules.continuousOn_coord`: the coordinates are continuous on `π⁻¹V(ℂ)`.
* `MMP.Modules.chartIso_hom_over`, `MMP.Modules.chartIso_hom_appTop_coord`: `chartIso c` lies
  over `V` and pulls `Tᵢ` back to `chartCoordSection c i`.
* `MMP.Modules.coord_eq_transition_mulVec`: `coord c' p = transition c c' (π p) *ᵥ coord c p` on
  `π⁻¹(V ∩ V')(ℂ)`.
* `MMP.Modules.transition_eq_of_basicOpen`: on a basic open `D(a) ⊆ V ∩ V'`, the transition
  matrix is the change-of-basis matrix of `b`, `b'` over `D(a)`, evaluated at the point.
* `MMP.Modules.continuousOn_transition`: the transition matrices are continuous on
  `(V ∩ V')(ℂ)`.

## Implementation notes

`Γ(V, Sym ℰ)` acts on `π⁻¹V` through the open immersion `Spec Γ(V, Sym ℰ) ⟶ 𝐕(ℰ)` of the
relative-spectrum gluing (`specSectionsι`); `π⁻¹V ≅ Spec Γ(V, Sym ℰ)` is
`IsOpenImmersion.isoOfRangeEq`. `bᵢ` enters `Γ(V, Sym ℰ)` as
`Stacks.SymAlgSections.symSectionsRingEquiv (ι bᵢ)`. This is compatible with restriction
(`generator_restrict`) by `Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl`.

`chartIso c` is `π⁻¹V ≅ Spec Γ(V, Sym ℰ)` followed by
`Γ(V, Sym ℰ) ≅ Γ(X, V)[T]` (`Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv`) and by
Mathlib's `AffineSpace.SpecIso` and `AffineSpace.map`. It does not use the existential
`Stacks.Chow.exists_iso_affineSpace_of_mvPolynomialSections`.

The bases do not restrict along `V ∩ V'`, which need not be affine. They restrict to the basic
opens `D(a) ⊆ V ∩ V'` with `a ∈ Γ(X, V)` (`basisBasicOpen`: `Γ(ℰ, D(a))` is the localization of
`Γ(ℰ, V)` at `a`). `transition` is defined without such a choice: its `i`-th column is the
`c'`-coordinate vector of `chartInv c x hx eᵢ`. It agrees with the change-of-basis matrix on
every such `D(a)`.

The total space, projection and algebra sheaf appear through the abbreviations `totalSpace E`,
`proj E` and `symAlg E`. Written out, `Scheme.Modules.vectorBundle X E` takes `E : X.Modules`
where a `SheafOfModules X.ringCatSheaf` is expected. That makes rewriting motives ill-typed at
reducible transparency.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Stacks.AffineAlgebraEquivalence
open scoped Matrix

namespace MMP.Modules

variable {X : Scheme.{0}} (E : X.Modules) [E.IsQuasicoherent]

/-- An affine open, as an open with an `IsAffineOpen` proof of the right type. -/
lemma isAffineOpen_affineOpens (V : X.affineOpens) : IsAffineOpen V.1 := V.2

/-- The total space `𝐕(ℰ) = Spec_X(Sym ℰ)` of the vector bundle of `ℰ`. -/
abbrev totalSpace : Scheme.{0} := Scheme.Modules.vectorBundle X E

/-- The projection `π : 𝐕(ℰ) ⟶ X`. -/
abbrev proj : totalSpace E ⟶ X := Scheme.Modules.vectorBundleToBase X E

/-- `Sym(ℰ)`, as a sheaf of `𝒪_X`-algebras. -/
abbrev symAlg : Stacks.RelativeSpec.AlgebraSheaf X := Scheme.Modules.symmetricAlgebraSheaf X E

/-- The total space of the vector bundle `𝐕(ℰ)` lies over `X` through its projection. -/
instance : (totalSpace E).CanonicallyOver X where
  hom := proj E

/-- The sections of `Sym(ℰ)` over `V`. -/
abbrev symSections (V : X.Opens) : CommRingCat.{0} :=
  (symAlg E).right.obj.obj (op V)

/-- The open immersion `Spec Γ(V, Sym ℰ) ⟶ 𝐕(ℰ)` onto the part of `𝐕(ℰ)` over `V`. -/
def specSectionsι (V : X.affineOpens) :
    Spec (symSections E V.1) ⟶ totalSpace E :=
  colimit.ι (relativeSpecGluingData (symAlg E)).functor V

/-- The map `Spec Γ(V, Sym ℰ) ⟶ 𝐕(ℰ)` is an open immersion. -/
instance (V : X.affineOpens) : IsOpenImmersion (specSectionsι E V) :=
  (relativeSpecGluingData (symAlg E)).cover.map_prop V

/-- The composite `Spec Γ(V, Sym ℰ) ⟶ 𝐕(ℰ) ⟶ X` is `Spec` of the structure map
`Γ(X, V) → Γ(V, Sym ℰ)` followed by `Spec Γ(X, V) ≅ V ⊆ X`. -/
lemma specSectionsι_toBase (V : X.affineOpens) :
    specSectionsι E V ≫ proj E =
      Spec.map ((symAlg E).hom.hom.app (op V.1)) ≫
        (isAffineOpen_affineOpens V).isoSpec.inv ≫ V.1.ι :=
  ((relativeSpecGluingData (symAlg E)).ι_toBase V).trans
    (Category.assoc _ _ _)

/-- The image of `Spec Γ(V, Sym ℰ) ⟶ 𝐕(ℰ)` is `π⁻¹(V)`. -/
lemma opensRange_specSectionsι (V : X.affineOpens) :
    (specSectionsι E V).opensRange = proj E ⁻¹ᵁ V.1 := by
  have h := (relativeSpecGluingData
    (symAlg E)).preimage_toBase_eq_range_ι V
  refine Opens.ext ?_
  change Set.range (specSectionsι E V) = _
  refine h.symm.trans ?_
  change _ ⁻¹' Set.range V.1.ι = _
  rw [Scheme.Opens.range_ι]
  rfl

/-- For affine opens `W ⊆ V`, the open immersion of `Spec Γ(W, Sym ℰ)` factors through that of
`Spec Γ(V, Sym ℰ)` by `Spec` of the restriction map. -/
lemma specMap_secRes_specSectionsι {W V : X.affineOpens} (h : W ⟶ V) :
    Spec.map (secRes (symAlg E) h) ≫ specSectionsι E V =
      specSectionsι E W :=
  colimit.w (relativeSpecGluingData (symAlg E)).functor h

/-- The part `π⁻¹(V)` of `𝐕(ℰ)` over `V` is `Spec Γ(V, Sym ℰ)`. -/
def specIso (V : X.affineOpens) :
    (proj E ⁻¹ᵁ V.1).toScheme ≅ Spec (symSections E V.1) :=
  IsOpenImmersion.isoOfRangeEq (proj E ⁻¹ᵁ V.1).ι
    (specSectionsι E V) (by
      rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, opensRange_specSectionsι])

/-- The isomorphism `π⁻¹(V) ≅ Spec Γ(V, Sym ℰ)` is compatible with the inclusions into `𝐕(ℰ)`. -/
@[reassoc (attr := simp)]
lemma specIso_hom_specSectionsι (V : X.affineOpens) :
    (specIso E V).hom ≫ specSectionsι E V = (proj E ⁻¹ᵁ V.1).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The identification `Γ(V, Sym ℰ) ≅ Γ(π⁻¹V, 𝒪)` of the sections of `Sym(ℰ)` over an affine open
`V` with the functions on the part of `𝐕(ℰ)` over `V`. -/
def totalSections (V : X.affineOpens) :
    symSections E V.1 ⟶ Γ(totalSpace E,
      proj E ⁻¹ᵁ V.1) :=
  (Scheme.ΓSpecIso _).inv ≫ (specIso E V).hom.appTop ≫
    (proj E ⁻¹ᵁ V.1).topIso.hom

/-- The degree-one inclusion `Γ(ℰ, V) → Γ(V, Sym ℰ)` over an affine open `V`. -/
def generator {V : X.Opens} (hV : IsAffineOpen V) : Γ(E, V) →+ symSections E V :=
  (Stacks.SymAlgSections.symSectionsRingEquiv E hV).toAddMonoidHom.comp
    (SymmetricAlgebra.ι Γ(X, V) Γ(E, V)).toAddMonoidHom

/-- `generator E hV m` is the image of `m ∈ Sym¹ Γ(ℰ, V)` under
`Sym Γ(ℰ, V) ≃ Γ(V, Sym ℰ)`. -/
lemma generator_apply {V : X.Opens} (hV : IsAffineOpen V) (m : Γ(E, V)) :
    generator E hV m =
      Stacks.SymAlgSections.symSectionsRingEquiv E hV (SymmetricAlgebra.ι Γ(X, V) Γ(E, V) m) :=
  rfl

/-- The inclusion `Γ(ℰ, V) → Γ(V, Sym ℰ)` is `Γ(X, V)`-linear: `a • m` maps to the product of
the image of `a` and that of `m`. -/
lemma generator_smul {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (m : Γ(E, V)) :
    generator E hV (a • m) =
      ((symAlg E).hom.hom.app (op V)).hom a *
        generator E hV m := by
  rw [generator_apply, generator_apply, map_smul, Algebra.smul_def, map_mul,
    Stacks.SymAlgSections.symSectionsRingEquiv_algebraMap]

/-- The inclusion `Γ(ℰ, V) → Γ(V, Sym ℰ)` commutes with restriction to an affine open `W ⊆ V`. -/
lemma generator_restrict {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h : W ≤ V) (m : Γ(E, V)) :
    ((symAlg E).right.obj.map (homOfLE h).op).hom
        (generator E hV m) =
      generator E hW (E.presheaf.map (homOfLE h).op m) := by
  rw [generator_apply, generator_apply,
    Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl,
    Stacks.SymAlgSections.symSectionsRingEquiv_ι_eq_ungradedIncl]
  refine (SheafOfModules.GradedAlgebra.ungradedIncl_naturality _ _ 1 _).trans ?_
  congr 1
  exact (PresheafOfModules.naturality_apply
    (Scheme.Modules.symmetricAlgebraGen X E).val (homOfLE h).op m).symm

variable (r : ℕ)

/-- A *chart* of `ℰ`: an affine open `V` of `X` with a basis of `Γ(ℰ, V)` over `Γ(X, V)`
indexed by `Fin r`. -/
abbrev Chart := Σ V : X.affineOpens, Module.Basis (Fin r) Γ(X, V.1) Γ(E, V.1)

variable {E r}

/-- The charts of a finite locally free sheaf of rank `r` cover `X`, inside any open
neighbourhood of a point. -/
lemma exists_chart_mem_le
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] {x : X}
    {W : X.Opens} (hxW : x ∈ W) : ∃ c : Chart E r, x ∈ c.1.1 ∧ c.1.1 ≤ W := by
  obtain ⟨V, hV, hxV, hVW, ⟨b⟩⟩ := Stacks.Chow.exists_isAffineOpen_basis_sections_le E r hxW
  exact ⟨⟨⟨V, hV⟩, b⟩, hxV, hVW⟩

variable (r) in
/-- The charts of a finite locally free sheaf of rank `r` cover `X`. -/
lemma exists_chart_mem
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] (x : X) :
    ∃ c : Chart E r, x ∈ c.1.1 := by
  obtain ⟨c, hc, -⟩ :=
    exists_chart_mem_le (E := E) (r := r) (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨c, hc⟩

/-- The `i`-th coordinate function of a chart `(V, b)`: the basis element `bᵢ ∈ Γ(ℰ, V)`, as a
function on `π⁻¹(V)` through `Γ(ℰ, V) → Γ(V, Sym ℰ) = Γ(π⁻¹V, 𝒪)`. -/
def chartCoordSection (c : Chart E r) (i : Fin r) :
    Γ(totalSpace E, proj E ⁻¹ᵁ c.1.1) :=
  totalSections E c.1 (generator E (isAffineOpen_affineOpens c.1) (c.2 i))

/-- The polynomial ring `Γ(X, V)[T₁, …, Tᵣ]` is `Γ(V, Sym ℰ)`, sending `Tᵢ` to `bᵢ`. -/
def polyIso (c : Chart E r) :
    CommRingCat.of (MvPolynomial (Fin r) Γ(X, c.1.1)) ≅ symSections E c.1.1 :=
  (Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E (isAffineOpen_affineOpens c.1)
    c.2).symm.toCommRingCatIso

/-- `polyIso c` sends the variable `Tᵢ` to `bᵢ ∈ Γ(V, Sym ℰ)`. -/
lemma polyIso_hom_X (c : Chart E r) (i : Fin r) :
    (polyIso c).hom (MvPolynomial.X i) = generator E (isAffineOpen_affineOpens c.1) (c.2 i) := by
  change (Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E
    (isAffineOpen_affineOpens c.1) c.2).symm
    (MvPolynomial.X i) = _
  change Stacks.SymAlgSections.symSectionsRingEquiv E (isAffineOpen_affineOpens c.1)
    ((SymmetricAlgebra.equivMvPolynomial c.2).symm (MvPolynomial.X i)) = _
  rw [SymmetricAlgebra.equivMvPolynomial_symm_X]
  rfl

/-- `polyIso c` sends a constant `a ∈ Γ(X, V)` to its image under the structure map
`Γ(X, V) → Γ(V, Sym ℰ)`. -/
lemma polyIso_hom_C (c : Chart E r) (a : Γ(X, c.1.1)) :
    (polyIso c).hom (MvPolynomial.C a) =
      ((symAlg E).hom.hom.app (op c.1.1)).hom a := by
  change (Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E
    (isAffineOpen_affineOpens c.1) c.2).symm
    (MvPolynomial.C a) = _
  rw [RingEquiv.symm_apply_eq]
  exact (Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv_app E
    (isAffineOpen_affineOpens c.1) c.2 a).symm

/-- `𝔸ʳ` over `Spec Γ(X, V)` is `𝔸ʳ` over `V`. -/
def affineSpaceIsoSpec (V : X.affineOpens) (r : ℕ) :
    𝔸(Fin r; Spec Γ(X, V.1)) ≅ 𝔸(Fin r; V.1.toScheme) where
  hom := AffineSpace.map (Fin r) (isAffineOpen_affineOpens V).isoSpec.inv
  inv := AffineSpace.map (Fin r) (isAffineOpen_affineOpens V).isoSpec.hom
  hom_inv_id := by rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id]
  inv_hom_id := by rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id]

/-- **The chart isomorphism `π⁻¹(V) ≅ 𝔸ʳ_V`** of a chart `(V, b)`: the composite of
`π⁻¹V ≅ Spec Γ(V, Sym ℰ)`, of `Γ(V, Sym ℰ) ≅ Γ(X, V)[T₁, …, Tᵣ]` (`Tᵢ ↦ bᵢ`) and of
`Spec Γ(X, V)[T₁, …, Tᵣ] ≅ 𝔸ʳ_V`. -/
def chartIso (c : Chart E r) :
    (proj E ⁻¹ᵁ c.1.1).toScheme ≅ 𝔸(Fin r; c.1.1.toScheme) :=
  specIso E c.1 ≪≫ Scheme.Spec.mapIso (polyIso c).op ≪≫
    (AffineSpace.SpecIso (Fin r) Γ(X, c.1.1)).symm ≪≫ affineSpaceIsoSpec c.1 r

/-- The chart isomorphism lies over `V`. -/
@[reassoc]
lemma chartIso_hom_over_ι (c : Chart E r) :
    (chartIso c).hom ≫ 𝔸(Fin r; c.1.1.toScheme) ↘ c.1.1.toScheme ≫ c.1.1.ι =
      (proj E ⁻¹ᵁ c.1.1).ι ≫
        proj E := by
  have hC : CommRingCat.ofHom (MvPolynomial.C (σ := Fin r) (R := Γ(X, c.1.1))) ≫
      (polyIso c).hom = (symAlg E).hom.hom.app (op c.1.1) := by
    ext a
    exact polyIso_hom_C c a
  simp only [chartIso, affineSpaceIsoSpec, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc,
    AffineSpace.map_over_assoc, AffineSpace.SpecIso_inv_over_assoc]
  rw [← Spec.map_comp_assoc, hC, ← specIso_hom_specSectionsι_assoc, specSectionsι_toBase]
  rfl

/-- The chart isomorphism lies over `V`, as the restriction of `π` to `π⁻¹V`. -/
lemma chartIso_hom_over (c : Chart E r) :
    (chartIso c).hom ≫ 𝔸(Fin r; c.1.1.toScheme) ↘ c.1.1.toScheme =
      proj E ∣_ c.1.1 := by
  rw [← cancel_mono c.1.1.ι, Category.assoc, chartIso_hom_over_ι, morphismRestrict_ι]

/-- **The chart isomorphism pulls the coordinate `Tᵢ` of `𝔸ʳ_V` back to the coordinate function
`bᵢ`** (`chartCoordSection`). -/
lemma chartIso_hom_appTop_coord (c : Chart E r) (i : Fin r) :
    (chartIso c).hom.appTop (AffineSpace.coord c.1.1.toScheme i) =
      (proj E ⁻¹ᵁ c.1.1).topIso.inv (chartCoordSection c i) := by
  simp only [chartCoordSection, totalSections, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
  simp only [chartIso, affineSpaceIsoSpec, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.map_appTop_coord]
  have h1 : (AffineSpace.SpecIso (Fin r) Γ(X, c.1.1)).inv.appTop (AffineSpace.coord _ i) =
      (Scheme.ΓSpecIso _).inv (MvPolynomial.X i) := AffineSpace.SpecIso_inv_appTop_coord _ _
  have h2 : (Spec.map (polyIso c).hom).appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X i)) =
      (Scheme.ΓSpecIso _).inv ((polyIso c).hom (MvPolynomial.X i)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rw [h1, h2, polyIso_hom_X]

/-! ### Points -/

section Points

open UnderlyingSpace

/-- The projection of `𝐕(ℰ)` lies over every base of `X`. -/
instance {S : Scheme.{0}} [X.Over S] : (proj E).IsOver S :=
  ⟨rfl⟩

/-- A morphism `T ⟶ Y` landing in an open `U ⊆ Y`, as a morphism to the open subscheme `U`. -/
def openLift {T Y : Scheme.{0}} (U : Y.Opens) (f : T ⟶ Y) (hf : ⊤ ≤ f ⁻¹ᵁ U) :
    T ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι f (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hf (show z ∈ (⊤ : T.Opens) from trivial))

/-- The lift `openLift U f hf` composed with the inclusion `U ⟶ Y` is `f`. -/
@[reassoc (attr := simp)]
lemma openLift_ι {T Y : Scheme.{0}} (U : Y.Opens) (f : T ⟶ Y) (hf : ⊤ ≤ f ⁻¹ᵁ U) :
    openLift U f hf ≫ U.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/-- A section over `U`, pulled back along `f ≫ U.ι`, is the section of `Γ(U, ⊤)` it corresponds
to, pulled back along `f`. -/
lemma appLE_comp_ι_topIso_hom {T Y : Scheme.{0}} (U : Y.Opens) (f : T ⟶ U.toScheme)
    (h : ⊤ ≤ (f ≫ U.ι) ⁻¹ᵁ U) (s : Γ(U.toScheme, ⊤)) :
    (f ≫ U.ι).appLE U ⊤ h (U.topIso.hom s) = f.appTop s := by
  rw [← Scheme.Hom.appLE_comp_appLE f U.ι U ⊤ ⊤ U.ι_preimage_self.ge
    (Scheme.Hom.preimage_top f).ge, CommRingCat.comp_apply, UnderlyingSpace.appLE_top_top]
  congr 1
  have key : ∀ {A B : Y.Opens} (i : op A ⟶ op B) (j : op B ⟶ op A) (t : Γ(Y, A)),
      Y.presheaf.map j (Y.presheaf.map i t) = t := by
    intro A B i j t
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (i ≫ j) (𝟙 _),
      CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_hom]
  exact key _ _ s

omit [E.IsQuasicoherent] in
/-- On global sections, `Spec.map φ` acts as `φ` under the identifications `Γ(Spec R, ⊤) ≅ R`. -/
lemma specMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{0}} (φ : R ⟶ S) (a : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv a) = (Scheme.ΓSpecIso S).inv (φ a) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

omit [E.IsQuasicoherent] in
/-- For an affine open `V` and `φ : Γ(X, V) ⟶ R`, the map `Spec R ⟶ Spec Γ(X, V) ≅ V` acts on
global sections as `φ`. -/
lemma appTop_specMap_isoSpec_inv {R : CommRingCat.{0}} {V : X.Opens} (hV : IsAffineOpen V)
    (φ : Γ(X, V) ⟶ R) (a : Γ(X, V)) :
    (Spec.map φ ≫ hV.isoSpec.inv).appTop (V.topIso.inv a) = (Scheme.ΓSpecIso R).inv (φ a) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_inv_appTop,
    CommRingCat.comp_apply, Iso.inv_hom_id_apply, specMap_appTop_ΓSpecIso_inv]

variable (E) [X.Over (Spec (.of ℂ))]

/-- A point of `π⁻¹V(ℂ)` as a point of `Spec Γ(V, Sym ℰ)`. -/
def liftSpec (V : X.affineOpens) (p : UnderlyingSpace ℂ (totalSpace E))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ V.1)) :
    Spec (.of ℂ) ⟶ Spec (symSections E V.1) :=
  IsOpenImmersion.lift (specSectionsι E V) p.toHom (by
    rintro _ ⟨z, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, opensRange_specSectionsι]
    exact hp (show z ∈ (⊤ : (Spec (.of ℂ)).Opens) from trivial))

/-- The lift `liftSpec E V p hp` composed with `Spec Γ(V, Sym ℰ) ⟶ 𝐕(ℰ)` is the point `p`. -/
@[reassoc (attr := simp)]
lemma liftSpec_ι (V : X.affineOpens) (p : UnderlyingSpace ℂ (totalSpace E))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ V.1)) :
    liftSpec E V p hp ≫ specSectionsι E V = p.toHom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The value at `p ∈ π⁻¹V(ℂ)` of the function on `π⁻¹V` given by a section of `Sym(ℰ)` over
`V` is its image under the ring map `Γ(V, Sym ℰ) → ℂ` of `p`. -/
lemma eval_totalSections (V : X.affineOpens)
    (p : UnderlyingSpace ℂ (totalSpace E))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ V.1))
    (a : symSections E V.1) :
    eval p hp (totalSections E V a) =
      (Scheme.ΓSpecIso (.of ℂ)).hom ((liftSpec E V p hp).appTop ((Scheme.ΓSpecIso _).inv a)) := by
  set U := proj E ⁻¹ᵁ V.1
  set f := openLift U p.toHom hp
  have hlift : f ≫ (specIso E V).hom = liftSpec E V p hp := by
    rw [← cancel_mono (specSectionsι E V), Category.assoc, specIso_hom_specSectionsι, liftSpec_ι,
      openLift_ι]
  have key : ∀ (g : Spec (.of ℂ) ⟶ totalSpace E) (hg : ⊤ ≤ g ⁻¹ᵁ U)
      (t : Γ(U.toScheme, ⊤)), g = f ≫ U.ι → g.appLE U ⊤ hg (U.topIso.hom t) = f.appTop t := by
    rintro _ hg t rfl
    exact appLE_comp_ι_topIso_hom U f hg t
  simp only [UnderlyingSpace.eval, totalSections, CommRingCat.comp_apply]
  rw [key p.toHom hp _ (openLift_ι U p.toHom hp).symm, ← hlift, Scheme.Hom.comp_appTop]
  rfl

/-- For affine opens `W ⊆ V` and `p ∈ π⁻¹W(ℂ)`, the lift of `p` to `Spec Γ(V, Sym ℰ)` is its
lift to `Spec Γ(W, Sym ℰ)` followed by `Spec` of the restriction map. -/
lemma liftSpec_restrict {W V : X.affineOpens} (h : W ≤ V)
    (p : UnderlyingSpace ℂ (totalSpace E))
    (hpW : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ W.1))
    (hpV : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ V.1)) :
    liftSpec E W p hpW ≫ Spec.map (secRes (symAlg E) (homOfLE h)) =
      liftSpec E V p hpV := by
  rw [← cancel_mono (specSectionsι E V), Category.assoc, specMap_secRes_specSectionsι,
    liftSpec_ι, liftSpec_ι]

/-- Evaluation at points is compatible with restriction of sections of `Sym(ℰ)`. -/
lemma eval_totalSections_restrict {W V : X.affineOpens} (h : W ≤ V)
    (p : UnderlyingSpace ℂ (totalSpace E))
    (hpW : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ W.1))
    (hpV : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ V.1))
    (a : symSections E V.1) :
    eval p hpW (totalSections E W
        (secRes (symAlg E) (homOfLE h) a)) =
      eval p hpV (totalSections E V a) := by
  rw [eval_totalSections, eval_totalSections, ← liftSpec_restrict E h p hpW hpV,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, specMap_appTop_ΓSpecIso_inv]

/-- A section of `𝒪_X` over `V`, seen in `Γ(V, Sym ℰ)`, takes at `p` its value at `π(p)`. -/
lemma eval_totalSections_structureMap (V : X.affineOpens)
    (p : UnderlyingSpace ℂ (totalSpace E))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ V.1))
    (hx : ⊤ ≤ (mapFun (proj E) p).toHom ⁻¹ᵁ V.1)
    (a : Γ(X, V.1)) :
    eval p hp (totalSections E V
        (((symAlg E).hom.hom.app (op V.1)).hom a)) =
      eval (mapFun (proj E) p) hx a := by
  set g := liftSpec E V p hp ≫
    Spec.map ((symAlg E).hom.hom.app (op V.1)) ≫
      (isAffineOpen_affineOpens V).isoSpec.inv
  have hg : (mapFun (proj E) p).toHom = g ≫ V.1.ι := by
    rw [toHom_mapFun, ← liftSpec_ι E V p hp, Category.assoc, specSectionsι_toBase]
    simp only [g, Category.assoc]
    rfl
  have key : ∀ (k : Spec (.of ℂ) ⟶ X) (hk : ⊤ ≤ k ⁻¹ᵁ V.1)
      (t : Γ(V.1.toScheme, ⊤)), k = g ≫ V.1.ι → k.appLE V.1 ⊤ hk (V.1.topIso.hom t) =
        g.appTop t := by
    rintro _ hk t rfl
    exact appLE_comp_ι_topIso_hom V.1 g hk t
  rw [eval_totalSections]
  simp only [UnderlyingSpace.eval]
  have hval : (liftSpec E V p hp ≫ Spec.map ((symAlg E).hom.hom.app (op V.1)) ≫
      (isAffineOpen_affineOpens V).isoSpec.inv).appTop (V.1.topIso.inv a) =
      (liftSpec E V p hp).appTop ((Scheme.ΓSpecIso _).inv ((symAlg E).hom.hom.app (op V.1) a)) := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    congr 1
    exact appTop_specMap_isoSpec_inv (isAffineOpen_affineOpens V) _ a
  conv_rhs => rw [← Iso.inv_hom_id_apply V.1.topIso a, key _ hx _ hg]
  rw [hval]

variable {E}

/-- The coordinates `p ↦ (bᵢ(p))ᵢ ∈ ℂʳ` of a chart `(V, b)`, on the points of `π⁻¹V(ℂ)`
(and `0` elsewhere). -/
def coord (c : Chart E r) (p : UnderlyingSpace ℂ (totalSpace E)) :
    Fin r → ℂ :=
  fun i ↦ evalExt (proj E ⁻¹ᵁ c.1.1) (chartCoordSection c i) p

/-- On `π⁻¹V(ℂ)`, the `i`-th coordinate of a chart is the value of `bᵢ` at the point. -/
lemma coord_apply (c : Chart E r) {p : UnderlyingSpace ℂ (totalSpace E)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) (i : Fin r) :
    coord c p i = eval p hp (chartCoordSection c i) :=
  evalExt_of_le _ hp

/-- The coordinates of a chart are continuous on `π⁻¹V(ℂ)`. -/
lemma continuousOn_coord (c : Chart E r) :
    ContinuousOn (coord c)
      {p : UnderlyingSpace ℂ (totalSpace E) |
        ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)} :=
  continuousOn_pi.mpr fun _ ↦ continuousOn_evalExt _ _

end Points

/-! ### The chart homeomorphisms -/

section ChartHomeomorph

open UnderlyingSpace

omit [E.IsQuasicoherent] in
/-- The value at `p = f ≫ ι_U` of the section of `Γ(Y, U)` corresponding to `t ∈ Γ(U, ⊤)`. -/
lemma eval_topIso_hom {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] (U : Y.Opens)
    (p : UnderlyingSpace ℂ Y) (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U) (f : Spec (.of ℂ) ⟶ U.toScheme)
    (hf : f ≫ U.ι = p.toHom) (t : Γ(U.toScheme, ⊤)) :
    eval p hp (U.topIso.hom t) = (Scheme.ΓSpecIso (.of ℂ)).hom (f.appTop t) := by
  have key : ∀ (g : Spec (.of ℂ) ⟶ Y) (hg : ⊤ ≤ g ⁻¹ᵁ U), g = f ≫ U.ι →
      g.appLE U ⊤ hg (U.topIso.hom t) = f.appTop t := by
    rintro _ hg rfl
    exact appLE_comp_ι_topIso_hom U f hg t
  simp only [UnderlyingSpace.eval]
  rw [key p.toHom hp hf.symm]

omit [E.IsQuasicoherent] in
/-- For an isomorphism of schemes `e : A ≅ B`, pulling a global section of `B` back along
`e.hom` and then along `e.inv` returns it. -/
lemma appTop_inv_hom_apply {A B : Scheme.{0}} (e : A ≅ B) (y : Γ(B, ⊤)) :
    e.inv.appTop (e.hom.appTop y) = y := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop,
    CommRingCat.id_apply]

/-- The coordinate function `bᵢ` is the pullback of the coordinate `Tᵢ` of `𝔸ʳ_V` along the
chart isomorphism. -/
lemma chartCoordSection_eq (c : Chart E r) (i : Fin r) :
    chartCoordSection c i = (proj E ⁻¹ᵁ c.1.1).topIso.hom
      ((chartIso c).hom.appTop (AffineSpace.coord c.1.1.toScheme i)) := by
  rw [chartIso_hom_appTop_coord, Iso.inv_hom_id_apply]

/-- The inverse chart isomorphism `𝔸ʳ_V ≅ π⁻¹(V)`, followed by `π`, is the projection of
`𝔸ʳ_V` to `V ⊆ X`. -/
@[reassoc]
lemma chartIso_inv_ι_proj (c : Chart E r) :
    (chartIso c).inv ≫ (proj E ⁻¹ᵁ c.1.1).ι ≫ proj E =
      𝔸(Fin r; c.1.1.toScheme) ↘ c.1.1.toScheme ≫ c.1.1.ι := by
  rw [← chartIso_hom_over_ι, Iso.inv_hom_id_assoc]

variable [X.Over (Spec (.of ℂ))]

/-- The map `𝔸ʳ_V ≅ π⁻¹(V) ⟶ 𝐕(ℰ)` is a morphism over `Spec ℂ`. -/
instance (c : Chart E r) : ((chartIso c).inv ≫ (proj E ⁻¹ᵁ c.1.1).ι).IsOver (Spec (.of ℂ)) := by
  constructor
  change ((chartIso c).inv ≫ (proj E ⁻¹ᵁ c.1.1).ι) ≫ proj E ≫ X ↘ Spec (.of ℂ) =
    𝔸(Fin r; c.1.1.toScheme) ↘ c.1.1.toScheme ≫ c.1.1.ι ≫ X ↘ Spec (.of ℂ)
  rw [Category.assoc, chartIso_inv_ι_proj_assoc]

/-- The point of `𝔸ʳ_V(ℂ)` over `x ∈ V(ℂ)` with coordinates `w`. -/
def affinePoint (c : Chart E r)
    (xw : {x : UnderlyingSpace ℂ X // ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1} × (Fin r → ℂ)) :
    UnderlyingSpace ℂ 𝔸(Fin r; c.1.1.toScheme) :=
  ⟨AffineSpace.homOfVector (openLift c.1.1 xw.1.1.toHom xw.1.2)
      (fun i ↦ (Scheme.ΓSpecIso (.of ℂ)).inv (xw.2 i)), by
    change _ ≫ 𝔸(Fin r; c.1.1.toScheme) ↘ c.1.1.toScheme ≫ c.1.1.ι ≫ X ↘ Spec (.of ℂ) = _
    rw [AffineSpace.homOfVector_over_assoc, openLift_ι_assoc, xw.1.1.toHom_comp_over]⟩

/-- **The point of `𝐕(ℰ)(ℂ)` over `x ∈ V(ℂ)` with coordinates `w`** in the chart `c = (V, b)`. -/
def chartInv (c : Chart E r) (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1)
    (w : Fin r → ℂ) : UnderlyingSpace ℂ (totalSpace E) :=
  mapFun ((chartIso c).inv ≫ (proj E ⁻¹ᵁ c.1.1).ι) (affinePoint c (⟨x, hx⟩, w))

/-- The point `chartInv c x hx w`, composed with `π`, is `x`, as morphisms from `Spec ℂ`. -/
lemma toHom_chartInv_proj (c : Chart E r) (x : UnderlyingSpace ℂ X)
    (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1) (w : Fin r → ℂ) :
    (chartInv c x hx w).toHom ≫ proj E = x.toHom := by
  change (AffineSpace.homOfVector _ _ ≫ (chartIso c).inv ≫ (proj E ⁻¹ᵁ c.1.1).ι) ≫ proj E = _
  rw [Category.assoc, Category.assoc, chartIso_inv_ι_proj, AffineSpace.homOfVector_over_assoc,
    openLift_ι]

/-- The point `chartInv c x hx w` lies over `x`. -/
lemma mapFun_proj_chartInv (c : Chart E r) (x : UnderlyingSpace ℂ X)
    (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1) (w : Fin r → ℂ) :
    mapFun (proj E) (chartInv c x hx w) = x :=
  UnderlyingSpace.ext (toHom_chartInv_proj c x hx w)

/-- The point `chartInv c x hx w` lies in `π⁻¹V(ℂ)`. -/
lemma chartInv_mem (c : Chart E r) (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1)
    (w : Fin r → ℂ) : ⊤ ≤ (chartInv c x hx w).toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) := by
  intro z hz
  change proj E ((chartInv c x hx w).toHom z) ∈ c.1.1
  rw [← Scheme.Hom.comp_apply, toHom_chartInv_proj]
  exact hx hz

/-- The point `chartInv c x hx w` has coordinates `w` in the chart `c`. -/
lemma coord_chartInv (c : Chart E r) (x : UnderlyingSpace ℂ X) (hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1)
    (w : Fin r → ℂ) : coord c (chartInv c x hx w) = w := by
  funext i
  rw [coord_apply c (chartInv_mem c x hx w), chartCoordSection_eq,
    eval_topIso_hom _ _ _ ((affinePoint c (⟨x, hx⟩, w)).toHom ≫ (chartIso c).inv)
      (Category.assoc _ _ _), Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    appTop_inv_hom_apply]
  change (Scheme.ΓSpecIso (.of ℂ)).hom ((AffineSpace.homOfVector _ _).appTop _) = _
  rw [AffineSpace.homOfVector_appTop_coord, Iso.inv_hom_id_apply]

/-- `π(p) ∈ V(ℂ)` for `p ∈ π⁻¹V(ℂ)`. -/
lemma mapFun_proj_mem {V : X.Opens} {p : UnderlyingSpace ℂ (totalSpace E)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ V)) : ⊤ ≤ (mapFun (proj E) p).toHom ⁻¹ᵁ V :=
  hp

/-- A point of `π⁻¹V(ℂ)` is the point of the chart over its image with its coordinates. -/
lemma chartInv_mapFun_proj_coord (c : Chart E r) (p : UnderlyingSpace ℂ (totalSpace E))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) :
    chartInv c (mapFun (proj E) p) (mapFun_proj_mem hp) (coord c p) = p := by
  set f := openLift (proj E ⁻¹ᵁ c.1.1) p.toHom hp
  have hpt : AffineSpace.homOfVector (openLift c.1.1 (mapFun (proj E) p).toHom
      (mapFun_proj_mem hp))
      (fun i ↦ (Scheme.ΓSpecIso (.of ℂ)).inv (coord c p i)) = f ≫ (chartIso c).hom := by
    refine AffineSpace.hom_ext ?_ fun i ↦ ?_
    · rw [AffineSpace.homOfVector_over, ← cancel_mono c.1.1.ι, openLift_ι]
      simp only [Category.assoc]
      rw [chartIso_hom_over_ι, openLift_ι_assoc, toHom_mapFun]
    · rw [AffineSpace.homOfVector_appTop_coord, coord_apply c hp, chartCoordSection_eq,
        eval_topIso_hom _ p hp f (openLift_ι _ _ _), Iso.hom_inv_id_apply,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  refine UnderlyingSpace.ext ?_
  change AffineSpace.homOfVector _ _ ≫ (chartIso c).inv ≫ (proj E ⁻¹ᵁ c.1.1).ι = _
  rw [hpt, Category.assoc, Iso.hom_inv_id_assoc, openLift_ι]

omit [E.IsQuasicoherent] [X.Over (Spec (.of ℂ))] in
/-- The global sections of `𝔸ʳ_S`, for `S` affine, are generated by those of `S` and the
coordinates. -/
lemma closure_range_affineSpace_eq_top (S : Scheme.{0}) [IsAffine S] (n : ℕ) :
    Subring.closure (Set.range (𝔸(Fin n; S) ↘ S).appTop ∪
      Set.range (AffineSpace.coord S)) = ⊤ := by
  refine eq_top_iff.2 fun t _ ↦ ?_
  obtain ⟨q, rfl⟩ : ∃ q, (AffineSpace.isoOfIsAffine (Fin n) S).hom.appTop q = t :=
    ⟨(AffineSpace.isoOfIsAffine (Fin n) S).inv.appTop t,
      appTop_inv_hom_apply (AffineSpace.isoOfIsAffine (Fin n) S).symm t⟩
  rw [AffineSpace.isoOfIsAffine_hom_appTop, CommRingCat.comp_apply]
  generalize (Scheme.ΓSpecIso _).hom q = q
  induction q using MvPolynomial.induction_on with
  | C a => exact Subring.subset_closure (.inl ⟨a, by simp⟩)
  | add q q' hq hq' => simpa using Subring.add_mem _ hq hq'
  | mul_X q i hq => simpa using Subring.mul_mem _ hq (Subring.subset_closure (.inr ⟨i, rfl⟩))

omit [E.IsQuasicoherent] [X.Over (Spec (.of ℂ))] in
/-- The value of a global section `a` of `T` at the image `f(p)` of a `ℂ`-point is the value of
its pullback along `f` at `p`. -/
lemma evalTop_mapFun {S T : Scheme.{0}} [S.Over (Spec (.of ℂ))] [T.Over (Spec (.of ℂ))]
    (f : S ⟶ T) [f.IsOver (Spec (.of ℂ))] (p : UnderlyingSpace ℂ S) (a : Γ(T, ⊤)) :
    evalTop (mapFun f p) a = evalTop p (f.appTop a) := by
  rw [evalTop_eq, evalTop_eq, toHom_mapFun, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

omit [E.IsQuasicoherent] [X.Over (Spec (.of ℂ))] in
/-- For `S` affine over `ℂ`, the classical topology on `𝔸ʳ_S(ℂ)` is induced by the projection to
`S(ℂ)` and the coordinates. -/
lemma isInducing_affineSpace (S : Scheme.{0}) [S.Over (Spec (.of ℂ))] [IsAffine S] (n : ℕ) :
    IsInducing fun p : UnderlyingSpace ℂ 𝔸(Fin n; S) ↦
      (mapFun (𝔸(Fin n; S) ↘ S) p, fun i ↦ evalTop p (AffineSpace.coord S i)) := by
  let y : Γ(S, ⊤) ⊕ Fin n → Γ(𝔸(Fin n; S), ⊤) :=
    Sum.elim (𝔸(Fin n; S) ↘ S).appTop (AffineSpace.coord S)
  have hy : Subring.closure (Set.range (structureRingHom ℂ 𝔸(Fin n; S)) ∪ Set.range y) = ⊤ := by
    refine eq_top_iff.2 ((closure_range_affineSpace_eq_top S n).symm.le.trans
      (Subring.closure_mono ?_))
    rintro _ (⟨a, rfl⟩ | ⟨i, rfl⟩)
    · exact .inr ⟨.inl a, rfl⟩
    · exact .inr ⟨.inr i, rfl⟩
  refine IsInducing.of_comp (g := fun sw : UnderlyingSpace ℂ S × (Fin n → ℂ) ↦
      Sum.elim (evalTop sw.1) sw.2) ?_ ?_ ?_
  · exact (continuous_mapFun _).prodMk (continuous_pi fun i ↦
      (continuous_apply _).comp (isInducing_evalTop (K := ℂ) (X := 𝔸(Fin n; S))).continuous)
  · refine continuous_pi fun j ↦ ?_
    rcases j with a | i
    · exact (continuous_apply a).comp
        ((isInducing_evalTop (K := ℂ) (X := S)).continuous.comp continuous_fst)
    · exact (continuous_apply i).comp continuous_snd
  · convert isInducing_evalFamily (K := ℂ) y hy using 1
    funext p j
    rcases j with a | i
    · exact evalTop_mapFun _ p a
    · rfl

/-- A point `x ∈ V(ℂ)`, as a point of the open subscheme `V`. -/
def openLiftPoint {V : X.Opens} (x : {x : UnderlyingSpace ℂ X // ⊤ ≤ x.toHom ⁻¹ᵁ V}) :
    UnderlyingSpace ℂ V.toScheme :=
  ⟨openLift V x.1.toHom x.2, by
    change _ ≫ V.ι ≫ X ↘ Spec (.of ℂ) = _
    rw [openLift_ι_assoc V x.1.toHom x.2, x.1.toHom_comp_over]⟩

omit [E.IsQuasicoherent] in
/-- The identification of `{x ∈ X(ℂ) | x ∈ V}` with `V(ℂ)` is continuous. -/
lemma continuous_openLiftPoint (V : X.Opens) :
    Continuous (openLiftPoint (V := V)) := by
  refine (isInducing_map_of_isOpenImmersion (K := ℂ) V.ι).continuous_iff.2 ?_
  have : (map (K := ℂ) V.ι) ∘ openLiftPoint (V := V) = Subtype.val := by
    funext x
    exact UnderlyingSpace.ext (openLift_ι V x.1.toHom x.2)
  rw [this]
  exact continuous_subtype_val

omit [E.IsQuasicoherent] in
/-- The map `V(ℂ) × ℂʳ → 𝔸ʳ_V(ℂ)`, `(x, w) ↦ affinePoint c (x, w)`, is continuous. -/
lemma continuous_affinePoint (c : Chart E r) : Continuous (affinePoint c) := by
  have : IsAffine c.1.1.toScheme := isAffineOpen_affineOpens c.1
  refine (isInducing_affineSpace c.1.1.toScheme r).continuous_iff.2 ?_
  have : (fun p : UnderlyingSpace ℂ 𝔸(Fin r; c.1.1.toScheme) ↦
      (mapFun (𝔸(Fin r; c.1.1.toScheme) ↘ c.1.1.toScheme) p,
        fun i ↦ evalTop p (AffineSpace.coord c.1.1.toScheme i))) ∘ affinePoint c =
      fun xw ↦ (openLiftPoint xw.1, xw.2) := by
    funext xw
    refine Prod.ext (UnderlyingSpace.ext ?_) (funext fun i ↦ ?_)
    · exact AffineSpace.homOfVector_over _ _
    · change evalTop (affinePoint c xw) _ = _
      rw [evalTop_eq]
      change (Scheme.ΓSpecIso (.of ℂ)).hom ((AffineSpace.homOfVector _ _).appTop _) = _
      rw [AffineSpace.homOfVector_appTop_coord, Iso.inv_hom_id_apply]
  rw [this]
  exact ((continuous_openLiftPoint _).comp continuous_fst).prodMk continuous_snd

/-- The map `V(ℂ) × ℂʳ → 𝐕(ℰ)(ℂ)`, `(x, w) ↦ chartInv c x hx w`, is continuous. -/
lemma continuous_chartInv (c : Chart E r) :
    Continuous fun xw : {x : UnderlyingSpace ℂ X // ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1} × (Fin r → ℂ) ↦
      chartInv c xw.1.1 xw.1.2 xw.2 :=
  (continuous_mapFun _).comp (continuous_affinePoint c)

/-- **The chart homeomorphism `π⁻¹V(ℂ) ≃ₜ V(ℂ) × ℂʳ`** of a chart `c = (V, b)`,
`p ↦ (π p, (bᵢ(p))ᵢ)`. Its inverse is read off from the chart isomorphism `π⁻¹V ≅ 𝔸ʳ_V`
(`chartIso`). -/
def chartHomeomorph (c : Chart E r) :
    {p : UnderlyingSpace ℂ (totalSpace E) // ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)} ≃ₜ
      {x : UnderlyingSpace ℂ X // ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1} × (Fin r → ℂ) where
  toFun p := (⟨mapFun (proj E) p.1, mapFun_proj_mem p.2⟩, coord c p.1)
  invFun xw := ⟨chartInv c xw.1.1 xw.1.2 xw.2, chartInv_mem c xw.1.1 xw.1.2 xw.2⟩
  left_inv p := Subtype.ext (chartInv_mapFun_proj_coord c p.1 p.2)
  right_inv xw := Prod.ext (Subtype.ext (mapFun_proj_chartInv c xw.1.1 xw.1.2 xw.2))
    (coord_chartInv c xw.1.1 xw.1.2 xw.2)
  continuous_toFun :=
    (((continuous_mapFun _).comp continuous_subtype_val).subtype_mk _).prodMk
      (continuousOn_coord c).domRestrict
  continuous_invFun := (continuous_chartInv c).subtype_mk _

/-- The first component of `chartHomeomorph c p` is `π(p)`. -/
@[simp]
lemma chartHomeomorph_apply_fst (c : Chart E r)
    (p : {p : UnderlyingSpace ℂ (totalSpace E) // ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)}) :
    ((chartHomeomorph c p).1 : UnderlyingSpace ℂ X) = mapFun (proj E) p.1 :=
  rfl

/-- The second component of `chartHomeomorph c p` is the coordinate vector `coord c p`. -/
@[simp]
lemma chartHomeomorph_apply_snd (c : Chart E r)
    (p : {p : UnderlyingSpace ℂ (totalSpace E) // ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)}) :
    (chartHomeomorph c p).2 = coord c p.1 :=
  rfl

/-- The inverse of `chartHomeomorph c` sends `(x, w)` to `chartInv c x hx w`. -/
@[simp]
lemma chartHomeomorph_symm_apply (c : Chart E r)
    (xw : {x : UnderlyingSpace ℂ X // ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1} × (Fin r → ℂ)) :
    ((chartHomeomorph c).symm xw : UnderlyingSpace ℂ (totalSpace E)) =
      chartInv c xw.1.1 xw.1.2 xw.2 :=
  rfl

end ChartHomeomorph

/-! ### Linear transitions -/

section Transition

open UnderlyingSpace Stacks.AlgebraicGeometry.QuasicoherentBaseChange

/-- The restriction to a basic open `D(a)` of a basis of the sections of `ℰ` over an affine open
`V`: the sections over `D(a)` are the localization of those over `V` at `a`
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`). -/
def basisBasicOpen {V : X.Opens} (hV : IsAffineOpen V) {ι : Type*}
    (b : Module.Basis ι Γ(X, V) Γ(E, V)) (a : Γ(X, V)) :
    Module.Basis ι Γ(X, X.basicOpen a) Γ(E, X.basicOpen a) :=
  letI := moduleOfLE E (X.basicOpen_le a)
  haveI : IsScalarTower Γ(X, V) Γ(X, X.basicOpen a) Γ(E, X.basicOpen a) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  haveI := hV.isLocalization_basicOpen a
  haveI := isLocalizedModule_restrictₗ E hV a rfl (X.basicOpen_le a)
  b.ofIsLocalizedModule Γ(X, X.basicOpen a) (Submonoid.powers a)
    (restrictₗ E (X.basicOpen_le a))

/-- The `i`-th element of the restricted basis over `D(a)` is the restriction of `bᵢ`. -/
lemma basisBasicOpen_apply {V : X.Opens} (hV : IsAffineOpen V) {ι : Type*}
    (b : Module.Basis ι Γ(X, V) Γ(E, V)) (a : Γ(X, V)) (i : ι) :
    basisBasicOpen hV b a i = E.presheaf.map (homOfLE (X.basicOpen_le a)).op (b i) := by
  unfold basisBasicOpen
  rw [Module.Basis.ofIsLocalizedModule_apply]
  rfl

/-- The change-of-basis matrix over a basic open `D(a) ⊆ V ∩ V'` of two charts `(V, b)`,
`(V', b')`: `b'ⱼ = ∑ᵢ Aⱼᵢ bᵢ` on `D(a)`. -/
def transitionSection (c c' : Chart E r) (a : Γ(X, c.1.1)) (ha : X.basicOpen a ≤ c'.1.1)
    (j i : Fin r) : Γ(X, X.basicOpen a) :=
  (basisBasicOpen (isAffineOpen_affineOpens c.1) c.2 a).repr
    (E.presheaf.map (homOfLE ha).op (c'.2 j)) i

/-- On a basic open `D(a) ⊆ V ∩ V'`, `b'ⱼ = ∑ᵢ Aⱼᵢ bᵢ` with `A` the change-of-basis matrix
`transitionSection c c' a ha`. -/
lemma restrict_eq_sum_transitionSection (c c' : Chart E r) (a : Γ(X, c.1.1))
    (ha : X.basicOpen a ≤ c'.1.1) (j : Fin r) :
    E.presheaf.map (homOfLE ha).op (c'.2 j) = ∑ i, transitionSection c c' a ha j i •
      E.presheaf.map (homOfLE (X.basicOpen_le a)).op (c.2 i) := by
  conv_lhs => rw [← (basisBasicOpen (isAffineOpen_affineOpens c.1) c.2 a).sum_repr
    (E.presheaf.map (homOfLE ha).op (c'.2 j))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [basisBasicOpen_apply]
  rfl

variable [X.Over (Spec (.of ℂ))]

/-- **Linear transitions, over a basic open.** On `π⁻¹D(a)(ℂ)`, for `D(a) ⊆ V ∩ V'`, the
coordinates of the chart `(V', b')` are those of `(V, b)` multiplied by the change-of-basis matrix
evaluated at the base point. -/
theorem coord_eq_mulVec_of_basicOpen (c c' : Chart E r) (a : Γ(X, c.1.1))
    (ha : X.basicOpen a ≤ c'.1.1) (p : UnderlyingSpace ℂ (totalSpace E))
    (hpa : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ X.basicOpen a)) :
    coord c' p = Matrix.of (fun j i ↦ eval (mapFun (proj E) p) (mapFun_proj_mem hpa)
      (transitionSection c c' a ha j i)) *ᵥ coord c p := by
  let W : X.affineOpens := ⟨X.basicOpen a, (isAffineOpen_affineOpens c.1).basicOpen a⟩
  have hWV : W ≤ c.1 := X.basicOpen_le a
  have hWV' : W ≤ c'.1 := ha
  have hpV : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) :=
    hpa.trans (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hWV))
  have hpV' : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ c'.1.1) :=
    hpa.trans (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hWV'))
  have hpW : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ W.1) := hpa
  funext j
  have h1 : secRes (symAlg E) (homOfLE hWV')
      (generator E (isAffineOpen_affineOpens c'.1) (c'.2 j)) =
      generator E (isAffineOpen_affineOpens W) (E.presheaf.map (homOfLE ha).op (c'.2 j)) :=
    generator_restrict E _ _ ha _
  have h2 : ∀ i, secRes (symAlg E) (homOfLE hWV)
      (generator E (isAffineOpen_affineOpens c.1) (c.2 i)) =
      generator E (isAffineOpen_affineOpens W)
        (E.presheaf.map (homOfLE (X.basicOpen_le a)).op (c.2 i)) :=
    fun i ↦ generator_restrict E _ _ (X.basicOpen_le a) _
  rw [coord_apply c' hpV' j, chartCoordSection, ← eval_totalSections_restrict E hWV' p hpW hpV',
    h1, restrict_eq_sum_transitionSection c c' a ha j, map_sum, map_sum,
    ← evalRingHom_apply, map_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [generator_smul, map_mul, map_mul, evalRingHom_apply, evalRingHom_apply,
    eval_totalSections_structureMap E W p hpW (mapFun_proj_mem hpa), coord_apply c hpV i,
    chartCoordSection, ← eval_totalSections_restrict E hWV p hpW hpV, h2]

/-- **The transition matrix** between two charts `c = (V, b)` and `c' = (V', b')` at a point
`x ∈ V(ℂ)`: its `i`-th column is the `c'`-coordinate vector of the point with `c`-coordinates
`eᵢ` over `x`. On `(V ∩ V')(ℂ)` it is the change-of-basis matrix of `b`, `b'` evaluated at `x`
(`transition_eq_of_basicOpen`); it is `0` off `V(ℂ)`. -/
def transition (c c' : Chart E r) (x : UnderlyingSpace ℂ X) : Matrix (Fin r) (Fin r) ℂ :=
  open Classical in
  if hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1 then
    Matrix.of fun j i ↦ coord c' (chartInv c x hx (Pi.single i 1)) j
  else 0

/-- On a basic open `D(a) ⊆ V ∩ V'`, the transition matrix is the change-of-basis matrix of the
two bases, evaluated at the point. -/
theorem transition_eq_of_basicOpen (c c' : Chart E r) (a : Γ(X, c.1.1))
    (ha : X.basicOpen a ≤ c'.1.1) (x : UnderlyingSpace ℂ X)
    (hxa : ⊤ ≤ x.toHom ⁻¹ᵁ X.basicOpen a) :
    transition c c' x = Matrix.of fun j i ↦ eval x hxa (transitionSection c c' a ha j i) := by
  have hx : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1 := hxa.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le a))
  rw [transition, dite_eq_left hx]
  ext j i
  have hpa : ⊤ ≤ (chartInv c x hx (Pi.single i 1)).toHom ⁻¹ᵁ (proj E ⁻¹ᵁ X.basicOpen a) := by
    intro z hz
    change proj E ((chartInv c x hx (Pi.single i 1)).toHom z) ∈ X.basicOpen a
    rw [← Scheme.Hom.comp_apply, toHom_chartInv_proj]
    exact hxa hz
  have key : ∀ (y : UnderlyingSpace ℂ X) (hy : y = x) (h : ⊤ ≤ y.toHom ⁻¹ᵁ X.basicOpen a),
      eval y h (transitionSection c c' a ha j i) =
        eval x hxa (transitionSection c c' a ha j i) := by
    rintro _ rfl _
    rfl
  rw [Matrix.of_apply, Matrix.of_apply, coord_eq_mulVec_of_basicOpen c c' a ha _ hpa,
    coord_chartInv, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.of_apply,
    key _ (mapFun_proj_chartInv c x hx _)]

/-- **Linear transitions.** On `π⁻¹(V ∩ V')(ℂ)`, the coordinates of the chart `c' = (V', b')`
are those of `c = (V, b)` multiplied by the transition matrix at the base point. -/
theorem coord_eq_transition_mulVec (c c' : Chart E r) (p : UnderlyingSpace ℂ (totalSpace E))
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ (c.1.1 ⊓ c'.1.1))) :
    coord c' p = transition c c' (mapFun (proj E) p) *ᵥ coord c p := by
  have hz : proj E (p.toHom (IsLocalRing.closedPoint ℂ)) ∈ c.1.1 ⊓ c'.1.1 :=
    hp (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Spec (.of ℂ)).Opens) from trivial)
  obtain ⟨a, ha, hza⟩ := (isAffineOpen_affineOpens c.1).exists_basicOpen_le ⟨_, hz.2⟩ hz.1
  have hpa : ⊤ ≤ p.toHom ⁻¹ᵁ (proj E ⁻¹ᵁ X.basicOpen a) := (top_le_preimage_iff p _).mpr hza
  rw [transition_eq_of_basicOpen c c' a ha _ (mapFun_proj_mem hpa),
    coord_eq_mulVec_of_basicOpen c c' a ha p hpa]

/-- **The transition matrices are continuous** on `(V ∩ V')(ℂ)`. -/
theorem continuousOn_transition (c c' : Chart E r) :
    ContinuousOn (transition c c')
      {x : UnderlyingSpace ℂ X | ⊤ ≤ x.toHom ⁻¹ᵁ (c.1.1 ⊓ c'.1.1)} := by
  intro x hx
  have hz : x.toHom (IsLocalRing.closedPoint ℂ) ∈ c.1.1 ⊓ c'.1.1 :=
    hx (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Spec (.of ℂ)).Opens) from trivial)
  obtain ⟨a, ha, hza⟩ := (isAffineOpen_affineOpens c.1).exists_basicOpen_le ⟨_, hz.2⟩ hz.1
  have hD : IsOpen {y : UnderlyingSpace ℂ X | ⊤ ≤ y.toHom ⁻¹ᵁ X.basicOpen a} :=
    isOpen_setOf_le_preimage _
  have hxD : x ∈ {y : UnderlyingSpace ℂ X | ⊤ ≤ y.toHom ⁻¹ᵁ X.basicOpen a} :=
    (top_le_preimage_iff x _).mpr hza
  let M : UnderlyingSpace ℂ X → Matrix (Fin r) (Fin r) ℂ := fun y ↦
    Matrix.of fun j i ↦ evalExt (X.basicOpen a) (transitionSection c c' a ha j i) y
  have hM : ContinuousOn M {y : UnderlyingSpace ℂ X | ⊤ ≤ y.toHom ⁻¹ᵁ X.basicOpen a} :=
    continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun i ↦ continuousOn_evalExt _ _
  have heq : M =ᶠ[𝓝 x] transition c c' := by
    filter_upwards [hD.mem_nhds hxD] with y hy
    rw [transition_eq_of_basicOpen c c' a ha y hy]
    ext j i
    exact evalExt_of_le _ hy
  exact ((hM.continuousAt (hD.mem_nhds hxD)).congr heq).continuousWithinAt

end Transition

end MMP.Modules
