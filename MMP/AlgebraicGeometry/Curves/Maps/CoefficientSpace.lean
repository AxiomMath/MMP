module

public import MMP.Attr
public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.CoordinateSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.PinnedTwist
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemLifting
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Multiplication
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ZeroSchemeSectionPower
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.SectionRingZero
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullback

/-!
# The coefficient space of tuples of sections and the family of maps to projective space

Let `C` be a proper `k`-scheme, `L` an invertible `𝒪_C`-module and `e₁, …, e_N` global sections of
`L` (in the application, a basis of the finite-dimensional space `H⁰(C, L)`). A `T`-point of the
affine space `𝔸^{(n+1)N}_k` is a tuple of coefficients `(c_{ij})`, and gives the tuple of sections
`σ_i = Σ_j c_{ij} · e_j` of `pr_C^* L` on `C ×ₖ T`. The tuple of the universal point lives on
`C ×ₖ 𝔸`. Its common-zero locus is closed, its image in `𝔸` is closed because `C` is proper, and
the complement `M₁` is the open scheme of tuples without common zero. Over `M₁` the universal tuple
generates `pr_C^* L`, hence defines (Stacks Tag 01NE) a `k`-morphism `Φ : C ×ₖ M₁ → ℙⁿ_k` with
`Φ^* 𝒪(1) ≅ pr_C^* L` carrying the pulled-back coordinates to the sections.

## Main definitions

* `MMP.Fourfold.coefficientSpace`, `MMP.Fourfold.universalSection`: the coefficient space and the
  universal tuple of sections of `pr_C^* L`.
* `MMP.Fourfold.noCommonZeroOpen`, `MMP.Fourfold.noCommonZeroScheme`: the open locus of tuples
  without common zero, and its subscheme.
* `MMP.Fourfold.noCommonZeroFamily`: the family `Φ : C ×ₖ M₁ → ℙⁿ_k`.

## Main results

* `MMP.Fourfold.generatesStalks_familySection`: a `T`-point of `M₁` gives a generating tuple.
* `MMP.Fourfold.exists_familyMap_iso_pullback_twistingSheaf`: the map to `ℙⁿ_k` of any `T`-point
  of `M₁`, with the pinned isomorphism `Φ^* 𝒪(1) ≅ pr_C^* L`.
* `MMP.Fourfold.exists_iso_noCommonZeroFamily`: the same for the universal family.
* `MMP.Fourfold.exists_lift_noCommonZeroScheme`: `k`-points of `M₁`.
* `MMP.Fourfold.coefficients`, `MMP.Fourfold.eq_sum_coefficients`,
  `MMP.Fourfold.coefficients_sum`, `MMP.Fourfold.coefficients_add`,
  `MMP.Fourfold.coefficients_smul`: the `k`-linear identification of tuples of coefficients with
  `H⁰(C, L)` against a `k`-basis.
* `MMP.Fourfold.eq_toProjectiveSpaceAtUniverse_of_pinned`,
  `MMP.Fourfold.eq_of_pinned_of_iso`, `MMP.Fourfold.eq_of_pinned_of_iso_over`: uniqueness of the
  morphism to `ℙⁿ` determined by a pinned isomorphism `Φ^* 𝒪(1) ≅ L` (Stacks Tag 01NE).
* `MMP.Fourfold.exists_iso_of_pinned_same_hom`: two tuples with the same map differ by an
  isomorphism of the line bundle.
* `MMP.Fourfold.coefficientPoint_mem_noCommonZeroOpen`: the `k`-point of a tuple coming from a
  morphism `f` to `ℙⁿ_k` lies in `M₁`.
* `MMP.Fourfold.noCommonZeroFamily_base_change_eq`: `Φ|_{[f]} = f`.

## References

* Kollár, *Rational curves on algebraic varieties*, II.1.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Stacks.ProjectiveFromSections Stacks.NonvanishingOpen
open Stacks.Ample (IsInvertibleModule nonvanishingLocus)

universe u

namespace MMP.Fourfold

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- The coefficient space `𝔸^{(n+1) N}_k` of tuples `(c_{ij})` of coefficients. -/
abbrev coefficientSpace (n N : ℕ) (k : Type u) [Field k] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin (n + 1) × Fin N); Spec (.of k))

/-- The structure morphism of the coefficient space. -/
abbrev coefficientSpaceOver (n N : ℕ) (k : Type u) [Field k] :
    coefficientSpace n N k ⟶ Spec (.of k) := coefficientSpace n N k ↘ Spec (.of k)

/-- The universal coordinate `x_{ij}`. -/
def coefficientCoord (n N : ℕ) (k : Type u) [Field k] (i : Fin (n + 1)) (j : Fin N) :
    Γ(coefficientSpace n N k, ⊤) :=
  AffineSpace.coord (Spec (.of k)) (⟨(i, j)⟩ : ULift.{u} (Fin (n + 1) × Fin N))

/-- **The universal tuple of sections** on `C ×ₖ 𝔸`: the `i`-th section is `Σⱼ x_{ij} · e_j`. -/
def universalSection (i : Fin (n + 1)) :
    Γ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L, ⊤) :=
  Stacks.LinearSystemScheme.coordSection (pullback.fst sC (coefficientSpaceOver n N k))
    (pullback.snd sC (coefficientSpaceOver n N k)) L e (fun j => coefficientCoord n N k i j)

/-- `C ×ₖ 𝔸`. -/
abbrev universalCurve : Scheme.{u} := pullback sC (coefficientSpaceOver n N k)

/-- `pr_C^* L` is an invertible module on `C ×ₖ 𝔸`. -/
instance : IsInvertibleModule (universalCurve (n := n) (N := N) sC)
    ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback _ L

/-- The set of points of `C ×ₖ 𝔸` at which all the universal sections vanish. -/
def commonZeroLocus : Set (universalCurve (n := n) (N := N) sC) :=
  (⋃ i : Fin (n + 1), ((nvCover (universalSection (n := n) sC L e) i :
    (universalCurve (n := n) (N := N) sC).Opens) : Set _))ᶜ

/-- The common-zero locus of the universal tuple is closed in `C ×ₖ 𝔸`. -/
theorem isClosed_commonZeroLocus :
    IsClosed (commonZeroLocus (n := n) sC L e) := by
  unfold commonZeroLocus
  rw [isClosed_compl_iff]
  exact isOpen_iUnion fun i => (nvCover (universalSection (n := n) sC L e) i).isOpen

/-- **The locus of tuples with no common zero**: the complement of the image, under the proper
projection `C ×ₖ 𝔸 → 𝔸`, of the closed common-zero locus. -/
def noCommonZeroOpen [IsProper sC] : (coefficientSpace n N k).Opens :=
  ⟨(pullback.snd sC (coefficientSpaceOver n N k) '' commonZeroLocus (n := n) sC L e)ᶜ, by
    rw [isOpen_compl_iff]
    exact (pullback.snd sC (coefficientSpaceOver n N k)).isClosedMap _
      (isClosed_commonZeroLocus sC L e)⟩

/-- **Generation by pulled-back sections.** If the images in `X` of all points of `Y` lie in the
nonvanishing opens of a family `s` of sections of an invertible module `M` on `X`, then the
pulled-back sections generate every stalk of `h^* M` (Tag 0H78). -/
theorem generatesStalks_pullback_of_forall_exists_mem {X Y : Scheme.{u}} (h : Y ⟶ X)
    (M : X.Modules) [IsInvertibleModule X M] {ι : Type*} (s : ι → Γ(M, ⊤))
    (hs : ∀ y : Y, ∃ i, h.base y ∈ nvCover s i) :
    letI : IsInvertibleModule Y ((Scheme.Modules.pullback h).obj M) :=
      Stacks.InvertiblePullback.isInvertibleModule_pullback h M
    GeneratesStalks fun i => AlgebraicGeometry.pullbackGlobalSections h M (s i) := by
  have : IsInvertibleModule Y ((Scheme.Modules.pullback h).obj M) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback h M
  refine (Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem _).2 fun y => ?_
  obtain ⟨i, hi⟩ := hs y
  refine ⟨i, ?_⟩
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen]
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen] at hi
  have hk' : y ∈ nonvanishingLocus ((Scheme.Modules.pullback h).obj M)
      (Stacks.NonvanishingPullback.pullbackGlobalSection h M (s i)) :=
    (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff h M (s i) y).2 hi
  rw [← Stacks.AmpleFormalSystemLifting.pullbackGlobalSections_eq_pullbackGlobalSection h M (s i)]
    at hk'
  exact hk'

section Family

variable {sC L e} {T : Scheme.{u}} (g : T ⟶ coefficientSpace n N k)

/-- The base change of a `T`-point `g` of the coefficient space: the morphism
`C ×ₖ T → C ×ₖ 𝔸`. -/
def familyPullbackMap : pullback sC (g ≫ coefficientSpaceOver n N k) ⟶
    universalCurve (n := n) (N := N) sC :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by simp [pullback.condition])

/-- The first projection of `C ×ₖ T → C ×ₖ 𝔸` is the first projection of `C ×ₖ T`. -/
@[reassoc (attr := simp)]
theorem familyPullbackMap_fst :
    familyPullbackMap (n := n) (N := N) (sC := sC) g ≫ pullback.fst sC (coefficientSpaceOver n N k) =
      pullback.fst sC (g ≫ coefficientSpaceOver n N k) :=
  pullback.lift_fst _ _ _

/-- The second projection of `C ×ₖ T → C ×ₖ 𝔸` is the second projection of `C ×ₖ T` followed by
`g`. -/
@[reassoc (attr := simp)]
theorem familyPullbackMap_snd :
    familyPullbackMap (n := n) (N := N) (sC := sC) g ≫ pullback.snd sC (coefficientSpaceOver n N k) =
      pullback.snd sC (g ≫ coefficientSpaceOver n N k) ≫ g :=
  pullback.lift_snd _ _ _

/-- The invertible sheaf `pr_C^* L` on `C ×ₖ T`. -/
abbrev familyModule : (pullback sC (g ≫ coefficientSpaceOver n N k)).Modules :=
  (Scheme.Modules.pullback (familyPullbackMap (n := n) (N := N) (sC := sC) g)).obj
    ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)

/-- The tuple of sections of `pr_C^* L` on `C ×ₖ T` determined by a `T`-point `g` of the
coefficient space: the pullback of the universal tuple. -/
def familySection (i : Fin (n + 1)) : Γ(familyModule (n := n) (N := N) (L := L) (sC := sC) g, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (familyPullbackMap (n := n) (N := N) (sC := sC) g) _
    (universalSection (n := n) sC L e i)

/-- `pr_C^* L` is an invertible module on `C ×ₖ T`. -/
instance : IsInvertibleModule (pullback sC (g ≫ coefficientSpaceOver n N k))
    (familyModule (n := n) (N := N) (L := L) (sC := sC) g) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback _ _

/-- **A `T`-point of the open locus of tuples without common zero gives a generating tuple on
`C ×ₖ T`.** -/
theorem generatesStalks_familySection [IsProper sC]
    (hg : ∀ t : T, g.base t ∈ noCommonZeroOpen (n := n) sC L e) :
    Stacks.ProjectiveFromSections.GeneratesStalks
      (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC) g) := by
  refine generatesStalks_pullback_of_forall_exists_mem _ _ _ fun y => ?_
  by_contra hne
  push Not at hne
  have hmem : (familyPullbackMap (n := n) (N := N) (sC := sC) g).base y ∈
      commonZeroLocus (n := n) sC L e := by
    simp only [commonZeroLocus, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact hne
  have := hg ((pullback.snd sC (g ≫ coefficientSpaceOver n N k)).base y)
  refine this ⟨_, hmem, ?_⟩
  exact congrArg (fun φ => φ.base y) (familyPullbackMap_snd (n := n) (N := N) (sC := sC) g)

open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections in
/-- **Existence of the morphism `C ×ₖ T → ℙⁿ_k` of a family of tuples without common zero**
(Stacks Tag 01NE, in its relative form): there are a `k`-morphism `Φ` to `ℙⁿ_k` and an
isomorphism `Φ^* 𝒪(1) ≅ pr_C^* L` carrying the `i`-th pulled-back coordinate to the `i`-th section
of the tuple. -/
theorem exists_familyMap_iso_pullback_twistingSheaf [IsProper sC]
    (hg : ∀ t : T, g.base t ∈ noCommonZeroOpen (n := n) sC L e) :
    ∃ p : pullback sC (g ≫ coefficientSpaceOver n N k) ⟶ projectiveSpaceOver n (Spec (.of k)),
      p ≫ pullback.fst (terminal.from (Spec (.of k)))
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
        pullback.fst sC (g ≫ coefficientSpaceOver n N k) ≫ sC ∧
      ∃ α : (Scheme.Modules.pullback
          (p ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
            (twistingSheafAtUniverse.{u} n) ⟶
          familyModule (n := n) (N := N) (L := L) (sC := sC) g,
        IsIso α ∧ ∀ i, α.app ⊤ (Stacks.TwistPullbackPinned.pullbackCoordSection.{u}
          (p ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
          familySection (n := n) (N := N) (L := L) (e := e) (sC := sC) g i :=
  Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse _
    (generatesStalks_familySection g hg) _

end Family

/-- The coefficient space is a Noetherian topological space, being an affine space of finite
type over a field. -/
instance noetherianSpace_coefficientSpace : TopologicalSpace.NoetherianSpace (coefficientSpace n N k) :=
  (TopologicalSpace.noetherianSpace_iff_of_homeomorph
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin (n + 1) × Fin N))
      (CommRingCat.of k))))).mpr (by
    show TopologicalSpace.NoetherianSpace (PrimeSpectrum _)
    infer_instance)

section Locus

variable [IsProper sC]

/-- **The scheme of tuples without common zero**: the open subscheme of the coefficient space
`𝔸(H⁰(C,L)^{n+1})` where the universal tuple of sections of `L` has no common zero. -/
abbrev noCommonZeroScheme : Scheme.{u} := (noCommonZeroOpen (n := n) sC L e).toScheme

/-- The open immersion of the scheme of tuples without common zero into the coefficient space. -/
abbrev noCommonZeroScheme.ι : noCommonZeroScheme (n := n) sC L e ⟶ coefficientSpace n N k :=
  (noCommonZeroOpen (n := n) sC L e).ι

/-- The structure morphism of the scheme of tuples without common zero. -/
abbrev noCommonZeroScheme.over : noCommonZeroScheme (n := n) sC L e ⟶ Spec (.of k) :=
  noCommonZeroScheme.ι (n := n) sC L e ≫ coefficientSpaceOver n N k

/-- The scheme of tuples without common zero is locally of finite type over `k`. -/
instance : LocallyOfFiniteType (noCommonZeroScheme.over (n := n) sC L e) := by
  unfold noCommonZeroScheme.over
  infer_instance

/-- The scheme of tuples without common zero is quasi-compact over `k`. -/
instance : QuasiCompact (noCommonZeroScheme.over (n := n) sC L e) := by
  have h1 : QuasiCompact (noCommonZeroScheme.ι (n := n) sC L e) :=
    ⟨fun U _ _ => by
      have : TopologicalSpace.NoetherianSpace (noCommonZeroScheme (n := n) sC L e) :=
        TopologicalSpace.NoetherianSpace.set
          ((noCommonZeroOpen (n := n) sC L e : Set (coefficientSpace n N k)))
      exact TopologicalSpace.NoetherianSpace.isCompact _⟩
  have h2 : QuasiCompact (coefficientSpaceOver n N k) := inferInstance
  unfold noCommonZeroScheme.over
  infer_instance

/-- The inclusion of the scheme of tuples without common zero lands in the open locus
`noCommonZeroOpen`. -/
theorem base_noCommonZeroScheme_ι_mem (t : noCommonZeroScheme (n := n) sC L e) :
    (noCommonZeroScheme.ι (n := n) sC L e).base t ∈ noCommonZeroOpen (n := n) sC L e :=
  t.2

open Stacks.AmpleProjectiveImmersion in
/-- **The family of maps `Φ : C ×ₖ M → ℙⁿ_k`** over the scheme of tuples without common zero
(Stacks Tag 01NE applied to the universal tuple), over `k`. -/
def noCommonZeroFamily :
    pullback sC (noCommonZeroScheme.over (n := n) sC L e) ⟶ projectiveSpaceOver n (Spec (.of k)) :=
  Classical.choose (exists_familyMap_iso_pullback_twistingSheaf
    (noCommonZeroScheme.ι (n := n) sC L e) (base_noCommonZeroScheme_ι_mem sC L e))

open Stacks.AmpleProjectiveImmersion in
/-- The family `Φ` lies over `k`. -/
theorem noCommonZeroFamily_over :
    noCommonZeroFamily (n := n) sC L e ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      pullback.fst sC (noCommonZeroScheme.over (n := n) sC L e) ≫ sC :=
  (Classical.choose_spec (exists_familyMap_iso_pullback_twistingSheaf
    (noCommonZeroScheme.ι (n := n) sC L e) (base_noCommonZeroScheme_ι_mem sC L e))).1

open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections in
/-- **`Φ^* 𝒪(1) ≅ pr_C^* L`**, carrying the pulled-back coordinates to the universal sections. -/
theorem exists_iso_noCommonZeroFamily :
    ∃ α : (Scheme.Modules.pullback
          (noCommonZeroFamily (n := n) sC L e ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
            (twistingSheafAtUniverse.{u} n) ⟶
          familyModule (n := n) (N := N) (L := L) (sC := sC)
            (noCommonZeroScheme.ι (n := n) sC L e),
        IsIso α ∧ ∀ i, α.app ⊤ (Stacks.TwistPullbackPinned.pullbackCoordSection.{u}
          (noCommonZeroFamily (n := n) sC L e ≫
            projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
          familySection (n := n) (N := N) (L := L) (e := e) (sC := sC)
            (noCommonZeroScheme.ι (n := n) sC L e) i :=
  (Classical.choose_spec (exists_familyMap_iso_pullback_twistingSheaf
    (noCommonZeroScheme.ι (n := n) sC L e) (base_noCommonZeroScheme_ι_mem sC L e))).2

/-- The `k`-point of the coefficient space with the given coefficients `a i j ∈ k`. -/
def coefficientPoint (a : Fin (n + 1) → Fin N → k) : Spec (.of k) ⟶ coefficientSpace n N k :=
  AffineSpace.homOfVector (𝟙 (Spec (.of k)))
    (fun x : ULift.{u} (Fin (n + 1) × Fin N) =>
      (Scheme.ΓSpecIso (.of k)).inv (a x.down.1 x.down.2))

/-- The `k`-point `coefficientPoint a` is a morphism over `k`. -/
@[simp]
theorem coefficientPoint_over (a : Fin (n + 1) → Fin N → k) :
    coefficientPoint (n := n) (N := N) a ≫ coefficientSpaceOver n N k = 𝟙 (Spec (.of k)) :=
  AffineSpace.homOfVector_over _ _

/-- A `k`-point of the coefficient space whose image lies in the locus of tuples without common
zero lifts to a `k`-point of the scheme of such tuples. -/
theorem exists_lift_noCommonZeroScheme (a : Fin (n + 1) → Fin N → k)
    (ha : ∀ t, (coefficientPoint (n := n) (N := N) a).base t ∈
      noCommonZeroOpen (n := n) sC L e) :
    ∃ m : Spec (.of k) ⟶ noCommonZeroScheme (n := n) sC L e,
      m ≫ noCommonZeroScheme.over (n := n) sC L e = 𝟙 (Spec (.of k)) ∧
        m ≫ noCommonZeroScheme.ι (n := n) sC L e = coefficientPoint (n := n) (N := N) a := by
  have hle : Set.range (coefficientPoint (n := n) (N := N) a).base ⊆
      Set.range (noCommonZeroScheme.ι (n := n) sC L e).base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ha t
  refine ⟨IsOpenImmersion.lift _ _ hle, ?_, IsOpenImmersion.lift_fac _ _ hle⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, coefficientPoint_over]

end Locus

section Uniqueness

open Opposite TopologicalSpace Stacks.AmpleProjectiveImmersion Stacks.SectionsToProjectiveSpace
  Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

/-- An isomorphism of `𝒪_X`-modules carries the nonvanishing locus of a global section to that of
its image (the map on stalks is a linear isomorphism). -/
theorem nonvanishingLocus_app_top_eq_of_iso {X : Scheme.{u}} {M M' : X.Modules} (e : M ≅ M')
    (t : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus M' (e.hom.val.app (op ⊤) t) =
      Stacks.Ample.nonvanishingLocus M t := by
  ext x
  change _ ∉ Stacks.ModuleStalk.maximalSmul M' x ↔ _ ∉ Stacks.ModuleStalk.maximalSmul M x
  refine not_congr ?_
  let φ := LinearEquiv.ofBijective (stalkLinearMap M M' e.hom x)
    (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_of_inverse e.hom e.inv e.hom_inv_id
      e.inv_hom_id x)
  have hg : (M'.presheaf.Γgerm x).hom (e.hom.val.app (op ⊤) t) =
      φ ((M.presheaf.Γgerm x).hom t) :=
    (stalkLinearMap_germ M M' e.hom ⊤ x trivial t).symm
  rw [hg]
  exact (Stacks.NonvanishingPullback.mem_ideal_smul_top_iff_of_linearEquiv _ φ _).symm

/-- Two morphisms `W ⟶ ℙⁿ_ℤ` landing in the chart `D₊(Tᵢ)` are equal if they pull back each chart
coordinate `Tⱼ/Tᵢ` to the same global function on `W`. -/
theorem hom_ext_projectiveSpace_of_appLE_coordFrac {W : Scheme.{u}} {n : ℕ} (i : Fin (n + 1))
    (a b : W ⟶ projectiveSpaceAtUniverse.{u} n)
    (ha : (⊤ : W.Opens) ≤ a ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (hb : (⊤ : W.Opens) ≤ b ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (h : ∀ j, a.appLE (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) ⊤ ha
        ((Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom (coordFrac.{u} i j)) =
      b.appLE (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) ⊤ hb
        ((Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom (coordFrac.{u} i j))) :
    a = b := by
  set D := Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) with hD
  have hDaff : IsAffineOpen D := Proj.isAffineOpen_basicOpen (coordGrading.{u} n)
    (MvPolynomial.X i) (X_mem_coordGrading_one i) one_pos
  have : IsAffine D.toScheme := hDaff
  have hra : Set.range a.base ⊆ Set.range D.ι.base := by
    rintro _ ⟨x, rfl⟩
    exact (Scheme.Opens.range_ι (U := D)).ge (ha trivial)
  have hrb : Set.range b.base ⊆ Set.range D.ι.base := by
    rintro _ ⟨x, rfl⟩
    exact (Scheme.Opens.range_ι (U := D)).ge (hb trivial)
  let a' := IsOpenImmersion.lift D.ι a hra
  let b' := IsOpenImmersion.lift D.ι b hrb
  have ha' : a' ≫ D.ι = a := IsOpenImmersion.lift_fac _ _ hra
  have hb' : b' ≫ D.ι = b := IsOpenImmersion.lift_fac _ _ hrb
  have aux : ∀ (c : W ⟶ D.toScheme) (c0 : W ⟶ projectiveSpaceAtUniverse.{u} n)
      (hc : c ≫ D.ι = c0) (hc0 : (⊤ : W.Opens) ≤ c0 ⁻¹ᵁ D),
      D.topIso.inv ≫ c.appTop = c0.appLE D ⊤ hc0 := by
    intro c c0 hc hc0
    subst hc
    have hι : D.ι.appLE D ⊤ (Stacks.AlgebraicGeometry.ProjTwistMono.preimage_self_eq_top D).ge =
        D.topIso.inv := by
      rw [Scheme.Opens.ι_appLE]; rfl
    have := Scheme.Hom.appLE_comp_appLE c D.ι D ⊤ ⊤
      (Stacks.AlgebraicGeometry.ProjTwistMono.preimage_self_eq_top D).ge le_rfl
    rw [hι] at this
    have e2 : c.appLE ⊤ ⊤ le_rfl = c.appTop := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
      change c.app ⊤ ≫ W.presheaf.map (𝟙 _) = c.app ⊤
      rw [W.presheaf.map_id, Category.comp_id]
    rw [e2] at this
    exact this
  have key : a' = b' := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi D.topIso.inv, aux a' a ha' ha, aux b' b hb' hb]
    have : IsIso (Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)) :=
      inferInstanceAs (IsIso (Proj.basicOpenIsoAway (coordGrading.{u} n) (MvPolynomial.X i)
        (X_mem_coordGrading_one i) one_pos).hom)
    rw [← cancel_epi (Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i))]
    ext z
    obtain ⟨p, rfl⟩ := Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_surjective
      (ULift.{u} ℤ) n i z
    set Fa := (Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i) ≫
      a.appLE D ⊤ ha).hom with hFa
    set Fb := (Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i) ≫
      b.appLE D ⊤ hb).hom with hFb
    have hF : Fa.comp (Stacks.AlgebraicGeometry.ProjPolyChart.chartHom (ULift.{u} ℤ) n i) =
        Fb.comp (Stacks.AlgebraicGeometry.ProjPolyChart.chartHom (ULift.{u} ℤ) n i) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · simp only [RingHom.comp_apply, Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_C]
        have e : ∀ F G : HomogeneousLocalization.Away (coordGrading.{u} n) (MvPolynomial.X i) →+* Γ(W, ⊤),
            F.comp (Stacks.AlgebraicGeometry.ProjPolyChart.coeffToAway (ULift.{u} ℤ) n i) =
              G.comp (Stacks.AlgebraicGeometry.ProjPolyChart.coeffToAway (ULift.{u} ℤ) n i) := by
          intro F G
          ext ⟨z⟩
          have hz : (ULift.up z : ULift.{u} ℤ) = (z : ULift.{u} ℤ) := rfl
          simp only [hz, map_intCast]
        exact DFunLike.congr_fun (e Fa Fb) r
      · simp only [RingHom.comp_apply, Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_X]
        exact h j.1
    exact DFunLike.congr_fun hF p
  rw [← ha', ← hb', key]

/-- A morphism of `𝒪_X`-modules commutes with restriction of sections. -/
theorem moduleHom_app_map {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens}
    (i : U ⟶ V) (x : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app V x) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x)

/-- **Tag 0H78 as an equivalence, at the spelling `pullbackGlobalSections`**: a pulled-back
section does not vanish at `x` iff the section does not vanish at the image of `x`. -/
theorem mem_nonvanishingLocus_pullbackGlobalSections_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) (x : X) :
    x ∈ nonvanishingLocus ((Scheme.Modules.pullback f).obj M)
        (AlgebraicGeometry.pullbackGlobalSections f M s) ↔
      f.base x ∈ nonvanishingLocus M s := by
  have hsec : AlgebraicGeometry.pullbackGlobalSections f M s =
      Stacks.NonvanishingPullback.pullbackGlobalSection f M s := by
    change ((Scheme.Modules.pullback f).obj M).presheaf.map
        (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
        (Stacks.NonvanishingPullback.pullbackGlobalSection f M s) = _
    exact Functor.map_id_apply _ _ _
  rw [hsec]
  exact Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff f M s x

/-- **The pulled-back coordinate `g ^* Tᵢ` does not vanish at `x` iff `g x ∈ D₊(Tᵢ)`.** -/
theorem mem_nonvanishingLocus_pullbackCoordSection_iff {X : Scheme.{u}} {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1)) (x : X) :
    x ∈ nonvanishingLocus ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n))
        (pullbackCoordSection.{u} g i) ↔
      g.base x ∈ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
  refine (mem_nonvanishingLocus_pullbackGlobalSections_iff g _ _ x).trans ?_
  exact (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    (coordGrading.{u} n) 1 1 ⟨MvPolynomial.X i, X_mem_coordGrading_one i⟩
    (by rw [whereInvertible_coordGrading_eq_top]; trivial))

/-- The standard charts `D₊(Tᵢ)` cover `ℙⁿ_ℤ`. -/
theorem exists_mem_basicOpen_coord (n : ℕ) (y : projectiveSpaceAtUniverse.{u} n) :
    ∃ i : Fin (n + 1), y ∈ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
  have h := Proj.iSup_basicOpen_eq_top' (coordGrading.{u} n) (fun i : Fin (n + 1) => MvPolynomial.X i)
    (fun i => ⟨1, X_mem_coordGrading_one i⟩)
    (Stacks.AlgebraicGeometry.ProjPolyChart.adjoin_range_X_eq_top (ULift.{u} ℤ) n)
  have hy : y ∈ ⨆ i : Fin (n + 1), Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
    rw [h]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hy

section Pinned

variable {X : Scheme.{u}} {n : ℕ} {M : X.Modules} [IsInvertibleModule X M]
  (s : Fin (n + 1) → Γ(M, ⊤)) (g : X ⟶ projectiveSpaceAtUniverse.{u} n)
  (α : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n) ⟶ M) [IsIso α]
  (hα : ∀ i, α.app ⊤ (pullbackCoordSection.{u} g i) = s i)

include hα in
/-- If `g ^* 𝒪(1) ≅ M` carries `g ^* Tᵢ` to `sᵢ`, then the nonvanishing locus of `sᵢ` lies in
`g⁻¹ D₊(Tᵢ)`. -/
theorem nvCover_le_preimage_basicOpen_of_pinned (i : Fin (n + 1)) :
    nvCover s i ≤ g ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
  intro x hx
  have h1 : x ∈ Stacks.Ample.nonvanishingLocus M (s i) := hx
  rw [← hα i] at h1
  have h2 := nonvanishingLocus_app_top_eq_of_iso (asIso α) (pullbackCoordSection.{u} g i)
  have h3 : x ∈ nonvanishingLocus ((Scheme.Modules.pullback g).obj
      (twistingSheafAtUniverse.{u} n)) (pullbackCoordSection.{u} g i) := by
    rw [← h2]; exact h1
  exact (mem_nonvanishingLocus_pullbackCoordSection_iff g i x).1 h3

include hα in
/-- If `g ^* 𝒪(1) ≅ M` carries `g ^* Tᵢ` to `sᵢ`, then `g` pulls back the chart coordinate `Tⱼ/Tᵢ`
to the ratio `sⱼ/sᵢ` on the nonvanishing locus of `sᵢ`. -/
theorem appLE_coordFrac_of_pinned (i j : Fin (n + 1)) :
    g.appLE (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) (nvCover s i)
        (nvCover_le_preimage_basicOpen_of_pinned s g α hα i)
        ((Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
          (coordFrac.{u} i j)) = ratio s i j := by
  have hle := nvCover_le_preimage_basicOpen_of_pinned s g α hα i
  have key := congrArg (pullbackSectionOn g (twistingSheafAtUniverse.{u} n)
    (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)))
    (coordGlobalSection_res_eq.{u} n i j)
  rw [pullbackSectionOn_smul, pullbackGlobalSections_res, pullbackGlobalSections_res] at key
  have h2 := congrArg (resM hle) key
  rw [resM_smul, resM_resT, resM_resT] at h2
  have hs : resO hle
      ((Proj.awayToSection (coordGrading.{u} n)
        (MvPolynomial.X i)).hom (coordFrac.{u} i j) |>
          (g.app (Proj.basicOpen (coordGrading.{u} n)
            (MvPolynomial.X i)))) =
      g.appLE (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) (nvCover s i) hle
        ((Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
          (coordFrac.{u} i j)) :=
    (appLE_apply g _ _ hle _).symm
  rw [hs] at h2
  have h3 := congrArg (α.app (nvCover s i)) h2
  rw [Scheme.Modules.Hom.app_smul] at h3
  have e1 : ∀ t : Γ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n), ⊤),
      α.app (nvCover s i) (resT (nvCover s i) t) = resT (nvCover s i) (α.app ⊤ t) :=
    fun t => moduleHom_app_map α (homOfLE le_top) t
  rw [e1, e1] at h3
  have hα' : ∀ j, α.app ⊤ (pullbackGlobalSections g (twistingSheafAtUniverse.{u} n)
      (coordGlobalSection.{u} n j)) = s j := hα
  rw [hα', hα'] at h3
  exact (eq_of_smul_eq_smul (s i) le_rfl (h3.symm.trans (ratio_smul s i j).symm))

include hα in
/-- **Uniqueness on a chart.** A morphism `g` with a pinned isomorphism `g ^* 𝒪(1) ≅ M` restricts
on `X_{sᵢ}` to the chart morphism of the ratios `sⱼ/sᵢ`. -/
theorem ι_comp_eq_chartHom_of_pinned (i : Fin (n + 1)) :
    (nvCover s i).ι ≫ g = chartHom s i := by
  have hle := nvCover_le_preimage_basicOpen_of_pinned s g α hα i
  have ha : (⊤ : (nvCover s i).toScheme.Opens) ≤ ((nvCover s i).ι ≫ g) ⁻¹ᵁ
      Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := fun x _ => hle x.2
  have hb : (⊤ : (nvCover s i).toScheme.Opens) ≤ chartHom s i ⁻¹ᵁ
      Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
    show (⊤ : (nvCover s i).toScheme.Opens) ≤ Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio s i)
      (span_range_chartRatio s i) ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)
    rw [preimage_basicOpen (chartRatio s i) (span_range_chartRatio s i) i, chartRatio_self,
      Scheme.basicOpen_one (nvCover s i).toScheme]
  refine hom_ext_projectiveSpace_of_appLE_coordFrac i _ _ ha hb fun j => ?_
  have h1 := CategoryTheory.ConcreteCategory.congr_hom
    (appLE_comp_topIso_inv g (nvCover s i)
      (Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) hle)
    ((Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom (coordFrac.{u} i j))
  rw [CategoryTheory.ConcreteCategory.comp_apply, appLE_coordFrac_of_pinned s g α hα i j]
    at h1
  refine h1.symm.trans ?_
  exact (appLE_top_coordFrac (chartRatio s i) (span_range_chartRatio s i) i j
    (chartRatio_self s i) _).symm

include hα in
/-- **Uniqueness of the morphism to `ℙⁿ_ℤ` of Tag 01NE.** A morphism with a pinned isomorphism
`g ^* 𝒪(1) ≅ M` carrying `g ^* Tᵢ` to `sᵢ` is the glued morphism of the generating family. -/
theorem eq_toProjectiveSpaceAtUniverse_of_pinned (hs : GeneratesStalks s) :
    g = Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse s hs := by
  refine (X.openCoverOfIsOpenCover (nvCover s)
    (isOpenCover_nvCover_of_generatesStalks s hs)).hom_ext _ _ fun i => ?_
  exact (ι_comp_eq_chartHom_of_pinned s g α hα i).trans
    (Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse s hs i).symm

end Pinned

end Uniqueness

section Linear

open Stacks.AlgebraicGeometry.SectionsBaseChange

variable (w : letI := baseModule sC L ⊤; Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ(L, ⊤))

/-- **The `k`-linear coordinates on `H⁰(C, L)`** against a `k`-basis `w` (a basis over
`Γ(Spec k, ⊤) ≅ k`, the module structure being the one induced by the structure morphism). -/
def coefficients (t : Γ(L, ⊤)) : Fin N → k :=
  letI := baseModule sC L ⊤
  fun j => (Scheme.ΓSpecIso (.of k)).hom (w.repr t j)

omit [IsInvertibleModule C L] in
/-- **Every global section of `L` is the `k`-linear combination of the basis with its
coordinates.** -/
theorem eq_sum_coefficients (t : Γ(L, ⊤)) :
    t = ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (coefficients sC L w t j)) • w j := by
  let _ := baseModule sC L ⊤
  conv_lhs => rw [← w.sum_repr t]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Stacks.LinearSystemScheme.baseModule_smul_eq]
  simp [coefficients]

omit [IsInvertibleModule C L] in
/-- **Uniqueness of coordinates**: the coefficients of a `k`-linear combination of the basis are
the coefficients used. -/
theorem coefficients_sum (a : Fin N → k) :
    coefficients sC L w (∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a j)) • w j) = a := by
  let _ := baseModule sC L ⊤
  funext j
  have h : (∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a j)) • w j) =
      ∑ j, ((Scheme.ΓSpecIso (.of k)).inv (a j)) • w j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Stacks.LinearSystemScheme.baseModule_smul_eq]
  rw [coefficients, h, Module.Basis.repr_sum_self]
  simp

omit [IsInvertibleModule C L] in
/-- The coefficients of a sum of sections are the sums of the coefficients. -/
theorem coefficients_add (t t' : Γ(L, ⊤)) :
    coefficients sC L w (t + t') = coefficients sC L w t + coefficients sC L w t' := by
  let _ := baseModule sC L ⊤
  funext j
  simp [coefficients]

omit [IsInvertibleModule C L] in
/-- The coordinates are `k`-linear: scalar multiplication by `c ∈ k` acts through the structure
morphism. -/
theorem coefficients_smul (c : k) (t : Γ(L, ⊤)) :
    coefficients sC L w (sC.appTop ((Scheme.ΓSpecIso (.of k)).inv c) • t) =
      c • coefficients sC L w t := by
  let _ := baseModule sC L ⊤
  funext j
  rw [← Stacks.LinearSystemScheme.baseModule_smul_eq]
  simp [coefficients]

end Linear

section KPoint

open AlgebraicGeometry.SectionsEqualizer (pullbackGlobalSections_smul)

omit [IsInvertibleModule C L] in
/-- The coefficient point `a` carries the coordinate `x_{ij}` to `a_{ij}`. -/
theorem coefficientPoint_appTop_coord (a : Fin (n + 1) → Fin N → k) (i : Fin (n + 1))
    (j : Fin N) :
    (coefficientPoint (n := n) (N := N) a).appTop (coefficientCoord n N k i j) =
      (Scheme.ΓSpecIso (.of k)).inv (a i j) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

omit [IsInvertibleModule C L] in
/-- **The pulled-back universal section at a `k`-point.** At the `k`-point `a` of the coefficient
space, the pullback of the `i`-th universal section is the pullback of `Σⱼ a_{ij} e_j`. -/
theorem pullbackComp_familySection_coefficientPoint (a : Fin (n + 1) → Fin N → k)
    (i : Fin (n + 1)) (τ : Γ(L, ⊤))
    (hτ : τ = ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j) :
    ((Scheme.Modules.pullbackComp
        (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a))
        (pullback.fst sC (coefficientSpaceOver n N k))).hom.app L).app ⊤
      (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC)
        (coefficientPoint (n := n) (N := N) a) i) =
      AlgebraicGeometry.pullbackGlobalSections
        (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫
          pullback.fst sC (coefficientSpaceOver n N k)) L τ := by
  set g := coefficientPoint (n := n) (N := N) a with hg
  unfold familySection universalSection
  rw [Stacks.LinearSystemScheme.coordSection_pullback]
  unfold Stacks.LinearSystemScheme.coordSection
  rw [hτ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pullbackGlobalSections_smul]
  congr 1
  have h1 : (familyPullbackMap (n := n) (N := N) (sC := sC) g ≫
        pullback.snd sC (coefficientSpaceOver n N k)).appTop (coefficientCoord n N k i j) =
      (pullback.snd sC (g ≫ coefficientSpaceOver n N k)).appTop
        ((Scheme.ΓSpecIso (.of k)).inv (a i j)) := by
    rw [familyPullbackMap_snd, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      coefficientPoint_appTop_coord]
  rw [h1]
  have h2 : (familyPullbackMap (n := n) (N := N) (sC := sC) g ≫
        pullback.fst sC (coefficientSpaceOver n N k)).appTop
        (sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j))) =
      (pullback.snd sC (g ≫ coefficientSpaceOver n N k)).appTop
        ((Scheme.ΓSpecIso (.of k)).inv (a i j)) := by
    rw [familyPullbackMap_fst, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      pullback.condition, hg, coefficientPoint_over]
    simp
  exact h2.symm

end KPoint

section PinnedCompare

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

variable {X : Scheme.{u}} {n : ℕ} {M₁ M₂ : X.Modules} [IsInvertibleModule X M₁]

/-- **Two pinned morphisms to `ℙⁿ_ℤ` agree if their pinned data are identified.** Let `g₁` (resp.
`g₂`) carry an isomorphism `g_ν ^* 𝒪(1) ≅ M_ν` sending the pulled-back coordinates to the
sections `s_ν`; if `s₁` generates and `γ : M₁ ≅ M₂` carries `s₁` to `s₂`, then `g₁ = g₂`. -/
theorem eq_of_pinned_of_iso (s₁ : Fin (n + 1) → Γ(M₁, ⊤)) (s₂ : Fin (n + 1) → Γ(M₂, ⊤))
    (hs : GeneratesStalks s₁) (γ : M₁ ≅ M₂) (hγ : ∀ i, γ.hom.app ⊤ (s₁ i) = s₂ i)
    (g₁ g₂ : X ⟶ projectiveSpaceAtUniverse.{u} n)
    (α₁ : (Scheme.Modules.pullback g₁).obj (twistingSheafAtUniverse.{u} n) ⟶ M₁) [IsIso α₁]
    (hα₁ : ∀ i, α₁.app ⊤ (pullbackCoordSection.{u} g₁ i) = s₁ i)
    (α₂ : (Scheme.Modules.pullback g₂).obj (twistingSheafAtUniverse.{u} n) ⟶ M₂) [IsIso α₂]
    (hα₂ : ∀ i, α₂.app ⊤ (pullbackCoordSection.{u} g₂ i) = s₂ i) : g₁ = g₂ := by
  have hα₂' : ∀ i, (α₂ ≫ γ.inv).app ⊤ (pullbackCoordSection.{u} g₂ i) = s₁ i := by
    intro i
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hα₂, ← hγ,
      ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, γ.hom_inv_id]
    rfl
  exact (eq_toProjectiveSpaceAtUniverse_of_pinned s₁ g₁ α₁ hα₁ hs).trans
    (eq_toProjectiveSpaceAtUniverse_of_pinned s₁ g₂ (α₂ ≫ γ.inv) hα₂' hs).symm

/-- **Uniqueness of the morphism to `ℙⁿ_S`** (Stacks Tag 01NE): two morphisms to `ℙⁿ_S` over the
same morphism to `S`, with identified pinned data, are equal. -/
theorem eq_of_pinned_of_iso_over {S : Scheme.{u}} (s₁ : Fin (n + 1) → Γ(M₁, ⊤))
    (s₂ : Fin (n + 1) → Γ(M₂, ⊤))
    (hs : GeneratesStalks s₁) (γ : M₁ ≅ M₂) (hγ : ∀ i, γ.hom.app ⊤ (s₁ i) = s₂ i)
    (p₁ p₂ : X ⟶ projectiveSpaceOver n S)
    (hover : p₁ ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      p₂ ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)))
    (r₁ r₂ : X ⟶ projectiveSpaceAtUniverse.{u} n)
    (hr₁ : p₁ ≫ projectiveSpaceOver.toIntegralAtUniverse n S = r₁)
    (hr₂ : p₂ ≫ projectiveSpaceOver.toIntegralAtUniverse n S = r₂)
    (α₁ : (Scheme.Modules.pullback r₁).obj (twistingSheafAtUniverse.{u} n) ⟶ M₁) [IsIso α₁]
    (hα₁ : ∀ i, α₁.app ⊤ (pullbackCoordSection.{u} r₁ i) = s₁ i)
    (α₂ : (Scheme.Modules.pullback r₂).obj (twistingSheafAtUniverse.{u} n) ⟶ M₂) [IsIso α₂]
    (hα₂ : ∀ i, α₂.app ⊤ (pullbackCoordSection.{u} r₂ i) = s₂ i) : p₁ = p₂ := by
  refine pullback.hom_ext hover ?_
  change p₁ ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
    p₂ ≫ projectiveSpaceOver.toIntegralAtUniverse n S
  rw [hr₁, hr₂]
  exact eq_of_pinned_of_iso s₁ s₂ hs γ hγ _ _ α₁ hα₁ α₂ hα₂

omit [IsInvertibleModule X M₁] in
/-- **Two tuples define the same map exactly when an isomorphism of the line bundles carries one
tuple to the other.** If `g` carries pinned isomorphisms `g ^* 𝒪(1) ≅ M_ν` to the tuples `s_ν`,
then `M₁ ≅ M₂` by an isomorphism carrying `s₁` to `s₂`. (For `M₁ = M₂ = L` on a proper integral
curve over `k`, such an automorphism is a scalar, which the coefficient normalisation removes.) -/
theorem exists_iso_of_pinned_same_hom {M₂ : X.Modules} (g : X ⟶ projectiveSpaceAtUniverse.{u} n)
    (s₁ : Fin (n + 1) → Γ(M₁, ⊤)) (s₂ : Fin (n + 1) → Γ(M₂, ⊤))
    (α₁ : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n) ⟶ M₁) [IsIso α₁]
    (hα₁ : ∀ i, α₁.app ⊤ (pullbackCoordSection.{u} g i) = s₁ i)
    (α₂ : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n) ⟶ M₂) [IsIso α₂]
    (hα₂ : ∀ i, α₂.app ⊤ (pullbackCoordSection.{u} g i) = s₂ i) :
    ∃ γ : M₁ ≅ M₂, ∀ i, γ.hom.app ⊤ (s₁ i) = s₂ i := by
  refine ⟨(asIso α₁).symm ≪≫ asIso α₂, fun i => ?_⟩
  change (inv α₁ ≫ α₂).app ⊤ (s₁ i) = s₂ i
  rw [← hα₁ i, ← hα₂ i]
  simp [Scheme.Modules.Hom.comp_app]

end PinnedCompare

section Fibre

variable {sC L e} {T : Scheme.{u}} (g : T ⟶ coefficientSpace n N k)

/-- **`C ×ₖ T` is the fibre product of `C ×ₖ 𝔸 → 𝔸` with `T → 𝔸`.** -/
theorem isPullback_familyPullbackMap :
    IsPullback (familyPullbackMap (n := n) (N := N) (sC := sC) g)
      (pullback.snd sC (g ≫ coefficientSpaceOver n N k))
      (pullback.snd sC (coefficientSpaceOver n N k)) g := by
  refine IsPullback.of_right (h₁₂ := pullback.fst sC (coefficientSpaceOver n N k))
    (h₂₂ := coefficientSpaceOver n N k) ?_ (familyPullbackMap_snd (n := n) (N := N) g)
    (IsPullback.of_hasPullback _ _)
  rw [familyPullbackMap_fst]
  exact IsPullback.of_hasPullback _ _

/-- A point of `C ×ₖ 𝔸` over the image of a point of `T` comes from `C ×ₖ T`. -/
theorem exists_preimage_familyPullbackMap (x : universalCurve (n := n) (N := N) sC) (t : T)
    (hx : (pullback.snd sC (coefficientSpaceOver n N k)).base x = g.base t) :
    ∃ x' : ↥(pullback sC (g ≫ coefficientSpaceOver n N k)),
      (familyPullbackMap (n := n) (N := N) (sC := sC) g).base x' = x ∧
      (pullback.snd sC (g ≫ coefficientSpaceOver n N k)).base x' = t := by
  have H := isPullback_familyPullbackMap (n := n) (N := N) (sC := sC) g
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x t hx
  have e1 := H.isoPullback_hom_fst
  have e2 := H.isoPullback_hom_snd
  have hz : (H.isoPullback.hom) ((H.isoPullback.inv) z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; simp
  refine ⟨(H.isoPullback.inv) z, ?_, ?_⟩
  · have := congrArg (fun φ => φ ((H.isoPullback.inv) z)) e1
    simp only [Scheme.Hom.comp_apply, hz] at this
    rw [← this, hz1]
  · have := congrArg (fun φ => φ ((H.isoPullback.inv) z)) e2
    simp only [Scheme.Hom.comp_apply, hz] at this
    rw [← this, hz2]

end Fibre

section Restriction

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

/-- **Pinned data pulled back along a morphism**: if `λ : g'^* O ⟶ L` and `q : X' ⟶ X`, the
section `(q ≫ g')^* s` of `(q ≫ g')^* O` corresponds, under the comparison of iterated pullbacks
followed by `q^* λ`, to `q^* (λ (g'^* s))`. -/
theorem pullbackComp_inv_map_pullbackGlobalSections {X' X Y : Scheme.{u}} (q : X' ⟶ X)
    (g' : X ⟶ Y) {O : Y.Modules} {L' : X.Modules}
    (l : (Scheme.Modules.pullback g').obj O ⟶ L') (s : Γ(O, ⊤)) :
    ((Scheme.Modules.pullbackComp q g').inv.app O ≫ (Scheme.Modules.pullback q).map l).app ⊤
        (AlgebraicGeometry.pullbackGlobalSections (q ≫ g') O s) =
      AlgebraicGeometry.pullbackGlobalSections q L' (l.app ⊤
        (AlgebraicGeometry.pullbackGlobalSections g' O s)) := by
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    AlgebraicGeometry.pullbackGlobalSections_natural,
    ← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp q g' O s]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app]
  rfl

end Restriction

section BaseChange

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

/-- **Compatibility of pulled-back sections with an equality of morphisms**: if `h' = r ≫ h`,
the iterated pullback of `M` along `h` and `r` is isomorphic to its pullback along `h'`, carrying
the iterated pullback of a section to its pullback. -/
theorem exists_iso_pullbackGlobalSections_comp {X' X Y : Scheme.{u}} (r : X' ⟶ X) (h : X ⟶ Y)
    (h' : X' ⟶ Y) (hE : h' = r ≫ h) (M : Y.Modules) :
    ∃ γ : (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback h).obj M) ≅
        (Scheme.Modules.pullback h').obj M, ∀ U : Γ(M, ⊤),
      γ.hom.app ⊤ (AlgebraicGeometry.pullbackGlobalSections r _
        (AlgebraicGeometry.pullbackGlobalSections h M U)) =
        AlgebraicGeometry.pullbackGlobalSections h' M U := by
  subst hE
  exact ⟨(Scheme.Modules.pullbackComp r h).app M,
    fun U => AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp r h M U⟩

variable {sC L e} {T T' : Scheme.{u}}

/-- **Base change of the family**: for `q : T' ⟶ T` and a `T`-point `g` of the coefficient space,
the induced morphism `C ×ₖ T' ⟶ C ×ₖ T`. -/
def familyBaseChange (g : T ⟶ coefficientSpace n N k) (q : T' ⟶ T) :
    pullback sC (q ≫ g ≫ coefficientSpaceOver n N k) ⟶
      pullback sC (g ≫ coefficientSpaceOver n N k) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ q) (by simp [pullback.condition])

/-- The first projection of `C ×ₖ T' → C ×ₖ T` is the first projection of `C ×ₖ T'`. -/
@[reassoc (attr := simp)]
theorem familyBaseChange_fst (g : T ⟶ coefficientSpace n N k) (q : T' ⟶ T) :
    familyBaseChange (sC := sC) g q ≫ pullback.fst sC (g ≫ coefficientSpaceOver n N k) =
      pullback.fst sC (q ≫ g ≫ coefficientSpaceOver n N k) :=
  pullback.lift_fst _ _ _

/-- The second projection of `C ×ₖ T' → C ×ₖ T` is the second projection of `C ×ₖ T'` followed by
`q`. -/
@[reassoc (attr := simp)]
theorem familyBaseChange_snd (g : T ⟶ coefficientSpace n N k) (q : T' ⟶ T) :
    familyBaseChange (sC := sC) g q ≫ pullback.snd sC (g ≫ coefficientSpaceOver n N k) =
      pullback.snd sC (q ≫ g ≫ coefficientSpaceOver n N k) ≫ q :=
  pullback.lift_snd _ _ _

/-- The map `C ×ₖ T' → C ×ₖ 𝔸` of the `T'`-point `q ≫ g` factors through `C ×ₖ T` by the base
change along `q`. -/
theorem familyPullbackMap_comp (g : T ⟶ coefficientSpace n N k) (q : T' ⟶ T) :
    familyPullbackMap (n := n) (N := N) (sC := sC) (q ≫ g) =
      familyBaseChange (sC := sC) g q ≫ familyPullbackMap (n := n) (N := N) (sC := sC) g := by
  refine pullback.hom_ext ?_ ?_
  · rw [familyPullbackMap_fst]
    exact ((familyBaseChange_fst (sC := sC) g q).symm.trans
      (congrArg (familyBaseChange (sC := sC) g q ≫ ·)
        (familyPullbackMap_fst (n := n) (N := N) (sC := sC) g).symm)).trans
      (Category.assoc _ _ _).symm
  · rw [familyPullbackMap_snd]
    have h1 := familyBaseChange_snd (sC := sC) g q
    have h2 := familyPullbackMap_snd (n := n) (N := N) (sC := sC) g
    exact (congrArg (pullback.snd sC ((q ≫ g) ≫ coefficientSpaceOver n N k) ≫ ·) rfl).trans
      (((congrArg (· ≫ g) h1.symm).trans (Category.assoc _ _ _)).trans
        ((congrArg (familyBaseChange (sC := sC) g q ≫ ·) h2.symm).trans
          (Category.assoc _ _ _).symm))

end BaseChange

section Restriction2

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

/-- **The family of maps restricts at a `k`-point of the coefficient space to the map `f` that
the tuple comes from** (Stacks Tag 01NE, uniqueness). Let `f : C ⟶ ℙⁿ_k` be a morphism over `k`
whose pulled-back coordinates `f^* Tᵢ` correspond, under an isomorphism `f^* 𝒪(1) ≅ L`, to the
sections `τᵢ = Σⱼ aᵢⱼ eⱼ` of `L`, and let `a` have no common zero. Then any morphism
`p : C ×ₖ Spec k ⟶ ℙⁿ_k` with a pinned isomorphism to the pulled-back universal tuple at `a`
(for instance the one of `exists_familyMap_iso_pullback_twistingSheaf`) is `f` composed with the
projection `C ×ₖ Spec k ⟶ C`. -/
theorem familyMap_coefficientPoint_eq [IsProper sC] (a : Fin (n + 1) → Fin N → k)
    (g : Spec (.of k) ⟶ coefficientSpace n N k) (hg : g = coefficientPoint (n := n) (N := N) a)
    (ha : ∀ t, g.base t ∈ noCommonZeroOpen (n := n) sC L e)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (p : pullback sC (g ≫ coefficientSpaceOver n N k) ⟶
      projectiveSpaceOver n (Spec (.of k)))
    (hp : p ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      pullback.fst sC (g ≫ coefficientSpaceOver n N k) ≫ sC)
    (α : (Scheme.Modules.pullback (p ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ≅
        familyModule (n := n) (N := N) (L := L) (sC := sC)
          g)
    (hα : ∀ i, α.hom.app ⊤ (pullbackCoordSection.{u}
        (p ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      familySection (n := n) (N := N) (L := L) (e := e) (sC := sC)
        g i) :
    p = (familyPullbackMap (n := n) (N := N) (sC := sC) g ≫
        pullback.fst sC (coefficientSpaceOver n N k)) ≫ f := by
  subst hg
  have hs := generatesStalks_familySection (n := n) (N := N) (L := L) (e := e) (sC := sC) (coefficientPoint (n := n) (N := N) a) ha
  refine eq_of_pinned_of_iso_over (X := pullback sC (coefficientPoint (n := n) (N := N) a ≫ coefficientSpaceOver n N k))
    (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC) (coefficientPoint (n := n) (N := N) a))
    (fun i => AlgebraicGeometry.pullbackGlobalSections (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫ pullback.fst sC (coefficientSpaceOver n N k)) L
      (l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i)))
    hs
    ((Scheme.Modules.pullbackComp (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a))
      (pullback.fst sC (coefficientSpaceOver n N k))).app L) ?_ p ((familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫ pullback.fst sC (coefficientSpaceOver n N k)) ≫ f) ?_ _ ((familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫ pullback.fst sC (coefficientSpaceOver n N k)) ≫ f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) rfl rfl α.hom hα
    ((Scheme.Modules.pullbackComp (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫ pullback.fst sC (coefficientSpaceOver n N k)) (f ≫ projectiveSpaceOver.toIntegralAtUniverse n
      (Spec (.of k)))).inv.app (twistingSheafAtUniverse.{u} n) ≫ (Scheme.Modules.pullback (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫ pullback.fst sC (coefficientSpaceOver n N k))).map l) ?_
  · intro i
    exact pullbackComp_familySection_coefficientPoint (n := n) (N := N) (L := L) (e := e)
      (sC := sC) a i _ (hτ i)
  · rw [hp, Category.assoc, hf, familyPullbackMap_fst]
  · intro i
    exact pullbackComp_inv_map_pullbackGlobalSections _ _ l (coordGlobalSection.{u} n i)

/-- **The `k`-point of a tuple that generates `L` has no common zero.** If the sections
`τᵢ = Σⱼ aᵢⱼ eⱼ` correspond to the pulled-back coordinates of a morphism `f : C ⟶ ℙⁿ_k`, the
`k`-point `a` of the coefficient space lies in the locus of tuples without common zero. -/
theorem coefficientPoint_mem_noCommonZeroOpen [IsProper sC] (a : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j) :
    ∀ t, (coefficientPoint (n := n) (N := N) a).base t ∈ noCommonZeroOpen (n := n) sC L e := by
  intro t ⟨x, hx, hxt⟩
  obtain ⟨x', hx1, hx2⟩ := exists_preimage_familyPullbackMap (n := n) (N := N) (sC := sC)
    (coefficientPoint (n := n) (N := N) a) x t hxt
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_coord n
    ((f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))).base
      ((familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫ pullback.fst sC (coefficientSpaceOver n N k)).base x'))
  have hq : (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫ pullback.fst sC (coefficientSpaceOver n N k)).base x' ∈ nonvanishingLocus L (l.app ⊤ (pullbackCoordSection.{u}
      (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i)) := by
    have h2 : nonvanishingLocus L (l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i)) =
        nonvanishingLocus ((Scheme.Modules.pullback
          (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
          (twistingSheafAtUniverse.{u} n))
        (pullbackCoordSection.{u}
          (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) :=
      nonvanishingLocus_app_top_eq_of_iso (asIso l) _
    rw [h2]
    exact (mem_nonvanishingLocus_pullbackCoordSection_iff _ i _).2 hi
  have h1 := (mem_nonvanishingLocus_pullbackGlobalSections_iff (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫ pullback.fst sC (coefficientSpaceOver n N k)) L _ x').2 hq
  have hγ := pullbackComp_familySection_coefficientPoint (n := n) (N := N) (L := L) (e := e)
    (sC := sC) a i _ (hτ i)
  have h2 : x' ∈ nonvanishingLocus (familyModule (n := n) (N := N) (L := L) (sC := sC)
      (coefficientPoint (n := n) (N := N) a))
      (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC)
        (coefficientPoint (n := n) (N := N) a) i) := by
    have h4 : nonvanishingLocus ((Scheme.Modules.pullback (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a) ≫ pullback.fst sC (coefficientSpaceOver n N k))).obj L)
        (((Scheme.Modules.pullbackComp (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a))
          (pullback.fst sC (coefficientSpaceOver n N k))).hom.app L).app ⊤ (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC)
        (coefficientPoint (n := n) (N := N) a) i)) =
        nonvanishingLocus (familyModule (n := n) (N := N) (L := L) (sC := sC)
          (coefficientPoint (n := n) (N := N) a)) (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC)
        (coefficientPoint (n := n) (N := N) a) i) :=
      nonvanishingLocus_app_top_eq_of_iso
        ((Scheme.Modules.pullbackComp (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a))
          (pullback.fst sC (coefficientSpaceOver n N k))).app L) _
    rw [← h4, hγ]
    exact h1
  have h3 := (mem_nonvanishingLocus_pullbackGlobalSections_iff (familyPullbackMap (n := n) (N := N) (sC := sC) (coefficientPoint (n := n) (N := N) a)) _ _ x').1 h2
  rw [hx1] at h3
  exact hx (Set.mem_iUnion.2 ⟨i, h3⟩)

end Restriction2

section Compatibility

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

/-- **The universal family restricts at a `k`-point of the scheme of tuples without common zero
to the map `f` the tuple comes from.** This is the statement `Φ|_{[f]} = f`: for a `k`-point `m`
of `M₁` over the coefficients `a` with `Σⱼ aᵢⱼ eⱼ = τᵢ`, where `τᵢ` is the section of `L`
corresponding to the `i`-th pulled-back coordinate of a morphism `f : C ⟶ ℙⁿ_k` over `k`
(an isomorphism `f^* 𝒪(1) ≅ L` carries `f^* Tᵢ` to `τᵢ`), the base change of the family `Φ`
along `m` is the projection `C ×ₖ Spec k ⟶ C` followed by `f`. -/
theorem noCommonZeroFamily_base_change_eq [IsProper sC] (a : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (m : Spec (.of k) ⟶ noCommonZeroScheme (n := n) sC L e)
    (hm : m ≫ noCommonZeroScheme.ι (n := n) sC L e = coefficientPoint (n := n) (N := N) a) :
    familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m ≫
        noCommonZeroFamily (n := n) sC L e =
      (familyPullbackMap (n := n) (N := N) (sC := sC)
          (m ≫ noCommonZeroScheme.ι (n := n) sC L e) ≫
        pullback.fst sC (coefficientSpaceOver n N k)) ≫ f := by
  obtain ⟨αM, hiso, hαM⟩ := exists_iso_noCommonZeroFamily (n := n) sC L e
  have := hiso
  obtain ⟨γ, hγ⟩ := exists_iso_pullbackGlobalSections_comp
    (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m)
    (familyPullbackMap (n := n) (N := N) (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e))
    (familyPullbackMap (n := n) (N := N) (sC := sC) (m ≫ noCommonZeroScheme.ι (n := n) sC L e))
    (familyPullbackMap_comp _ m)
    ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
  let α₁ := ((((Scheme.Modules.pullbackComp (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m)
      (noCommonZeroFamily (n := n) sC L e ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).app
        (twistingSheafAtUniverse.{u} n)).symm ≪≫
      (Scheme.Modules.pullback (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m)).mapIso (asIso αM)) ≪≫ γ)
  refine familyMap_coefficientPoint_eq (n := n) (N := N) (L := L) (e := e) (sC := sC) a
    (m ≫ noCommonZeroScheme.ι (n := n) sC L e) hm
    (fun t => base_noCommonZeroScheme_ι_mem sC L e (m.base t)) f hf l hτ
    ((familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m) ≫ noCommonZeroFamily (n := n) sC L e) ?_ α₁ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg ((familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m) ≫ ·)
      (noCommonZeroFamily_over (n := n) sC L e)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ sC)
        (familyBaseChange_fst (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m))))
  · intro i
    have h1 := pullbackComp_inv_map_pullbackGlobalSections (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m)
      (noCommonZeroFamily (n := n) sC L e ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) αM
      (coordGlobalSection.{u} n i)
    have h2 := hγ (universalSection (n := n) sC L e i)
    change γ.hom.app ⊤ (((Scheme.Modules.pullbackComp (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m)
      (noCommonZeroFamily (n := n) sC L e ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).inv.app
        (twistingSheafAtUniverse.{u} n) ≫
      (Scheme.Modules.pullback (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m)).map αM).app ⊤
      (AlgebraicGeometry.pullbackGlobalSections ((familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m) ≫ (noCommonZeroFamily (n := n) sC L e ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))) _
        (coordGlobalSection.{u} n i))) = _
    rw [h1]
    exact (congrArg (fun z => γ.hom.app ⊤
      (AlgebraicGeometry.pullbackGlobalSections (familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m) _ z)) (hαM i)).trans h2

end Compatibility

section ZeroLocus

/-- A morphism `g : T ⟶ Spec S` factors as `T → Spec Γ(T, 𝒪_T) → Spec S`, the second map induced by
`g` on global sections. -/
theorem eq_toSpecΓ_comp_map {S : CommRingCat.{u}} {T : Scheme.{u}} (g : T ⟶ Spec S) :
    g = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso S).inv ≫ g.appTop) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality ((Scheme.ΓSpecIso S).inv ≫ g.appTop)]
  simp

/-- The closed subscheme of `Spec S` cut out by an ideal. -/
noncomputable def specQuotientι (S : CommRingCat.{u}) (I : Ideal S) :
    Spec (.of (S ⧸ I)) ⟶ Spec S := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- A morphism `g : T ⟶ Spec S` factors through `Spec (S ⧸ I)` iff `g` kills every element of `I`
on global sections. -/
theorem exists_lift_specQuotientι {S : CommRingCat.{u}} (I : Ideal S) {T : Scheme.{u}}
    (g : T ⟶ Spec S) :
    (∃ h : T ⟶ Spec (.of (S ⧸ I)), h ≫ specQuotientι S I = g) ↔
      ∀ x ∈ I, g.appTop ((Scheme.ΓSpecIso S).inv x) = 0 := by
  constructor
  · rintro ⟨h, rfl⟩ x hx
    have := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))) x)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.2 hx,
      map_zero] at this
    rw [specQuotientι, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact (congrArg h.appTop.hom this.symm).trans (map_zero _)
  · intro hx
    refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I
      ((Scheme.ΓSpecIso S).inv ≫ g.appTop).hom hx)), ?_⟩
    rw [specQuotientι, Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom (Ideal.Quotient.lift I
      ((Scheme.ΓSpecIso S).inv ≫ g.appTop).hom hx) = (Scheme.ΓSpecIso S).inv ≫ g.appTop := by
      ext
      simp
    rw [this]
    exact (eq_toSpecΓ_comp_map g).symm

/-- The closed subscheme `Spec (Γ(A) ⧸ I)` of an affine scheme `A`. -/
noncomputable abbrev affineClosedSubscheme (A : Scheme.{u}) [IsAffine A] (I : Ideal Γ(A, ⊤)) :
    Scheme.{u} := Spec (.of (Γ(A, ⊤) ⧸ I))

/-- The closed immersion `Spec (Γ(A, 𝒪_A) ⧸ I) ⟶ A`. -/
noncomputable def affineClosedSubscheme.ι (A : Scheme.{u}) [IsAffine A] (I : Ideal Γ(A, ⊤)) :
    affineClosedSubscheme A I ⟶ A := specQuotientι Γ(A, ⊤) I ≫ A.isoSpec.inv

/-- `Spec (S ⧸ I) ⟶ Spec S` is a closed immersion. -/
instance (S : CommRingCat.{u}) (I : Ideal S) : IsClosedImmersion (specQuotientι S I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- `Spec (Γ(A, 𝒪_A) ⧸ I) ⟶ A` is a closed immersion. -/
instance (A : Scheme.{u}) [IsAffine A] (I : Ideal Γ(A, ⊤)) :
    IsClosedImmersion (affineClosedSubscheme.ι A I) := by
  unfold affineClosedSubscheme.ι
  infer_instance

/-- A morphism `g : T ⟶ A` to an affine scheme factors through the closed subscheme cut out by `I`
iff `g` kills every element of `I` on global sections. -/
theorem exists_lift_affineClosedSubscheme_ι (A : Scheme.{u}) [IsAffine A] (I : Ideal Γ(A, ⊤))
    {T : Scheme.{u}} (g : T ⟶ A) :
    (∃ h : T ⟶ affineClosedSubscheme A I, h ≫ affineClosedSubscheme.ι A I = g) ↔
      ∀ x ∈ I, g.appTop x = 0 := by
  have key : ∀ (h : T ⟶ Spec (.of (Γ(A, ⊤) ⧸ I))),
      h ≫ affineClosedSubscheme.ι A I = g ↔ (h ≫ specQuotientι Γ(A, ⊤) I) = g ≫ A.isoSpec.hom :=
    fun h => by rw [affineClosedSubscheme.ι, ← Category.assoc, Iso.comp_inv_eq]
  rw [exists_congr key, exists_lift_specQuotientι]
  refine forall₂_congr fun x hx => ?_
  have : (g ≫ A.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(A, ⊤)).inv x) = g.appTop x := by
    rw [Scheme.Hom.comp_appTop]
    simp [Scheme.isoSpec, Scheme.toSpecΓ_appTop]
  rw [this]

/-- **The closed subscheme of an affine scheme cut out by finitely many (or any family of) global
functions** `p`. -/
noncomputable abbrev zeroLocusScheme (A : Scheme.{u}) [IsAffine A] {ι : Type*}
    (p : ι → Γ(A, ⊤)) : Scheme.{u} :=
  affineClosedSubscheme A (Ideal.span (Set.range p))

/-- The closed immersion of the zero locus of a family of global functions. -/
noncomputable abbrev zeroLocusScheme.ι (A : Scheme.{u}) [IsAffine A] {ι : Type*}
    (p : ι → Γ(A, ⊤)) : zeroLocusScheme A p ⟶ A :=
  affineClosedSubscheme.ι A (Ideal.span (Set.range p))

/-- **Universal property of the zero locus.** A morphism `g : T ⟶ A` factors through the zero
locus of the family `p` if and only if the pulled-back functions `g^* p_i` all vanish. The
factorization is unique, the zero locus being a closed immersion (`zeroLocusScheme.ι` is a
monomorphism). -/
theorem exists_lift_zeroLocusScheme_ι_iff (A : Scheme.{u}) [IsAffine A] {ι : Type*}
    (p : ι → Γ(A, ⊤)) {T : Scheme.{u}} (g : T ⟶ A) :
    (∃ h : T ⟶ zeroLocusScheme A p, h ≫ zeroLocusScheme.ι A p = g) ↔
      ∀ i, g.appTop (p i) = 0 := by
  rw [exists_lift_affineClosedSubscheme_ι]
  constructor
  · intro h i
    exact h _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro h x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩; exact h i
    · exact map_zero _
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro a b _ hb; rw [smul_eq_mul, map_mul, hb, mul_zero]

/-- The closed immersion of a zero locus is a monomorphism. -/
theorem zeroLocusScheme.ι_cancel (A : Scheme.{u}) [IsAffine A] {ι : Type*}
    (p : ι → Γ(A, ⊤)) {T : Scheme.{u}} (h₁ h₂ : T ⟶ zeroLocusScheme A p)
    (h : h₁ ≫ zeroLocusScheme.ι A p = h₂ ≫ zeroLocusScheme.ι A p) : h₁ = h₂ :=
  (cancel_mono _).1 h

end ZeroLocus

section Equations

open Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.LinearSystemScheme

variable [IsProper sC] {L' : C.Modules} [L'.IsQuasicoherent] {N' : ℕ}
  (w' : letI := baseModule sC L' ⊤; Module.Basis (Fin N') Γ(Spec (.of k), ⊤) Γ(L', ⊤))

omit [IsProper sC] in
/-- `C ×ₖ 𝔸` is the pullback of `C → Spec k` along `𝔸 → Spec k`. -/
theorem isPullback_universalCurve :
    IsPullback (pullback.fst sC (coefficientSpaceOver n N k))
      (pullback.snd sC (coefficientSpaceOver n N k)) sC (coefficientSpaceOver n N k) :=
  IsPullback.of_hasPullback _ _

/-- The coefficient space is flat over `k`. -/
instance : Flat (coefficientSpaceOver n N k) := by
  unfold coefficientSpaceOver
  infer_instance

/-- Every global section of `pr_C^* L'` on `C ×ₖ 𝔸` is `Σ_j f_j · w'_j` for a unique tuple of
global functions `f_j` on `𝔸`. -/
theorem coordSection_bijective_universalCurve :
    Function.Bijective (coordSection (pullback.fst sC (coefficientSpaceOver n N k))
      (pullback.snd sC (coefficientSpaceOver n N k)) L' w') := by
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated sC
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  exact coordSection_bijective (isPullback_universalCurve (n := n) (N := N) sC) L' w'

/-- **The coefficients of a section of `pr_C^* L'` on `C ×ₖ 𝔸`** against the `k`-basis `w'` of
`H⁰(C, L')`: the functions `c_j` on `𝔸` with `ρ = Σⱼ c_j · w'_j` (degree-zero flat base change). -/
def coefficientFunctions
    (ρ : Γ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L', ⊤)) :
    Fin N' → Γ(coefficientSpace n N k, ⊤) :=
  (Equiv.ofBijective _ (coordSection_bijective_universalCurve (n := n) (N := N) sC w')).symm ρ

/-- The section `Σ_j f_j · w'_j` built from the coefficient functions `f_j` of `ρ` is `ρ`. -/
theorem coordSection_coefficientFunctions
    (ρ : Γ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L', ⊤)) :
    coordSection (pullback.fst sC (coefficientSpaceOver n N k))
      (pullback.snd sC (coefficientSpaceOver n N k)) L' w'
      (coefficientFunctions (n := n) (N := N) sC w' ρ) = ρ :=
  (Equiv.ofBijective _ (coordSection_bijective_universalCurve (n := n) (N := N) sC w')).apply_symm_apply ρ

/-- **Substitution commutes with base change, in coordinates, and vanishes iff the coefficients
do.** For an affine `k`-scheme `T` and a `T`-point `g` of the coefficient space, the pullback of a
section `ρ` of `pr_C^* L'` to `C ×ₖ T` vanishes if and only if the pulled-back coefficient
functions `g^* c_j` all vanish. -/
theorem pullback_eq_zero_iff_coefficientFunctions {T : Scheme.{u}} [IsAffine T]
    (g : T ⟶ coefficientSpace n N k)
    (ρ : Γ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L', ⊤)) :
    ((Scheme.Modules.pullbackComp (familyPullbackMap (n := n) (N := N) (sC := sC) g)
        (pullback.fst sC (coefficientSpaceOver n N k))).hom.app L').app ⊤
      (AlgebraicGeometry.pullbackGlobalSections
        (familyPullbackMap (n := n) (N := N) (sC := sC) g) _ ρ) = 0 ↔
    ∀ j, g.appTop (coefficientFunctions (n := n) (N := N) sC w' ρ j) = 0 := by
  have key := coordSection_pullback (familyPullbackMap (n := n) (N := N) (sC := sC) g)
    (pullback.fst sC (coefficientSpaceOver n N k))
    (pullback.snd sC (coefficientSpaceOver n N k)) L' w'
    (coefficientFunctions (n := n) (N := N) sC w' ρ)
  rw [coordSection_coefficientFunctions] at key
  rw [key]
  have e : coordSection (familyPullbackMap (n := n) (N := N) (sC := sC) g ≫
        pullback.fst sC (coefficientSpaceOver n N k))
      (familyPullbackMap (n := n) (N := N) (sC := sC) g ≫
        pullback.snd sC (coefficientSpaceOver n N k)) L' w'
      (coefficientFunctions (n := n) (N := N) sC w' ρ) =
      coordSection (familyPullbackMap (n := n) (N := N) (sC := sC) g ≫
          pullback.fst sC (coefficientSpaceOver n N k))
        (pullback.snd sC (g ≫ coefficientSpaceOver n N k)) L' w'
        (fun j => g.appTop (coefficientFunctions (n := n) (N := N) sC w' ρ j)) := by
    simp only [coordSection, familyPullbackMap_snd,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [e]
  have H : IsPullback (familyPullbackMap (n := n) (N := N) (sC := sC) g ≫
        pullback.fst sC (coefficientSpaceOver n N k))
      (pullback.snd sC (g ≫ coefficientSpaceOver n N k)) sC (g ≫ coefficientSpaceOver n N k) := by
    rw [familyPullbackMap_fst]
    exact IsPullback.of_hasPullback _ _
  have : Flat (g ≫ coefficientSpaceOver n N k) := inferInstance
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated sC
  have hb := coordSection_bijective H L' w'
  have h0 : coordSection (familyPullbackMap (n := n) (N := N) (sC := sC) g ≫
        pullback.fst sC (coefficientSpaceOver n N k))
        (pullback.snd sC (g ≫ coefficientSpaceOver n N k)) L' w' 0 = 0 := by
    simp [coordSection]
  rw [← h0, hb.1.eq_iff]
  exact funext_iff

end Equations

section Substitution

open Stacks.GradedSections (powSections sectionRing)
open Stacks.Algebraization (degreeOneSection)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) (M : X.Modules) [IsInvertibleModule X M]

/-- **The substitution of a tuple of sections into a polynomial**, in the section ring
`⨁ₑ Γ(X, M^{⊗e})`: the element `F(σ₀, …, σₙ)`, where the base field acts through the global
functions of `X` put in degree zero. -/
def substitutedElement (σ : Fin (n + 1) → Γ(M, ⊤)) (F : MvPolynomial (Fin (n + 1)) k) :
    sectionRing M :=
  letI := Stacks.SectionRingGeometric.schemeSectionCommRing X M
  MvPolynomial.eval₂ ((Stacks.SectionRingZero.sectionRingZeroHom X M).comp
    (RingHom.comp π.appTop.hom (Scheme.ΓSpecIso (.of k)).inv.hom))
    (fun i => DirectSum.of (powSections M) 1 (degreeOneSection M (σ i))) F

/-- **The degree-`d` component of `F(σ)`**, a global section of `M^{⊗d}`; for a form `F` of
degree `d` it is the whole of `F(σ)`. -/
def substitutedSection (σ : Fin (n + 1) → Γ(M, ⊤)) (F : MvPolynomial (Fin (n + 1)) k) (d : ℕ) :
    powSections M d :=
  substitutedElement π M σ F d

end Substitution

section EquationFunctions

open Stacks.GradedSections (powSections sectionRing)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.SectionsBaseChange

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable [IsProper sC] (d : ℕ) {N' : ℕ}
  (w' : letI := baseModule sC (Stacks.TensorPowers.natTensorPow L d) ⊤;
    Module.Basis (Fin N') Γ(Spec (.of k), ⊤) Γ(Stacks.TensorPowers.natTensorPow L d, ⊤))

/-- **The substituted equation as a section of `pr_C^* (L^{⊗d})`.** The form `F` of degree `d`
evaluated on the universal tuple is a global section of `(pr_C^* L)^{⊗d}` on `C ×ₖ 𝔸`
(`Stacks.Algebraization.degreeOneSection` and the graded product); it is read as a section of
`pr_C^* (L^{⊗d})` through the comparison `pullbackNatTensorPowIso`. -/
def substitutedUniversalSection (F : MvPolynomial (Fin (n + 1)) k) :
    Γ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj
      (Stacks.TensorPowers.natTensorPow L d), ⊤) :=
  (pullbackNatTensorPowIso (pullback.fst sC (coefficientSpaceOver n N k)) L d).hom.app ⊤
    (Stacks.SectionProduct.globalSection _ _
      (substitutedSection (pullback.fst sC (coefficientSpaceOver n N k) ≫ sC)
        ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
        (universalSection (n := n) sC L e) F d))

end EquationFunctions

section Avoid

variable [IsProper sC] {T : Scheme.{u}} (sT : T ⟶ Spec (.of k)) {Y : Scheme.{u}}

/-- **The locus of a parameter scheme over which a family of maps avoids a closed set.** For a
proper `k`-scheme `C`, a family `Ψ : C ×ₖ T → Y` and a closed subset `Z ⊆ Y`, the set of
`t ∈ T` such that no point of `C ×ₖ T` over `t` is sent into `Z` is open: its complement is the
image under the closed map `C ×ₖ T → T` (a base change of the proper `C → Spec k`) of the closed
set `Ψ⁻¹ Z`. -/
def avoidOpen (Ψ : pullback sC sT ⟶ Y) (Z : Set Y) (hZ : IsClosed Z) : T.Opens :=
  ⟨(pullback.snd sC sT '' (Ψ.base ⁻¹' Z))ᶜ, by
    rw [isOpen_compl_iff]
    exact (pullback.snd sC sT).isClosedMap _ (hZ.preimage Ψ.base.hom.continuous)⟩

/-- `t` lies in `avoidOpen` iff `Ψ` maps no point of the fibre of `C ×ₖ T` over `t` into `Z`. -/
theorem mem_avoidOpen_iff (Ψ : pullback sC sT ⟶ Y) (Z : Set Y) (hZ : IsClosed Z) (t : T) :
    t ∈ avoidOpen sC sT Ψ Z hZ ↔ ∀ x : ↥(pullback sC sT),
      (pullback.snd sC sT).base x = t → Ψ.base x ∉ Z := by
  change t ∈ (pullback.snd sC sT '' (Ψ.base ⁻¹' Z))ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_image, Set.mem_preimage, not_exists, not_and]
  exact ⟨fun h x hx hZx => h x hZx hx, fun h x hx hxt => h x hxt hx⟩

end Avoid

section Assembly

variable [IsProper sC] {κ : Type*} (q : κ → Γ(coefficientSpace n N k, ⊤))
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- **The closed subscheme of the coefficient space** cut out by a family `q` of polynomial
equations in the coefficients. -/
abbrev closedLocus : Scheme.{u} := zeroLocusScheme (coefficientSpace n N k) q

/-- The closed immersion of `closedLocus q` into the coefficient space. -/
abbrev closedLocus.ι : closedLocus (n := n) (N := N) (k := k) q ⟶ coefficientSpace n N k :=
  zeroLocusScheme.ι (coefficientSpace n N k) q

/-- `closedLocus q` is a Noetherian topological space. -/
instance : TopologicalSpace.NoetherianSpace (closedLocus (n := n) (N := N) (k := k) q) :=
  (closedLocus.ι (n := n) (N := N) (k := k) q).isClosedEmbedding.isInducing.noetherianSpace

/-- The structure morphism of `closedLocus q`. -/
abbrev closedLocus.over : closedLocus (n := n) (N := N) (k := k) q ⟶ Spec (.of k) :=
  closedLocus.ι (n := n) (N := N) (k := k) q ≫ coefficientSpaceOver n N k

/-- **The locus of the closed subscheme without common zero**: the preimage of the open locus
of tuples without common zero. -/
def closedNoCommonZeroOpen : (closedLocus (n := n) (N := N) (k := k) q).Opens :=
  closedLocus.ι (n := n) (N := N) (k := k) q ⁻¹ᵁ noCommonZeroOpen (n := n) sC L e

/-- The scheme `M₂` of tuples without common zero satisfying the polynomial equations `q`. -/
abbrev closedNoCommonZeroScheme : Scheme.{u} :=
  (closedNoCommonZeroOpen (n := n) sC L e q).toScheme

/-- The open immersion `M₂ ⟶ closedLocus q`. -/
abbrev closedNoCommonZeroScheme.ι : closedNoCommonZeroScheme (n := n) sC L e q ⟶
    closedLocus (n := n) (N := N) (k := k) q :=
  (closedNoCommonZeroOpen (n := n) sC L e q).ι

/-- The structure morphism of `M₂`. -/
abbrev closedNoCommonZeroScheme.over : closedNoCommonZeroScheme (n := n) sC L e q ⟶
    Spec (.of k) :=
  closedNoCommonZeroScheme.ι (n := n) sC L e q ≫ closedLocus.over (n := n) (N := N) q

/-- The points of `M₂` map into the locus `M₁` of tuples without common zero. -/
theorem range_closedNoCommonZeroScheme_ι_subset :
    Set.range ((closedNoCommonZeroScheme.ι (n := n) sC L e q ≫
      closedLocus.ι (n := n) (N := N) (k := k) q).base) ⊆
      Set.range (noCommonZeroScheme.ι (n := n) sC L e).base := by
  rintro _ ⟨x, rfl⟩
  have hx : x.1 ∈ closedNoCommonZeroOpen (n := n) sC L e q := x.2
  have h : (closedLocus.ι (n := n) (N := N) (k := k) q).base x.1 ∈
      noCommonZeroOpen (n := n) sC L e := hx
  exact ⟨⟨_, h⟩, rfl⟩

omit [IsProper sC] in
/-- The morphism `C ×ₖ T' ⟶ C ×ₖ T` induced by a morphism `h : T' ⟶ T` of `k`-schemes. -/
def familyMapOfHom {T T' : Scheme.{u}} {sT : T ⟶ Spec (.of k)} {sT' : T' ⟶ Spec (.of k)}
    (h : T' ⟶ T) (hh : h ≫ sT = sT') : pullback sC sT' ⟶ pullback sC sT :=
  pullback.map sC sT' sC sT (𝟙 C) h (𝟙 _) (by simp) (by simp [hh])

omit [IsProper sC] in
/-- The first projection of `C ×ₖ T' → C ×ₖ T` is the first projection of `C ×ₖ T'`. -/
@[reassoc (attr := simp)]
theorem familyMapOfHom_fst {T T' : Scheme.{u}} {sT : T ⟶ Spec (.of k)}
    {sT' : T' ⟶ Spec (.of k)} (h : T' ⟶ T) (hh : h ≫ sT = sT') :
    familyMapOfHom sC h hh ≫ pullback.fst sC sT = pullback.fst sC sT' :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [IsProper sC] in
/-- The second projection of `C ×ₖ T' → C ×ₖ T` is the second projection of `C ×ₖ T'` followed by
`h`. -/
@[reassoc (attr := simp)]
theorem familyMapOfHom_snd {T T' : Scheme.{u}} {sT : T ⟶ Spec (.of k)}
    {sT' : T' ⟶ Spec (.of k)} (h : T' ⟶ T) (hh : h ≫ sT = sT') :
    familyMapOfHom sC h hh ≫ pullback.snd sC sT = pullback.snd sC sT' ≫ h :=
  pullback.lift_snd _ _ _

/-- The map `M₂ ⟶ M₁` of the scheme of tuples without common zero satisfying `q` to the scheme
of tuples without common zero. -/
def closedNoCommonZeroScheme.toNoCommonZero :
    closedNoCommonZeroScheme (n := n) sC L e q ⟶ noCommonZeroScheme (n := n) sC L e :=
  IsOpenImmersion.lift (noCommonZeroScheme.ι (n := n) sC L e)
    (closedNoCommonZeroScheme.ι (n := n) sC L e q ≫ closedLocus.ι (n := n) (N := N) (k := k) q)
    (range_closedNoCommonZeroScheme_ι_subset sC L e q)

/-- `M₂ ⟶ M₁` commutes with the inclusions into the coefficient space. -/
theorem closedNoCommonZeroScheme.toNoCommonZero_ι :
    closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q ≫
        noCommonZeroScheme.ι (n := n) sC L e =
      closedNoCommonZeroScheme.ι (n := n) sC L e q ≫ closedLocus.ι (n := n) (N := N) (k := k) q :=
  IsOpenImmersion.lift_fac _ _ _

/-- `M₂ ⟶ M₁` is a morphism over `k`. -/
theorem closedNoCommonZeroScheme.toNoCommonZero_over :
    closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q ≫
        noCommonZeroScheme.over (n := n) sC L e =
      closedNoCommonZeroScheme.over (n := n) sC L e q := by
  unfold noCommonZeroScheme.over closedNoCommonZeroScheme.over closedLocus.over
  rw [← Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_ι, Category.assoc]

/-- **The family `Φ : C ×ₖ M₂ → ℙⁿ_k`** over the scheme of tuples without common zero satisfying
the equations `q`: the restriction of the family over the scheme of tuples without common zero. -/
def closedNoCommonZeroFamily :
    pullback sC (closedNoCommonZeroScheme.over (n := n) sC L e q) ⟶
      projectiveSpaceOver n (Spec (.of k)) :=
  familyMapOfHom sC (closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q)
    (closedNoCommonZeroScheme.toNoCommonZero_over sC L e q) ≫ noCommonZeroFamily (n := n) sC L e

/-- **The open locus of `M₂` over which the family avoids the closed set `Zc`** (in the
application `Ū ∖ U`). -/
def finalOpen : (closedNoCommonZeroScheme (n := n) sC L e q).Opens :=
  avoidOpen sC (closedNoCommonZeroScheme.over (n := n) sC L e q)
    (closedNoCommonZeroFamily (n := n) sC L e q) Zc hZc

/-- **The coefficient space `M`** of the fixed-line curve-map lemma: the scheme of tuples of
sections of `L` with no common zero, satisfying the closed conditions `q`, whose family of maps
to `ℙⁿ_k` avoids the closed set `Zc`. -/
abbrev finalSpace : Scheme.{u} := (finalOpen (n := n) sC L e q Zc hZc).toScheme

/-- The inclusion `M ⟶ M₂`, an open immersion. -/
abbrev finalSpace.ι : finalSpace (n := n) sC L e q Zc hZc ⟶
    closedNoCommonZeroScheme (n := n) sC L e q :=
  (finalOpen (n := n) sC L e q Zc hZc).ι

/-- The structure morphism of `M`. -/
abbrev finalSpace.over : finalSpace (n := n) sC L e q Zc hZc ⟶ Spec (.of k) :=
  finalSpace.ι (n := n) sC L e q Zc hZc ≫ closedNoCommonZeroScheme.over (n := n) sC L e q

/-- **The family of maps `Φ : C ×ₖ M → ℙⁿ_k`** on `M`. -/
def finalFamily :
    pullback sC (finalSpace.over (n := n) sC L e q Zc hZc) ⟶
      projectiveSpaceOver n (Spec (.of k)) :=
  familyMapOfHom sC (finalSpace.ι (n := n) sC L e q Zc hZc) rfl ≫
    closedNoCommonZeroFamily (n := n) sC L e q

/-- `M` is locally of finite type over `k`. -/
instance : LocallyOfFiniteType (finalSpace.over (n := n) sC L e q Zc hZc) := by
  unfold finalSpace.over closedNoCommonZeroScheme.over closedLocus.over
  infer_instance

/-- `M₂` is a Noetherian topological space. -/
instance : TopologicalSpace.NoetherianSpace (closedNoCommonZeroScheme (n := n) sC L e q) :=
  TopologicalSpace.NoetherianSpace.set _

/-- `M` is a Noetherian topological space. -/
instance : TopologicalSpace.NoetherianSpace (finalSpace (n := n) sC L e q Zc hZc) :=
  TopologicalSpace.NoetherianSpace.set _

/-- `M` is quasi-compact over `k`. -/
instance : QuasiCompact (finalSpace.over (n := n) sC L e q Zc hZc) := by
  have h1 : QuasiCompact (finalSpace.ι (n := n) sC L e q Zc hZc ≫
      closedNoCommonZeroScheme.ι (n := n) sC L e q ≫
      closedLocus.ι (n := n) (N := N) (k := k) q) :=
    ⟨fun U _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have h2 : QuasiCompact (coefficientSpaceOver n N k) := inferInstance
  unfold finalSpace.over closedNoCommonZeroScheme.over closedLocus.over
  simp only [← Category.assoc] at h1 ⊢
  infer_instance

end Assembly

section KPointFinal

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

variable {sC} {T T' : Scheme.{u}} {sT : T ⟶ Spec (.of k)} {sT' : T' ⟶ Spec (.of k)}

/-- **`C ×ₖ T'` is the fibre product of `C ×ₖ T → T` with `T' → T`.** -/
theorem isPullback_familyMapOfHom (h : T' ⟶ T) (hh : h ≫ sT = sT') :
    IsPullback (familyMapOfHom sC h hh) (pullback.snd sC sT') (pullback.snd sC sT) h := by
  refine IsPullback.of_right (h₁₂ := pullback.fst sC sT) (h₂₂ := sT) ?_
    (familyMapOfHom_snd sC h hh) (IsPullback.of_hasPullback _ _)
  rw [familyMapOfHom_fst]
  subst hh
  exact IsPullback.of_hasPullback _ _

/-- A point of `C ×ₖ T` over the image of a point of `T'` comes from `C ×ₖ T'`. -/
theorem exists_preimage_familyMapOfHom (h : T' ⟶ T) (hh : h ≫ sT = sT')
    (x : ↥(pullback sC sT)) (t : T')
    (hx : (pullback.snd sC sT).base x = h.base t) :
    ∃ x' : ↥(pullback sC sT'), (familyMapOfHom sC h hh).base x' = x ∧
      (pullback.snd sC sT').base x' = t := by
  have H := isPullback_familyMapOfHom (sC := sC) h hh
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x t hx
  have e1 := H.isoPullback_hom_fst
  have e2 := H.isoPullback_hom_snd
  have hz : (H.isoPullback.hom) ((H.isoPullback.inv) z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; simp
  refine ⟨(H.isoPullback.inv) z, ?_, ?_⟩
  · have := congrArg (fun φ => φ ((H.isoPullback.inv) z)) e1
    simp only [Scheme.Hom.comp_apply, hz] at this
    rw [← this, hz1]
  · have := congrArg (fun φ => φ ((H.isoPullback.inv) z)) e2
    simp only [Scheme.Hom.comp_apply, hz] at this
    rw [← this, hz2]

/-- `familyMapOfHom` is compatible with composition of morphisms of `k`-schemes. -/
theorem familyMapOfHom_comp {T'' : Scheme.{u}} {sT'' : T'' ⟶ Spec (.of k)} (h : T' ⟶ T)
    (hh : h ≫ sT = sT') (h' : T'' ⟶ T') (hh' : h' ≫ sT' = sT'') :
    familyMapOfHom sC (h' ≫ h) (by rw [Category.assoc, hh, hh']) =
      familyMapOfHom sC h' hh' ≫ familyMapOfHom sC h hh := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

end KPointFinal

section KPointFinalExists

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

variable [IsProper sC] {κ : Type*} (q : κ → Γ(coefficientSpace n N k, ⊤))
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- The family `Φ` on `M₁`, restricted along a `k`-point `m` of `M₁`, is `familyMapOfHom`
followed by `Φ`; this is the base change of the family of `noCommonZeroFamily_base_change_eq`. -/
theorem familyMapOfHom_eq_familyBaseChange
    (m : Spec (.of k) ⟶ noCommonZeroScheme (n := n) sC L e) :
    familyMapOfHom sC m (sT := noCommonZeroScheme.over (n := n) sC L e)
        (sT' := m ≫ noCommonZeroScheme.over (n := n) sC L e) rfl =
      familyBaseChange (sC := sC) (noCommonZeroScheme.ι (n := n) sC L e) m := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

omit [IsProper sC] in
/-- The restriction of `Φ` along a `k`-point `m` of `M₁` for the point `a` of `f`: its image avoids
`Zc` if `f` does (this is `noCommonZeroFamily_base_change_eq`, for an arbitrary spelling of
the structure morphism of the point). -/
theorem familyMapOfHom_noCommonZeroFamily_not_mem [IsProper sC]
    (a : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (m : Spec (.of k) ⟶ noCommonZeroScheme (n := n) sC L e)
    (hm : m ≫ noCommonZeroScheme.ι (n := n) sC L e = coefficientPoint (n := n) (N := N) a)
    {Zc : Set (projectiveSpaceOver n (Spec (.of k)))} (hZ : ∀ x : C, f.base x ∉ Zc)
    {s : Spec (.of k) ⟶ Spec (.of k)} (hs : m ≫ noCommonZeroScheme.over (n := n) sC L e = s)
    (x : ↥(pullback sC s))
    (hx : (familyMapOfHom sC m hs ≫ noCommonZeroFamily (n := n) sC L e).base x ∈ Zc) : False := by
  subst hs
  have key := noCommonZeroFamily_base_change_eq (n := n) (N := N) (L := L) (e := e) (sC := sC)
    a f hf l hτ m hm
  rw [familyMapOfHom_eq_familyBaseChange, key] at hx
  exact hZ _ hx

/-- **`[f]` is a `k`-point of `M`.** Let `f : C ⟶ ℙⁿ_k` be a morphism over `k` with an isomorphism
`f^* 𝒪(1) ≅ L` carrying `f^* Tᵢ` to the tuple `τᵢ = Σⱼ aᵢⱼ eⱼ`. If the coefficients `a` satisfy
the closed conditions `q` and `f` avoids the closed set `Zc`, then the `k`-point `a` of the
coefficient space lifts to a `k`-point of `M`. -/
theorem exists_kPoint_finalSpace (a : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (hq : ∀ i, (coefficientPoint (n := n) (N := N) a).appTop (q i) = 0)
    (hZ : ∀ x : C, f.base x ∉ Zc) :
    ∃ m : Spec (.of k) ⟶ finalSpace (n := n) sC L e q Zc hZc,
      m ≫ finalSpace.over (n := n) sC L e q Zc hZc = 𝟙 (Spec (.of k)) ∧
      m ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫
        closedNoCommonZeroScheme.ι (n := n) sC L e q ≫
        closedLocus.ι (n := n) (N := N) (k := k) q = coefficientPoint (n := n) (N := N) a := by
  have ha := coefficientPoint_mem_noCommonZeroOpen (n := n) (N := N) (L := L) (e := e) (sC := sC)
    a f l hτ
  obtain ⟨z, hz⟩ := (exists_lift_zeroLocusScheme_ι_iff (coefficientSpace n N k) q
    (coefficientPoint (n := n) (N := N) a)).2 hq
  have hle2 : Set.range z.base ⊆
      Set.range (closedNoCommonZeroScheme.ι (n := n) sC L e q).base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (closedLocus.ι (n := n) (N := N) (k := k) q).base (z.base t) ∈
      noCommonZeroOpen (n := n) sC L e
    have := ha t
    rw [← hz] at this
    exact this
  set m₂ := IsOpenImmersion.lift (closedNoCommonZeroScheme.ι (n := n) sC L e q) z hle2 with hm₂
  have hm₂ι : m₂ ≫ closedNoCommonZeroScheme.ι (n := n) sC L e q = z :=
    IsOpenImmersion.lift_fac _ _ _
  set m := m₂ ≫ closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q with hm
  have hmι : m ≫ noCommonZeroScheme.ι (n := n) sC L e =
      coefficientPoint (n := n) (N := N) a := by
    rw [hm, Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_ι, ← Category.assoc, hm₂ι, hz]
  have hle3 : Set.range m₂.base ⊆ Set.range (finalSpace.ι (n := n) sC L e q Zc hZc).base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change m₂.base t ∈ finalOpen (n := n) sC L e q Zc hZc
    unfold finalOpen
    rw [mem_avoidOpen_iff]
    intro x hx hxZ
    obtain ⟨x', hx'1, hx'2⟩ := exists_preimage_familyMapOfHom (sC := sC) m₂ rfl x t hx
    have h1 : closedNoCommonZeroFamily (n := n) sC L e q = familyMapOfHom sC
        (closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q)
        (closedNoCommonZeroScheme.toNoCommonZero_over sC L e q) ≫
          noCommonZeroFamily (n := n) sC L e := rfl
    have hs : m ≫ noCommonZeroScheme.over (n := n) sC L e =
        m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q := by
      rw [hm, Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_over]
    have h2 : (familyMapOfHom sC m₂ (sT := closedNoCommonZeroScheme.over (n := n) sC L e q)
          (sT' := m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q) rfl ≫
        closedNoCommonZeroFamily (n := n) sC L e q) =
        familyMapOfHom sC m hs ≫ noCommonZeroFamily (n := n) sC L e :=
      (congrArg (familyMapOfHom sC m₂ (sT := closedNoCommonZeroScheme.over (n := n) sC L e q)
          (sT' := m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q) rfl ≫ ·) h1).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ noCommonZeroFamily (n := n) sC L e)
            (familyMapOfHom_comp (sC := sC)
              (closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q)
              (closedNoCommonZeroScheme.toNoCommonZero_over sC L e q) m₂ rfl).symm))
    rw [← hx'1, ← Scheme.Hom.comp_apply, h2] at hxZ
    exact familyMapOfHom_noCommonZeroFamily_not_mem sC L e a f hf l hτ m hmι
      hZ hs x' hxZ
  have hm_over : m₂ ≫ closedNoCommonZeroScheme.over (n := n) sC L e q = 𝟙 (Spec (.of k)) := by
    unfold closedNoCommonZeroScheme.over closedLocus.over
    rw [← Category.assoc, hm₂ι, ← Category.assoc, hz, coefficientPoint_over]
  refine ⟨IsOpenImmersion.lift (finalSpace.ι (n := n) sC L e q Zc hZc) m₂ hle3, ?_, ?_⟩
  · unfold finalSpace.over
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hm_over]
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, hm₂ι, hz]

end KPointFinalExists

section LinearConditions

/-- The constant function `c ∈ k` on the coefficient space. -/
def constFunction (n N : ℕ) (k : Type u) [Field k] (c : k) : Γ(coefficientSpace n N k, ⊤) :=
  (coefficientSpaceOver n N k).appTop ((Scheme.ΓSpecIso (.of k)).inv c)

/-- **A `k`-linear form in the coefficients**: the function `Σᵢⱼ μᵢⱼ xᵢⱼ` on the coefficient
space. -/
def linearFunction (n N : ℕ) (k : Type u) [Field k] (μ : Fin (n + 1) → Fin N → k) :
    Γ(coefficientSpace n N k, ⊤) :=
  ∑ i, ∑ j, constFunction n N k (μ i j) * coefficientCoord n N k i j

/-- A `k`-point of the coefficient space pulls back the constant function `c` to `c`. -/
theorem appTop_coefficientPoint_constFunction (a : Fin (n + 1) → Fin N → k) (c : k) :
    (coefficientPoint (n := n) (N := N) a).appTop (constFunction n N k c) =
      (Scheme.ΓSpecIso (.of k)).inv c := by
  unfold constFunction
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, coefficientPoint_over]
  rfl

/-- **A linear form evaluated at a `k`-point** of the coefficient space. -/
theorem appTop_coefficientPoint_linearFunction (a : Fin (n + 1) → Fin N → k)
    (μ : Fin (n + 1) → Fin N → k) :
    (coefficientPoint (n := n) (N := N) a).appTop (linearFunction n N k μ) =
      (Scheme.ΓSpecIso (.of k)).inv (∑ i, ∑ j, μ i j * a i j) := by
  unfold linearFunction
  simp only [map_sum, map_mul, appTop_coefficientPoint_constFunction,
    coefficientPoint_appTop_coord]

/-- A linear form vanishes at a `k`-point of the coefficient space iff the linear form of
scalars does. -/
theorem appTop_coefficientPoint_linearFunction_eq_zero_iff (a : Fin (n + 1) → Fin N → k)
    (μ : Fin (n + 1) → Fin N → k) :
    (coefficientPoint (n := n) (N := N) a).appTop (linearFunction n N k μ) = 0 ↔
      ∑ i, ∑ j, μ i j * a i j = 0 := by
  rw [appTop_coefficientPoint_linearFunction]
  constructor
  · intro h
    exact (Scheme.ΓSpecIso (.of k)).inv.hom.injective (h.trans (map_zero _).symm)
  · intro h; rw [h, map_zero]

/-- The coefficient vector of the **proportionality condition at a marked point**: if `ℓ ∈ kᴺ`
are the values of the basis `e` at the point `P` (in a trivialization of the fibre `L|_P`) and
`c ∈ kⁿ⁺¹` is the specified nonzero value `f(P)`, the condition that the tuple at `P` is
proportional to `c`, in the form `(Σⱼ ℓⱼ x_{iⱼ}) c_{i'} = (Σⱼ ℓⱼ x_{i'ⱼ}) c_i`. -/
def proportionalityVector (ℓ : Fin N → k) (c : Fin (n + 1) → k) (i i' : Fin (n + 1)) :
    Fin (n + 1) → Fin N → k :=
  fun r j => ℓ j * ((if r = i then c i' else 0) - (if r = i' then c i else 0))

/-- The **proportionality conditions at a marked point**: all the linear forms
`proportionalityVector`. -/
def proportionalityFunction (n N : ℕ) (k : Type u) [Field k] (ℓ : Fin N → k)
    (c : Fin (n + 1) → k) (i i' : Fin (n + 1)) : Γ(coefficientSpace n N k, ⊤) :=
  linearFunction n N k (proportionalityVector ℓ c i i')

/-- The **normalization**: the linear form `μ` equals one. -/
def normalizationFunction (n N : ℕ) (k : Type u) [Field k] (μ : Fin (n + 1) → Fin N → k) :
    Γ(coefficientSpace n N k, ⊤) :=
  linearFunction n N k μ - constFunction n N k 1

/-- The proportionality condition at a `k`-point: `(Σⱼ ℓⱼ a_{iⱼ}) c_{i'} = (Σⱼ ℓⱼ a_{i'ⱼ}) c_i`. -/
theorem appTop_coefficientPoint_proportionalityFunction_eq_zero_iff
    (a : Fin (n + 1) → Fin N → k) (ℓ : Fin N → k) (c : Fin (n + 1) → k) (i i' : Fin (n + 1)) :
    (coefficientPoint (n := n) (N := N) a).appTop (proportionalityFunction n N k ℓ c i i') = 0 ↔
      (∑ j, ℓ j * a i j) * c i' = (∑ j, ℓ j * a i' j) * c i := by
  unfold proportionalityFunction
  rw [appTop_coefficientPoint_linearFunction_eq_zero_iff]
  have : ∑ r, ∑ j, proportionalityVector ℓ c i i' r j * a r j =
      (∑ j, ℓ j * a i j) * c i' - (∑ j, ℓ j * a i' j) * c i := by
    have h1 : ∀ (b : Fin (n + 1)) (x : k),
        ∑ r, ∑ j, (ℓ j * (if r = b then x else 0)) * a r j = (∑ j, ℓ j * a b j) * x := by
      intro b x
      rw [Finset.sum_eq_single b]
      · simp [Finset.sum_mul, mul_comm, mul_left_comm]
        exact (Finset.mul_sum _ _ _).symm
      · intro r _ hr; simp [hr]
      · simp
    simp only [proportionalityVector, mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [h1 i (c i'), h1 i' (c i)]
  rw [this, sub_eq_zero]

/-- The normalization at a `k`-point: the linear form takes the value one. -/
theorem appTop_coefficientPoint_normalizationFunction_eq_zero_iff (a : Fin (n + 1) → Fin N → k)
    (μ : Fin (n + 1) → Fin N → k) :
    (coefficientPoint (n := n) (N := N) a).appTop (normalizationFunction n N k μ) = 0 ↔
      ∑ i, ∑ j, μ i j * a i j = 1 := by
  unfold normalizationFunction
  rw [map_sub, appTop_coefficientPoint_linearFunction, appTop_coefficientPoint_constFunction,
    sub_eq_zero]
  exact ⟨fun h => (Scheme.ΓSpecIso (.of k)).inv.hom.injective h, fun h => by rw [h]⟩

end LinearConditions

section CurveMapConditions

open Stacks.Algebraization Stacks.AlgebraicGeometry.SectionsBaseChange

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable [IsProper sC]

/-- **The coefficients of the substituted equation** `F(σ) ∈ H⁰(C ×ₖ 𝔸, pr_C^* L^{⊗d})` against
a `k`-basis `w'` of `H⁰(C, L^{⊗d})`: finitely many functions on the coefficient space whose
simultaneous vanishing at a point says `F(σ) = 0` there. -/
def equationFunctions (d : ℕ) {N' : ℕ}
    (w' : letI := baseModule sC (Stacks.TensorPowers.natTensorPow L d) ⊤;
      Module.Basis (Fin N') Γ(Spec (.of k), ⊤) Γ(Stacks.TensorPowers.natTensorPow L d, ⊤))
    (F : MvPolynomial (Fin (n + 1)) k) : Fin N' → Γ(coefficientSpace n N k, ⊤) :=
  coefficientFunctions (n := n) (N := N) sC w' (substitutedUniversalSection (n := n) sC L e d F)

/-- **The closed conditions of the fixed-line curve-map space `M`**, as a family of functions on
the coefficient space `𝔸(H⁰(C, L)^{n+1})`:
* the coefficients of the substituted equations `F_α(σ) ∈ H⁰(C, L^{⊗ d_α})` of `Ū`
  (`equationFunctions`, one family of coefficients for each form `F_α` against a basis of
  `H⁰(C, L^{⊗ d_α})`);
* the proportionality of the tuple at each marked point `P_β` to the specified nonzero vector
  `c_β` (`proportionalityFunction`, with `ℓ_β` the values of the basis `e` at `P_β`);
* the normalization `μ(σ) = 1` of one coefficient functional `μ`. -/
def curveMapConditions {ιE : Type} (F : ιE → MvPolynomial (Fin (n + 1)) k) (d : ιE → ℕ)
    {N' : ιE → ℕ}
    (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow L (d α)) ⊤;
      Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
        Γ(Stacks.TensorPowers.natTensorPow L (d α), ⊤))
    {ιB : Type} (ℓ : ιB → Fin N → k) (c : ιB → Fin (n + 1) → k)
    (μ : Fin (n + 1) → Fin N → k) :
    ((Σ α, Fin (N' α)) ⊕ (ιB × Fin (n + 1) × Fin (n + 1)) ⊕ Unit) →
      Γ(coefficientSpace n N k, ⊤)
  | Sum.inl ⟨α, j⟩ => equationFunctions (n := n) sC L e (d α) (w' α) (F α) j
  | Sum.inr (Sum.inl ⟨β, i, i'⟩) => proportionalityFunction n N k (ℓ β) (c β) i i'
  | Sum.inr (Sum.inr ()) => normalizationFunction n N k μ

end CurveMapConditions

section CurveMapSpace

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open Stacks.AlgebraicGeometry.SectionsBaseChange

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable [IsProper sC] {ιE : Type} (F : ιE → MvPolynomial (Fin (n + 1)) k) (d : ιE → ℕ)
  {N' : ιE → ℕ}
  (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow L (d α)) ⊤;
    Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
      Γ(Stacks.TensorPowers.natTensorPow L (d α), ⊤))
  {ιB : Type} (ℓ : ιB → Fin N → k) (c : ιB → Fin (n + 1) → k) (μ : Fin (n + 1) → Fin N → k)
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- **The coefficient space `M` of the fixed-line curve-map lemma.** The scheme of tuples
`σ ∈ H⁰(C, L)^{n+1}` without common zero (open), whose substituted equations `F_α(σ) ∈
H⁰(C, L^{⊗ d_α})` of `Ū` vanish (closed), proportional at each marked point to the specified
nonzero value (linear), normalized by one coefficient functional equal to one (linear), and whose
family of maps `C → ℙⁿ` avoids the closed set `Zc` (open; in the application `Ū ∖ U`). It is a
subscheme of the coefficient space `𝔸(H⁰(C, L)^{n+1})`, locally of finite type and quasicompact
over `k`. -/
abbrev curveMapSpace : Scheme.{u} :=
  finalSpace (n := n) sC L e
    (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc

/-- **`[f]` is a `k`-point of `M`.** Let `f : C ⟶ ℙⁿ_k` be a morphism over `k` and
`f^* 𝒪(1) ≅ L` an isomorphism carrying `f^* Tᵢ` to the tuple `τᵢ = Σⱼ aᵢⱼ eⱼ`. If `a` satisfies
the conditions defining `M` (the substituted equations of `Ū` vanish at `a`, the tuple at each
marked point is proportional to `c_β`, the normalizing functional takes the value one) and `f`
avoids `Zc`, then `a` lifts to a `k`-point of `M`, lying over `a` in the coefficient space. -/
theorem exists_kPoint_curveMapSpace (a : Fin (n + 1) → Fin N → k)
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l]
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (hF : ∀ α j, (coefficientPoint (n := n) (N := N) a).appTop
      (equationFunctions (n := n) sC L e (d α) (w' α) (F α) j) = 0)
    (hprop : ∀ β i i', (∑ j, ℓ β j * a i j) * c β i' = (∑ j, ℓ β j * a i' j) * c β i)
    (hnorm : ∑ i, ∑ j, μ i j * a i j = 1)
    (hZ : ∀ x : C, f.base x ∉ Zc) :
    ∃ m : Spec (.of k) ⟶ curveMapSpace (n := n) sC L e F d w' ℓ c μ Zc hZc,
      m ≫ finalSpace.over (n := n) sC L e
        (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc = 𝟙 (Spec (.of k)) ∧
      m ≫ finalSpace.ι (n := n) sC L e
          (curveMapConditions (n := n) sC L e F d w' ℓ c μ) Zc hZc ≫
        closedNoCommonZeroScheme.ι (n := n) sC L e
          (curveMapConditions (n := n) sC L e F d w' ℓ c μ) ≫
        closedLocus.ι (n := n) (N := N) (k := k)
          (curveMapConditions (n := n) sC L e F d w' ℓ c μ) =
        coefficientPoint (n := n) (N := N) a := by
  refine exists_kPoint_finalSpace (n := n) sC L e _ Zc hZc a f hf l hτ ?_ hZ
  rintro (⟨α, j⟩ | ⟨β, i, i'⟩ | ⟨⟩)
  · exact hF α j
  · exact (appTop_coefficientPoint_proportionalityFunction_eq_zero_iff a (ℓ β) (c β) i i').2
      (hprop β i i')
  · exact (appTop_coefficientPoint_normalizationFunction_eq_zero_iff a μ).2 hnorm

end CurveMapSpace

end MMP.Fourfold

end
