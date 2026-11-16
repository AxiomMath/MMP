module

public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion

/-!
# Finitely many finite-type families of effective Cartier divisors with a fixed Hilbert polynomial

Let `k` be an algebraically closed field, `S` a projective `k`-scheme, `H` a very ample invertible
sheaf on `S` and `P ∈ ℚ[X]` a polynomial that takes integer values on the integers. There are
finitely many finite-type `k`-schemes `Tᵢ`, each with finitely many irreducible components, and
effective Cartier divisors `𝒟ᵢ ⊆ S ×_k Tᵢ`, flat over `Tᵢ`, whose fibre `𝒟ᵢ,ₜ ⊆ S_{κ(t)}` over
every point `t ∈ Tᵢ` has Hilbert polynomial `n ↦ χ(𝒟ᵢ,ₜ, H^{⊗ n}|_{𝒟ᵢ,ₜ}) = P(n)`, such that every
effective Cartier divisor `D ⊆ S` with `χ(D, H^{⊗ n}|_D) = P(n)` for all `n ∈ ℤ` is the fibre of
some `𝒟ᵢ` over a `k`-point of `Tᵢ`. The parameter schemes are not asserted to be projective.

For the proof, embed `S` by `H` as a closed subscheme `ι : S ↪ ℙᴺ_k` with `H ≅ ι^* 𝒪(1)`.
A closed subscheme `Z ⊆ S` with Hilbert function `P` pushes forward to a
quotient of `𝒪_{ℙᴺ_k}` with Hilbert polynomial `P`, a `k`-point of the scheme `Quot^P` of
quotients of `𝒪` on `ℙᴺ` (Stacks, Tag 0DPA). The universal quotient cuts out a closed
subscheme of `ℙᴺ_{Quot^P}`; its intersection with `S ×_k Quot^P`, flattened over the base
(Stacks, Tag 05UH), is a closed subscheme `D ⊆ S ×_k T` flat over a finite-type `k`-scheme `T`
whose fibres over `k`-points include every such `Z`.

Two open conditions cut `T` down to the single family of the statement: the locus where the
fibre Hilbert function is `P`, open because Hilbert functions of flat families on `ℙᴺ` are
locally constant (Stacks, Tag 0B9T), and the complement of the image of the locus of
`S ×_k T` near which `D` is not an effective Cartier divisor, open because `S ×_k T ⟶ T` is
proper. A fibre over a `k`-point that is an effective Cartier divisor lies in the second
locus by the fibrewise criterion for relative effective Cartier divisors (Stacks, Tag 062Y).

## Main results

* `MMP.exists_finite_isEffectiveCartierDivisor_families`: the finitely many families.

## Implementation notes

* The base is an arbitrary algebraically closed field `k` rather than `ℂ`; complex points become
  `k`-points, i.e. sections `t` of the structure morphism `Tᵢ ⟶ Spec k`.
* A closed subscheme is a `Scheme.IdealSheafData`, and an effective Cartier divisor one whose ideal
  sheaf is invertible (`Stacks.Divisors.IsEffectiveCartierDivisor`). The product `S ×_k Tᵢ` is
  `pullback (S ↘ Spec k) pᵢ`, and flatness of `𝒟ᵢ` over `Tᵢ` is flatness of
  `𝒟ᵢ ⟶ S ×_k Tᵢ ⟶ Tᵢ`.
* The fibre of `𝒟ᵢ` over a point `t` is `Scheme.IdealSheafData.comap` along
  `S ×_k Spec κ(t) ⟶ S ×_k Tᵢ`, and over a `k`-point `t` it is the `comap` along
  `pullback.lift (𝟙 S) (S ↘ Spec k ≫ t)`. Hilbert polynomials are
  `MMP.Mori.subschemeHilbertFunction`.
* The universal line bundle `𝒪(𝒟ᵢ)` is the inverse of the ideal sheaf of `𝒟ᵢ`. Its restriction to
  the fibre over a `k`-point `t` is `𝒪_S(𝒟ᵢ,ₜ)`, since the pullback of an invertible ideal sheaf
  surjects onto the ideal of `comap`, which is invertible here; so equality of the fibre with `D`
  pins `𝒪(𝒟ᵢ)|_{S × {t}} ≅ 𝒪_S(D)`.
* Projectivity is H-projectivity, `AlgebraicGeometry.IsProjectiveMorphism` (Stacks, Tag 01W8);
  it gives properness through `AlgebraicGeometry.isProper_of_isProjectiveMorphism`, which the Euler
  characteristics need.

## References

* [A. Grothendieck, *Techniques de construction et théorèmes d'existence en géométrie
  algébrique IV: les schémas de Hilbert*]
* [Stacks Project, Tag 01W8, Tag 01WS, Tag 0DPA, Tag 05UH, Tag 0B9T, Tag 062Y]
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace MMP

universe u

section

variable {S : Scheme.{u}}

/-- The section `S ⟶ S ×_k T` over a `k`-point `t` of `T`. -/
private noncomputable abbrev fibreSection (k : Type u) [Field k] [S.Over (Spec (.of k))]
    {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) (t : Spec (.of k) ⟶ T) (ht : t ≫ p = 𝟙 _) :
    S ⟶ pullback (S ↘ Spec (.of k)) p :=
  pullback.lift (𝟙 S) (S ↘ Spec (.of k) ≫ t)
    (by rw [Category.assoc, ht, Category.comp_id, Category.id_comp])

/-- The morphism `S ×_k T ⟶ ℙᴺ_T` induced by `ι : S ⟶ ℙᴺ_k`. -/
private noncomputable def familyEmbedding (k : Type u) [Field k] [S.Over (Spec (.of k))] {N : ℕ}
    (ι : S ⟶ projectiveSpaceOver N (Spec (.of k))) {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) :
    pullback (S ↘ Spec (.of k)) p ⟶ projectiveSpaceOver N T :=
  pullback.lift (pullback.snd _ _)
    (pullback.fst _ _ ≫ ι ≫ projectiveSpaceOver.toIntegralAtUniverse N _)
    (terminal.hom_ext _ _)

private theorem familyEmbedding_fst (k : Type u) [Field k] [S.Over (Spec (.of k))] {N : ℕ}
    (ι : S ⟶ projectiveSpaceOver N (Spec (.of k))) {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) :
    familyEmbedding k ι p ≫ pullback.fst _ _ = pullback.snd (S ↘ Spec (.of k)) p :=
  pullback.lift_fst _ _ _

/-- `S ×_k T` is the base change of `S ⟶ ℙᴺ_k` along `ℙᴺ_T ⟶ ℙᴺ_k`. -/
private theorem isPullback_familyEmbedding (k : Type u) [Field k] [S.Over (Spec (.of k))]
    {N : ℕ} (ι : S ⟶ projectiveSpaceOver N (Spec (.of k)))
    (hι : ι ≫ pullback.fst _ _ = S ↘ Spec (.of k)) {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) :
    IsPullback (pullback.fst (S ↘ Spec (.of k)) p) (familyEmbedding k ι p) ι
      (projectiveSpaceOverMap N p) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_projectiveSpaceOverMap N p)
  · rw [familyEmbedding_fst, hι]
    exact IsPullback.of_hasPullback _ _
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, projectiveSpaceOverMap, pullback.lift_fst,
        familyEmbedding, pullback.lift_fst_assoc, hι, pullback.condition]
    · rw [Category.assoc, Category.assoc, projectiveSpaceOverMap, pullback.lift_snd,
        Category.comp_id, familyEmbedding, pullback.lift_snd]

private theorem isClosedImmersion_familyEmbedding (k : Type u) [Field k] [S.Over (Spec (.of k))]
    {N : ℕ} (ι : S ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion ι]
    (hι : ι ≫ pullback.fst _ _ = S ↘ Spec (.of k))
    {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) : IsClosedImmersion (familyEmbedding k ι p) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_familyEmbedding k ι hι p) ‹_›

/-! ### The embedding given by `H` -/

/-- A very ample `H` embeds `S` into `ℙᴺ_k` with `H ≅ ι^* 𝒪(1)`. -/
private theorem exists_embedding (k : Type u) [Field k] [S.Over (Spec (.of k))] (H : S.Modules)
    (hH : Intersection.IsVeryAmple k H) :
    ∃ (N : ℕ) (ι : S ⟶ projectiveSpaceOver N (Spec (.of k))), IsClosedImmersion ι ∧
      ι ≫ pullback.fst _ _ = S ↘ Spec (.of k) ∧
      Nonempty (H ≅ (Scheme.Modules.pullback ι).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k)))) := by
  obtain ⟨N, ι₀, hι₀, hι₀k, ⟨e⟩⟩ := hH
  haveI : IsClosedImmersion ι₀ := hι₀
  refine ⟨N, ι₀ ≫ (Intersection.ProjSpace.isoProjectiveSpaceOver k N).hom, inferInstance, ?_,
    ⟨?_⟩⟩
  · rw [Category.assoc, Intersection.ProjSpace.isoProjectiveSpaceOver_hom_fst, hι₀k]
  · exact e ≪≫ (Scheme.Modules.pullback ι₀).mapIso
      (Intersection.ProjSpace.twistOneIsoPullback k N).symm ≪≫
      (Scheme.Modules.pullbackComp ι₀ (Intersection.ProjSpace.isoProjectiveSpaceOver k N).hom).app _

/-! ### Hilbert functions -/

/-- The Euler characteristic depends only on the morphism and the isomorphism class. -/
private theorem eulerCharacteristic_congr (K : Type u) [Field K] {X : Scheme.{u}}
    {f f' : X ⟶ Spec (.of K)} (h : f = f') (hf : IsProper f) (hf' : IsProper f') {F G : X.Modules}
    (hF : F.IsCoherent) (hG : G.IsCoherent) (e : F ≅ G) :
    @eulerCharacteristic K _ X f hf F hF = @eulerCharacteristic K _ X f' hf' G hG := by
  subst h
  exact eulerCharacteristic_eq_of_iso K f e

/-- **The Hilbert function of `𝒪(1)|_D` is the subscheme Hilbert function.** For a closed
subscheme `i : D ⟶ Y` of a proper `K`-scheme embedded by `e` into `ℙᴺ_K` with `L ≅ e^* 𝒪(1)`,
`χ(D, (i ≫ e)^* 𝒪(1)^{⊗ d})` is `χ(D, i^* L^{⊗ d})`. -/
private theorem eulerCharacteristic_tensorPowerModules_eq_subschemeHilbertFunction (K : Type u)
    [Field K] {Y D : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [IsProper g] {N : ℕ}
    (e : Y ⟶ projectiveSpaceOver N (Spec (.of K)))
    (he : e ≫ (projectiveSpaceOver N (Spec (.of K)) ↘ Spec (.of K)) = g)
    (i : D ⟶ Y) [IsClosedImmersion i] (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (eL : L ≅ (Scheme.Modules.pullback e).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K))))
    (d : ℤ)
    (hproper : IsProper (((i ≫ e) ≫ (projectiveSpaceOver N (Spec (.of K)) ↘ Spec (.of K))) ≫
      (Iso.refl (Spec (.of K))).hom))
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible D.toRingedSpace.presheaf
      (structureSheafRing D.toRingedSpace).property ((Scheme.Modules.pullback (i ≫ e)).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K)))))
    (hcoh : (@Scheme.Modules.tensorPowerModules D ((Scheme.Modules.pullback (i ≫ e)).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K)))) hinv
        d).IsCoherent) :
    @eulerCharacteristic K _ D (((i ≫ e) ≫ (projectiveSpaceOver N (Spec (.of K)) ↘ Spec (.of K))) ≫
      (Iso.refl (Spec (.of K))).hom) hproper
      (@Scheme.Modules.tensorPowerModules D _ hinv d) hcoh =
      Mori.subschemeHilbertFunction K g i L d := by
  haveI : Stacks.Ample.IsInvertibleModule D ((Scheme.Modules.pullback (i ≫ e)).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K)))) := hinv
  let E1 : (Scheme.Modules.pullback (i ≫ e)).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of K))) ≅
      (Scheme.Modules.pullback i).obj L :=
    ((Scheme.Modules.pullbackComp i e).app _).symm ≪≫ (Scheme.Modules.pullback i).mapIso eL.symm
  unfold Mori.subschemeHilbertFunction
  refine eulerCharacteristic_congr K ?_ _ _ _ _ ?_
  · rw [Iso.refl_hom, Category.comp_id, Category.assoc, he]
  · refine Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso D _ d ≪≫
      Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorPowModuleIsoOfIsoInt D _ _ E1 d ≪≫
      (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso D _ d).symm ≪≫
      (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor _ _ _).symm

/-! ### Modules over a field are flat -/

/-- The local ring of `Spec k` at its point is a field. -/
private theorem isField_stalk_spec (k : Type u) [Field k] (x : Spec (.of k)) :
    IsField ((Spec (.of k)).presheaf.stalk x) := by
  refine isField_stalk_of_closure_mem_irreducibleComponents _ _ ?_
  have : closure ({x} : Set (Spec (.of k))) = Set.univ := by
    have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    exact Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ subset_closure rfl
  rw [this, irreducibleComponents_eq_singleton]
  rfl

private theorem flat_of_isField {R M : Type u} [CommRing R] [AddCommGroup M] (_ : Module R M)
    (h : IsField R) : Module.Flat R M := by
  letI := h.toField
  exact Module.Flat.of_free

/-- Every module on a scheme over `Spec k` is flat over `Spec k`. -/
private theorem isFlatOver_spec_field (k : Type u) [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) (F : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) :
    IsFlatOver g.toLRSHom.toShHom F := fun _ =>
  flat_of_isField _ (isField_stalk_spec k _)

/-! ### The `k`-point of `Quot^P` attached to a closed subscheme of `S` -/

open ProjectiveQuot in
/-- **A closed subscheme of `S` with Hilbert function `P` is a `k`-point of `Quot^P`.** Its
structure sheaf, pushed forward to `ℙᴺ_k` along `ι`, is the quotient of `𝒪` by
`familyOfClosedImmersion`, and its fibre Hilbert function is the subscheme Hilbert function. -/
private theorem familyOfClosedImmersion_mem_hilbertFamilies (k : Type u) [Field k]
    [S.Over (Spec (.of k))] [IsProper (S ↘ Spec (.of k))] {N : ℕ}
    (ι : S ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion ι]
    (hι : ι ≫ pullback.fst _ _ = S ↘ Spec (.of k)) (H : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    (eH : H ≅ (Scheme.Modules.pullback ι).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k))))
    (Z : S.IdealSheafData) (P : Polynomial ℚ)
    (hZ : ∀ n : ℤ, P.eval (n : ℚ) =
      Mori.subschemeHilbertFunction k (S ↘ Spec (.of k)) Z.subschemeι H n) :
    familyOfClosedImmersion (Z.subschemeι ≫ ι) ∈ hilbertFamilies N 1 P (Spec (.of k)) := by
  let i := Z.subschemeι ≫ ι
  have hπ : IsProper (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) :=
    isProper_projectiveSpaceOver N _
  have hln : IsLocallyNoetherian (projectiveSpaceOver N (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) ≫ (Iso.refl _).hom)
  have hlnZ : IsLocallyNoetherian Z.subscheme := isLocallyNoetherian_of_isClosedImmersion i
  have hcohZ : (Stacks.Ample.unitModule Z.subscheme).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit Z.subscheme
  have hcohF : ((Scheme.Modules.pushforward i).obj
      (Stacks.Ample.unitModule Z.subscheme)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i _
  have hfpF : ((Scheme.Modules.pushforward i).obj
      (Stacks.Ample.unitModule Z.subscheme)).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  refine ⟨ProjectiveQuotOverSpace.isFlatFamily_of_iso
      (quotientFamilyOfClosedImmersionIso i).symm
      ⟨hfpF, isFlatOver_spec_field k _ _⟩, ?_⟩
  have hfpQ : (quotient (familyOfClosedImmersion i)).IsFinitePresentation :=
    SheafOfModules.IsFinitePresentation.of_iso hfpF (quotientFamilyOfClosedImmersionIso i).symm
  have hpZ : IsProper (((i ≫ (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k))) ≫
      (Iso.refl (Spec (.of k))).hom)) := inferInstance
  have hinvL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.subscheme.toRingedSpace.presheaf
      (structureSheafRing Z.subscheme.toRingedSpace).property ((Scheme.Modules.pullback i).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k)))) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback i.toLRSHom.toShHom _
  have hcohL : ∀ d : ℤ, (@Scheme.Modules.tensorPowerModules Z.subscheme _ hinvL d).IsCoherent :=
    fun d => Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z.subscheme _
  rw [hasFibreHilbertPolynomial_iff]
  intro t d
  rw [fibreHilbert_eq_of_iso (quotientFamilyOfClosedImmersionIso i) t,
    fibreHilbert_pushforward_unitModule k (Iso.refl _) i hfpF t d hpZ hinvL (hcohL d),
    eulerCharacteristic_tensorPowerModules_eq_subschemeHilbertFunction k (S ↘ Spec (.of k)) ι hι
      Z.subschemeι H eH d hpZ hinvL (hcohL d)]
  exact (hZ d).symm

/-! ### The fibre Hilbert function of a family -/

open ProjectiveQuot in
/-- **The fibre Hilbert function of a family of closed subschemes of `S`.** For a closed
subscheme `D` of `S ×_k T` and a point `t` of `T`, the fibre Hilbert function at `t` of `D`,
pushed forward to `ℙᴺ_T`, is the subscheme Hilbert function of the fibre of `D` over `κ(t)`
with respect to the pullback of `H`. -/
private theorem fibreHilbert_eq_subschemeHilbertFunction (k : Type u) [Field k]
    [S.Over (Spec (.of k))] [IsProper (S ↘ Spec (.of k))] {N : ℕ}
    (ι : S ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion ι]
    (hι : ι ≫ pullback.fst _ _ = S ↘ Spec (.of k)) (H : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    (eH : H ≅ (Scheme.Modules.pullback ι).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k))))
    {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) (D : (pullback (S ↘ Spec (.of k)) p).IdealSheafData)
    [((Scheme.Modules.pushforward (D.subschemeι ≫ familyEmbedding k ι p)).obj
      (Stacks.Ample.unitModule D.subscheme)).IsFinitePresentation]
    (t : T) (d : ℤ) :
    fibreHilbert ((Scheme.Modules.pushforward (D.subschemeι ≫ familyEmbedding k ι p)).obj
      (Stacks.Ample.unitModule D.subscheme)) t d =
      Mori.subschemeHilbertFunction (T.residueField t)
        (pullback.snd (pullback.snd (S ↘ Spec (.of k)) p) (T.fromSpecResidueField t))
        (D.comap (pullback.fst (pullback.snd (S ↘ Spec (.of k)) p)
          (T.fromSpecResidueField t))).subschemeι
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd (S ↘ Spec (.of k)) p)
          (T.fromSpecResidueField t) ≫ pullback.fst (S ↘ Spec (.of k)) p)).obj H) d := by
  haveI := isClosedImmersion_familyEmbedding k ι hι p
  set g := T.fromSpecResidueField t
  set a := pullback.fst (pullback.snd (S ↘ Spec (.of k)) p) g with ha
  set j := familyEmbedding k ι p with hj
  let e : pullback (pullback.snd (S ↘ Spec (.of k)) p) g ⟶
      projectiveSpaceOver N (Spec (T.residueField t)) :=
    pullback.lift (pullback.snd _ _) (a ≫ j ≫ pullback.snd _ _) (terminal.hom_ext _ _)
  have he_fst : e ≫ pullback.fst _ _ = pullback.snd _ _ := pullback.lift_fst _ _ _
  have he_snd : e ≫ pullback.snd _ _ = a ≫ j ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  have hsqX : IsPullback a e j (projectiveSpaceOverMap N g) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_projectiveSpaceOverMap N g)
    · rw [he_fst, hj, familyEmbedding_fst]; exact IsPullback.of_hasPullback _ _
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, projectiveSpaceOverMap, pullback.lift_fst,
          ← Category.assoc e, he_fst, hj, familyEmbedding_fst, ha, pullback.condition]
      · rw [Category.assoc, Category.assoc, projectiveSpaceOverMap, pullback.lift_snd,
          Category.comp_id, he_snd]
  have hsqD := (Stacks.Bertini.isPullback_subschemeι_comap D a).flip.paste_vert hsqX
  haveI : IsClosedImmersion ((D.comap a).subschemeι ≫ e) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsqD inferInstance
  let eF := Stacks.Chow.pullbackPushforwardStructureSheafIso hsqD
  haveI hF' : ((Scheme.Modules.pushforward ((D.comap a).subschemeι ≫ e)).obj
      (Stacks.Ample.unitModule (D.comap a).subscheme)).IsFinitePresentation :=
    SheafOfModules.IsFinitePresentation.of_iso inferInstance eF
  obtain ⟨pt⟩ : Nonempty (Spec (.of (T.residueField t))) := inferInstance
  have hgpt : g pt = t := Scheme.fromSpecResidueField_apply t pt
  have h1 := fibreHilbert_pullback g ((Scheme.Modules.pushforward (D.subschemeι ≫ j)).obj
      (Stacks.Ample.unitModule D.subscheme)) pt
  rw [hgpt] at h1
  have hπ : IsProper (projectiveSpaceOver N (Spec (.of (T.residueField t))) ↘
      Spec (.of (T.residueField t))) := isProper_projectiveSpaceOver N _
  have hln : IsLocallyNoetherian (projectiveSpaceOver N (Spec (.of (T.residueField t)))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((projectiveSpaceOver N (Spec (.of (T.residueField t))) ↘ Spec (.of (T.residueField t))) ≫
        (Iso.refl _).hom)
  have hlnZ : IsLocallyNoetherian (D.comap a).subscheme :=
    isLocallyNoetherian_of_isClosedImmersion ((D.comap a).subschemeι ≫ e)
  have hpZ : IsProper (((((D.comap a).subschemeι ≫ e) ≫
      (projectiveSpaceOver N (Spec (.of (T.residueField t))) ↘ Spec (.of (T.residueField t)))) ≫
      (Iso.refl (Spec (.of (T.residueField t)))).hom)) := inferInstance
  have hinvL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (D.comap a).subscheme.toRingedSpace.presheaf
      (structureSheafRing (D.comap a).subscheme.toRingedSpace).property
      ((Scheme.Modules.pullback ((D.comap a).subschemeι ≫ e)).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N
          (Spec (.of (T.residueField t))))) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
      ((D.comap a).subschemeι ≫ e).toLRSHom.toShHom _
  have hcohL : (@Scheme.Modules.tensorPowerModules (D.comap a).subscheme _ hinvL d).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible (D.comap a).subscheme _
  have hcomp : ((a ≫ pullback.fst (S ↘ Spec (.of k)) p) ≫ ι) ≫
      projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of k)) =
      e ≫ projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of (T.residueField t))) := by
    change _ = e ≫ pullback.snd (terminal.from (Spec (T.residueField t)))
      (terminal.from (projectiveSpaceAtUniverse N))
    rw [he_snd, hj, familyEmbedding, pullback.lift_snd]
    simp only [Category.assoc]
  let eL : (Scheme.Modules.pullback (a ≫ pullback.fst (S ↘ Spec (.of k)) p)).obj H ≅
      (Scheme.Modules.pullback e).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N
        (Spec (.of (T.residueField t)))) :=
    (Scheme.Modules.pullback (a ≫ pullback.fst (S ↘ Spec (.of k)) p)).mapIso eH ≪≫
      (Scheme.Modules.pullbackComp _ ι).app _ ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hcomp).app _ ≪≫
      ((Scheme.Modules.pullbackComp e _).app _).symm
  rw [← h1, fibreHilbert_eq_of_iso eF pt,
    fibreHilbert_pushforward_unitModule (T.residueField t) (Iso.refl _) _ hF' pt d hpZ hinvL hcohL,
    eulerCharacteristic_tensorPowerModules_eq_subschemeHilbertFunction (T.residueField t)
      (pullback.snd (pullback.snd (S ↘ Spec (.of k)) p) g) e he_fst
      (D.comap a).subschemeι _ eL d hpZ hinvL hcohL]

/-! ### `Quot^P` and the closed subscheme of a `k`-point -/

open ProjectiveQuot in
/-- **The scheme `Quot^P` over `k`** (Stacks 0DPA): a finite-type `k`-scheme `T₀` with a member
`U₀` of `Quot^P_{𝒪/ℙᴺ}(T₀)` of which every member over `Spec k` is the base change along a
`k`-point. -/
private theorem exists_quot (k : Type u) [Field k] (N : ℕ) (P : Polynomial ℚ) :
    ∃ (T₀ : Scheme.{u}) (p₀ : T₀ ⟶ Spec (.of k)) (_ : QuasiCompact p₀)
      (_ : LocallyOfFiniteType p₀) (U₀ : Subobject (freeModule N 1 T₀)),
      U₀ ∈ hilbertFamilies N 1 P T₀ ∧
      ∀ K ∈ hilbertFamilies N 1 P (Spec (.of k)),
        ∃ t : Spec (.of k) ⟶ T₀, t ≫ p₀ = 𝟙 _ ∧ baseChange t U₀ = K := by
  obtain ⟨Z, hZ, ⟨E⟩⟩ := exists_isProper_iso_hilbertFunctor.{u} N 1 le_rfl P
  let T := pullback (terminal.from Z) (terminal.from (Spec (.of k)))
  let U := E.inv.app (Opposite.op T) (ULift.up (pullback.fst _ _) : ULift.{u + 1} (T ⟶ Z))
  haveI := hZ
  refine ⟨T, pullback.snd _ _, inferInstance, inferInstance, U.1, U.2, fun K hK => ?_⟩
  let zK : Spec (.of k) ⟶ Z := (E.hom.app (Opposite.op (Spec (.of k))) ⟨K, hK⟩).down
  let t : Spec (.of k) ⟶ T := pullback.lift zK (𝟙 _) (terminal.hom_ext _ _)
  refine ⟨t, pullback.lift_snd _ _ _, ?_⟩
  have h := NatTrans.naturality_apply E.inv t.op
    (ULift.up (pullback.fst (terminal.from Z) (terminal.from (Spec (.of k)))) :
      ULift.{u + 1} (T ⟶ Z))
  have h2 : (yoneda.obj Z ⋙ uliftFunctor.{u + 1}).map t.op
      (ULift.up (pullback.fst (terminal.from Z) (terminal.from (Spec (.of k)))) :
        ULift.{u + 1} (T ⟶ Z)) =
        E.hom.app (Opposite.op (Spec (.of k))) ⟨K, hK⟩ :=
    ULift.ext (pullback.lift_fst (f := terminal.from Z)
      (g := terminal.from (Spec (.of k))) zK (𝟙 _) (terminal.hom_ext _ _))
  have h3 : E.inv.app (Opposite.op (Spec (.of k)))
      (E.hom.app (Opposite.op (Spec (.of k))) ⟨K, hK⟩) = ⟨K, hK⟩ :=
    Iso.hom_inv_id_apply (E.app (Opposite.op (Spec (.of k)))) _
  rw [h2] at h
  exact (congrArg Subtype.val (h3.symm.trans h)).symm

open ProjectiveQuot in
/-- **The closed subscheme of the `k`-point attached to `Z`, read back on `S`, is `Z`.** The
ideal sheaf of `ℙᴺ_k` cut out by `familyOfClosedImmersion (Z.subschemeι ≫ ι)` pulls back
along `ι` to `Z`: both quotients of `𝒪_S` are `𝒪_Z`. -/
private theorem comap_idealSheafDataOfFamily_familyOfClosedImmersion (k : Type u) [Field k]
    {N : ℕ} (ι : S ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion ι]
    (Z : S.IdealSheafData)
    (hK : (quotient (familyOfClosedImmersion (Z.subschemeι ≫ ι))).IsFinitePresentation) :
    (idealSheafDataOfFamily (familyOfClosedImmersion (Z.subschemeι ≫ ι)) hK).comap ι = Z := by
  haveI := Stacks.ClosedImmersion.full_pushforward ι
  haveI := Stacks.ClosedImmersion.faithful_pushforward ι
  haveI : IsIso (Scheme.Modules.pullbackPushforwardAdjunction ι).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  refine Stacks.IdealSheaf.eq_of_pushforwardUnit_iso ?_
  exact (Stacks.IdealSheaf.comapStructureSheafIso ι _).symm ≪≫
    (Scheme.Modules.pullback ι).mapIso
      (pushforwardUnitSubschemeOfFamilyIso _ hK ≪≫ quotientFamilyOfClosedImmersionIso _ ≪≫
        ((Scheme.Modules.pushforwardComp Z.subschemeι ι).app _).symm) ≪≫
    (asIso (Scheme.Modules.pullbackPushforwardAdjunction ι).counit).app _

/-! ### Flattening -/

/-- **Flattening a family** (Stacks 05UH). A family `𝒢₀` of finite presentation on `S ×_k T₀` has a
universal flattening `q : T ⟶ T₀`, of finite type over `k`, through which every `k`-point of
`T₀` factors, since over a field every module is flat. -/
private theorem exists_flattening (k : Type u) [Field k] [S.Over (Spec (.of k))]
    [IsProper (S ↘ Spec (.of k))]
    {T₀ : Scheme.{u}} (p₀ : T₀ ⟶ Spec (.of k)) [QuasiCompact p₀] [LocallyOfFiniteType p₀]
    (𝒢₀ : (pullback (S ↘ Spec (.of k)) p₀).Modules) [SheafOfModules.IsFinitePresentation 𝒢₀] :
    ∃ (T : Scheme.{u}) (q : T ⟶ T₀) (_ : QuasiCompact (q ≫ p₀))
      (_ : LocallyOfFiniteType (q ≫ p₀)),
      IsFlatOver (pullback.snd (S ↘ Spec (.of k)) (q ≫ p₀)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.map (S ↘ Spec (.of k)) (q ≫ p₀) (S ↘ Spec (.of k)) p₀
          (𝟙 S) q (𝟙 _) (by simp) (by simp))).obj 𝒢₀) ∧
      ∀ t : Spec (.of k) ⟶ T₀, ∃ t' : Spec (.of k) ⟶ T, t' ≫ q = t := by
  let f := pullback.snd (S ↘ Spec (.of k)) p₀
  haveI : IsLocallyNoetherian T₀ := LocallyOfFiniteType.isLocallyNoetherian p₀
  haveI : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI := isQuasicoherent_of_isFinitePresentation 𝒢₀
  obtain ⟨Z, _, hfp, ⟨R⟩⟩ := exists_mono_finitePresentation_representableBy_of_isProper f 𝒢₀
  have hZ : IsFlatOver (pullback.snd f Z.hom).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst f Z.hom)).obj 𝒢₀) := (R.homEquiv (𝟙 Z)).down
  let M := (Scheme.Modules.pullback (pullback.fst f Z.hom)).obj 𝒢₀
  haveI : SheafOfModules.IsFinitePresentation
      (R := structureSheafRing (pullback (S ↘ Spec (.of k)) p₀).toRingedSpace) 𝒢₀ := ‹_›
  haveI : SheafOfModules.IsFinitePresentation M :=
    Stacks.SheafOfModules.modulePullback_isFinitePresentation
      (pullback.fst f Z.hom).toLRSHom.toShHom 𝒢₀
  haveI hMfp : SheafOfModules.IsFinitePresentation
      (R := structureSheafRing (pullback f Z.hom).toRingedSpace) M := ‹_›
  haveI : SheafOfModules.IsQuasicoherent
      (R := structureSheafRing (pullback f Z.hom).toRingedSpace) M :=
    isQuasicoherent_of_isFinitePresentation M
  obtain ⟨hZlfp, hZqc, -⟩ := hfp
  haveI := hZlfp
  haveI := hZqc
  have hsq : IsPullback (pullbackLeftPullbackSndIso (S ↘ Spec (.of k)) p₀ Z.hom).inv
      (pullback.snd (S ↘ Spec (.of k)) (Z.hom ≫ p₀)) (pullback.snd f Z.hom) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [f]⟩
  have hmap : (pullbackLeftPullbackSndIso (S ↘ Spec (.of k)) p₀ Z.hom).inv ≫
      pullback.fst f Z.hom = pullback.map (S ↘ Spec (.of k)) (Z.hom ≫ p₀) (S ↘ Spec (.of k)) p₀
        (𝟙 S) Z.hom (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [f]
  refine ⟨Z.left, Z.hom, inferInstance, inferInstance, ?_, fun t => ?_⟩
  · refine (isFlatOver_iff_of_moduleIso _ ((Scheme.Modules.pullbackComp _ _).app 𝒢₀ ≪≫
      (Scheme.Modules.pullbackCongr hmap).app 𝒢₀)).mp ?_
    exact modulePullback_isFlatOver hsq M hZ
  · let φ : Over.mk t ⟶ Z := R.homEquiv.symm ⟨isFlatOver_spec_field k _ _⟩
    exact ⟨φ.left, Over.w φ⟩

/-! ### The flat family -/

private theorem fibreSection_comp_map (k : Type u) [Field k] [S.Over (Spec (.of k))]
    {T U : Scheme.{u}} (p : T ⟶ Spec (.of k)) (j : U ⟶ T) (t' : Spec (.of k) ⟶ U)
    (ht' : t' ≫ j ≫ p = 𝟙 _) :
    fibreSection k (j ≫ p) t' ht' ≫ pullback.map (S ↘ Spec (.of k)) (j ≫ p)
        (S ↘ Spec (.of k)) p (𝟙 S) j (𝟙 _) (by simp) (by simp) =
      fibreSection k p (t' ≫ j) (by rw [Category.assoc, ht']) := by
  apply pullback.hom_ext
  · simp only [fibreSection, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact Category.comp_id _
  · simp only [fibreSection, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

private theorem fibreSection_familyEmbedding (k : Type u) [Field k] [S.Over (Spec (.of k))]
    {N : ℕ} (ι : S ⟶ projectiveSpaceOver N (Spec (.of k)))
    (hι : ι ≫ pullback.fst _ _ = S ↘ Spec (.of k)) {T : Scheme.{u}} (p : T ⟶ Spec (.of k))
    (t : Spec (.of k) ⟶ T) (ht : t ≫ p = 𝟙 _) :
    fibreSection k p t ht ≫ familyEmbedding k ι p = ι ≫ projectiveSpaceOverMap N t := by
  apply pullback.hom_ext
  · rw [Category.assoc, familyEmbedding, pullback.lift_fst, fibreSection, pullback.lift_snd,
      Category.assoc, projectiveSpaceOverMap, pullback.lift_fst, ← Category.assoc, hι]
  · rw [Category.assoc, familyEmbedding, pullback.lift_snd, ← Category.assoc, fibreSection,
      pullback.lift_fst, Category.id_comp, Category.assoc, projectiveSpaceOverMap,
      pullback.lift_snd, Category.comp_id]

/-- `S ×_k T` is locally Noetherian for `T` locally of finite type over `k`. -/
private theorem isLocallyNoetherian_pullback (k : Type u) [Field k] [S.Over (Spec (.of k))]
    [IsProper (S ↘ Spec (.of k))] {T : Scheme.{u}} (p : T ⟶ Spec (.of k))
    [LocallyOfFiniteType p] : IsLocallyNoetherian (pullback (S ↘ Spec (.of k)) p) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (S ↘ Spec (.of k)) p ≫ p)

/-- The direct image of the structure sheaf of a closed subscheme of a locally Noetherian scheme
is of finite presentation. -/
private theorem isFinitePresentation_pushforward_unitModule {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (i : Y ⟶ X) [IsClosedImmersion i] :
    ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y)).IsFinitePresentation := by
  haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_isClosedImmersion i
  haveI : (Stacks.Ample.unitModule Y).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit Y
  haveI : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Y)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i _
  exact _root_.isFinitePresentation_of_isCoherent _

open ProjectiveQuot in
/-- **A flat family containing every closed subscheme with Hilbert function `P`.** The universal
member of `Quot^P_{𝒪/ℙᴺ}` cuts out a closed subscheme of `ℙᴺ_{T₀}`; its intersection with
`S ×_k T₀`, flattened over `T₀`, is a closed subscheme of `S ×_k T` flat over `T`, and every closed
subscheme `Z ⊆ S` with Hilbert function `P` is its fibre over a `k`-point. -/
private theorem exists_flatFamily (k : Type u) [Field k]
    [S.Over (Spec (.of k))] [IsProper (S ↘ Spec (.of k))] {N : ℕ}
    (ι : S ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion ι]
    (hι : ι ≫ pullback.fst _ _ = S ↘ Spec (.of k)) (H : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    (eH : H ≅ (Scheme.Modules.pullback ι).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k))))
    (P : Polynomial ℚ) :
    ∃ (T : Scheme.{u}) (p : T ⟶ Spec (.of k)) (_ : QuasiCompact p) (_ : LocallyOfFiniteType p)
      (D : (pullback (S ↘ Spec (.of k)) p).IdealSheafData),
      Flat (D.subschemeι ≫ pullback.snd (S ↘ Spec (.of k)) p) ∧
      ∀ Z : S.IdealSheafData, (∀ n : ℤ, P.eval (n : ℚ) =
          Mori.subschemeHilbertFunction k (S ↘ Spec (.of k)) Z.subschemeι H n) →
        ∃ (t : Spec (.of k) ⟶ T) (ht : t ≫ p = 𝟙 _), D.comap (fibreSection k p t ht) = Z := by
  obtain ⟨T₀, p₀, hqc, hlft, U₀, hU₀, hcov⟩ := exists_quot k N P
  let 𝒲 := idealSheafDataOfFamily U₀ hU₀.1.1
  let D₀ := 𝒲.comap (familyEmbedding k ι p₀)
  haveI := isLocallyNoetherian_pullback (S := S) k p₀
  haveI := isFinitePresentation_pushforward_unitModule D₀.subschemeι
  obtain ⟨T, q, hqc1, hlft1, hflat, hlift⟩ := exists_flattening k p₀
    ((Scheme.Modules.pushforward D₀.subschemeι).obj (Stacks.Ample.unitModule D₀.subscheme))
  let m := pullback.map (S ↘ Spec (.of k)) (q ≫ p₀) (S ↘ Spec (.of k)) p₀ (𝟙 S) q (𝟙 _)
    (by simp) (by simp)
  refine ⟨T, q ≫ p₀, hqc1, hlft1, D₀.comap m, ?_, fun Z hZ => ?_⟩
  · refine flat_of_isFlatOver_pushforward_unitModule _ _ ?_
    exact (isFlatOver_iff_of_moduleIso _ (Stacks.IdealSheaf.comapStructureSheafIso m D₀)).mp hflat
  · have hKZ := familyOfClosedImmersion_mem_hilbertFamilies k ι hι H eH Z P hZ
    obtain ⟨t₀, ht₀, hbc⟩ := hcov _ hKZ
    obtain ⟨t₁, ht₁⟩ := hlift t₀
    have ht : t₁ ≫ q ≫ p₀ = 𝟙 _ := by rw [← Category.assoc, ht₁, ht₀]
    refine ⟨t₁, ht, ?_⟩
    have hK' : (quotient (baseChange t₀ U₀)).IsFinitePresentation := hbc ▸ hKZ.1.1
    have key : ∀ (K : Subobject (freeModule N 1 (Spec (.of k))))
        (hK : (quotient K).IsFinitePresentation), K = familyOfClosedImmersion (Z.subschemeι ≫ ι) →
        (idealSheafDataOfFamily K hK).comap ι = Z := by
      rintro _ hK rfl
      exact comap_idealSheafDataOfFamily_familyOfClosedImmersion k ι Z hK
    rw [← Scheme.IdealSheafData.comap_comp, fibreSection_comp_map,
      ← Scheme.IdealSheafData.comap_comp]
    subst ht₁
    rw [fibreSection_familyEmbedding k ι hι, Scheme.IdealSheafData.comap_comp,
      ← idealSheafDataOfFamily_baseChange _ hU₀.1.1 hK']
    exact key _ hK' hbc

/-! ### Fibres over `k`-points -/

/-- The fibre section over `t` is the base change of `t` along `S ×_k T ⟶ T`. -/
private theorem isPullback_fibreSection (k : Type u) [Field k] [S.Over (Spec (.of k))]
    {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) (t : Spec (.of k) ⟶ T) (ht : t ≫ p = 𝟙 _) :
    IsPullback (fibreSection k p t ht) (S ↘ Spec (.of k)) (pullback.snd (S ↘ Spec (.of k)) p)
      t := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, ht]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The fibre section over `t` is the base change of `ℙᴺ_k ⟶ ℙᴺ_T` along `S ×_k T ⟶ ℙᴺ_T`. -/
private theorem isPullback_fibreSection_familyEmbedding (k : Type u) [Field k]
    [S.Over (Spec (.of k))] {N : ℕ} (ι : S ⟶ projectiveSpaceOver N (Spec (.of k)))
    (hι : ι ≫ pullback.fst _ _ = S ↘ Spec (.of k)) {T : Scheme.{u}} (p : T ⟶ Spec (.of k))
    (t : Spec (.of k) ⟶ T) (ht : t ≫ p = 𝟙 _) :
    IsPullback (fibreSection k p t ht) ι (familyEmbedding k ι p) (projectiveSpaceOverMap N t) := by
  refine IsPullback.of_right ?_ (fibreSection_familyEmbedding k ι hι p t ht)
    (isPullback_familyEmbedding k ι hι p)
  rw [pullback.lift_fst, projectiveSpaceOverMap_comp, ht, projectiveSpaceOverMap_id]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

open ProjectiveQuot in
/-- **At a `k`-point whose fibre has Hilbert function `P`, the family lies in the Hilbert
locus of `P`.** -/
private theorem fibreHilbert_apply_eq_of_comap_fibreSection (k : Type u) [Field k]
    [S.Over (Spec (.of k))] [IsProper (S ↘ Spec (.of k))] {N : ℕ}
    (ι : S ⟶ projectiveSpaceOver N (Spec (.of k))) [IsClosedImmersion ι]
    (hι : ι ≫ pullback.fst _ _ = S ↘ Spec (.of k)) (H : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    (eH : H ≅ (Scheme.Modules.pullback ι).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k))))
    (P : Polynomial ℚ)
    {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) (D : (pullback (S ↘ Spec (.of k)) p).IdealSheafData)
    [((Scheme.Modules.pushforward (D.subschemeι ≫ familyEmbedding k ι p)).obj
      (Stacks.Ample.unitModule D.subscheme)).IsFinitePresentation]
    (t : Spec (.of k) ⟶ T) (ht : t ≫ p = 𝟙 _)
    (hZ : ∀ n : ℤ, P.eval (n : ℚ) = Mori.subschemeHilbertFunction k (S ↘ Spec (.of k))
      (D.comap (fibreSection k p t ht)).subschemeι H n)
    (pt : Spec (.of k)) (d : ℤ) :
    (fibreHilbert ((Scheme.Modules.pushforward (D.subschemeι ≫ familyEmbedding k ι p)).obj
      (Stacks.Ample.unitModule D.subscheme)) (t pt) d : ℚ) = P.eval (d : ℚ) := by
  haveI := isClosedImmersion_familyEmbedding k ι hι p
  let s := fibreSection (S := S) k p t ht
  have hsq := (Stacks.Bertini.isPullback_subschemeι_comap D s).flip.paste_vert
    (isPullback_fibreSection_familyEmbedding k ι hι p t ht)
  haveI : IsClosedImmersion ((D.comap s).subschemeι ≫ ι) := inferInstance
  let eF := Stacks.Chow.pullbackPushforwardStructureSheafIso hsq
  have hK := familyOfClosedImmersion_mem_hilbertFamilies k ι hι H eH (D.comap s) P hZ
  haveI := hK.1.1
  haveI : ((Scheme.Modules.pushforward ((D.comap s).subschemeι ≫ ι)).obj
      (Stacks.Ample.unitModule (D.comap s).subscheme)).IsFinitePresentation :=
    SheafOfModules.IsFinitePresentation.of_iso inferInstance eF
  have h1 := fibreHilbert_pullback t ((Scheme.Modules.pushforward
    (D.subschemeι ≫ familyEmbedding k ι p)).obj (Stacks.Ample.unitModule D.subscheme)) pt
  rw [← h1, fibreHilbert_eq_of_iso eF pt,
    ← fibreHilbert_eq_of_iso (quotientFamilyOfClosedImmersionIso _) pt]
  exact ((hasFibreHilbertPolynomial_iff _).1 hK.2) pt d

/-- **The fibre of a family over a `k`-point is the fibre section.** Over an algebraically
closed `k`, the residue field of a `k`-point `t` of a finite-type `k`-scheme is `k`, so the
scheme-theoretic fibre over `t` is `S`, embedded by the fibre section; an effective Cartier
divisor on `S` is therefore one on the fibre. -/
private theorem isEffectiveCartierDivisor_comap_fiberι (k : Type u) [Field k] [IsAlgClosed k]
    [S.Over (Spec (.of k))] {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (D : (pullback (S ↘ Spec (.of k)) p).IdealSheafData)
    (t : Spec (.of k) ⟶ T) (ht : t ≫ p = 𝟙 _)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (fibreSection k p t ht))) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (D.comap ((pullback.snd (S ↘ Spec (.of k)) p).fiberι
        (t (IsLocalRing.closedPoint k)))) := by
  set x := t (IsLocalRing.closedPoint k)
  have hx : IsClosed {x} := (pointEquivClosedPoint p ⟨t, ht⟩).2
  have htx : t = pointOfClosedPoint p x hx :=
    congrArg Subtype.val ((pointEquivClosedPoint p).symm_apply_apply ⟨t, ht⟩).symm
  let ε := Spec.map (residueFieldIsoBase p x hx).hom
  have hε : ε ≫ T.fromSpecResidueField x = t := htx.symm
  let pr := pullback.snd (S ↘ Spec (.of k)) p
  let c : S ⟶ pr.fiber x := pullback.lift (fibreSection k p t ht) (S ↘ Spec (.of k) ≫ ε)
    (by rw [Category.assoc, hε]; exact (isPullback_fibreSection k p t ht).w)
  have hsq : IsPullback c (S ↘ Spec (.of k)) (pr.fiberToSpecResidueField x) ε := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    have h1 : c ≫ pullback.fst pr (T.fromSpecResidueField x) = fibreSection k p t ht :=
      pullback.lift_fst _ _ _
    erw [h1, hε]
    exact isPullback_fibreSection k p t ht
  haveI := hsq.isIso_fst_of_isIso
  have hc : inv c ≫ fibreSection k p t ht = pr.fiberι x := by
    rw [IsIso.inv_comp_eq]
    exact (pullback.lift_fst _ _ _).symm
  rw [← hc, Scheme.IdealSheafData.comap_comp]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _ hD

/-- **Near a point whose fibre is Cartier, a flat family is Cartier** (Stacks 062Y). If the fibre
of `D` through `x` is an effective Cartier divisor, then `D` is one on a neighbourhood of `x`:
on the support of `D` by the fibrewise criterion, off it trivially. -/
private theorem exists_opens_isEffectiveCartierDivisor_of_fiberι (k : Type u) [Field k]
    [S.Over (Spec (.of k))] [IsProper (S ↘ Spec (.of k))] {T : Scheme.{u}}
    (p : T ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (D : (pullback (S ↘ Spec (.of k)) p).IdealSheafData)
    [Flat (D.subschemeι ≫ pullback.snd (S ↘ Spec (.of k)) p)]
    (x : ↥(pullback (S ↘ Spec (.of k)) p))
    (hx : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap
      ((pullback.snd (S ↘ Spec (.of k)) p).fiberι (pullback.snd (S ↘ Spec (.of k)) p x)))) :
    ∃ W : (pullback (S ↘ Spec (.of k)) p).Opens, x ∈ W ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (D.comap W.ι) := by
  haveI := isLocallyNoetherian_pullback (S := S) k p
  haveI : LocallyOfFinitePresentation (S ↘ Spec (.of k)) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : LocallyOfFinitePresentation D.subschemeι :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  by_cases hxs : x ∈ D.support
  · obtain ⟨W, hxW, -, hrel⟩ :=
      Stacks.Divisors.exists_isRelativeEffectiveCartierDivisor_of_flat_of_finitePresentation
        _ D x hxs ⟨⊤, trivial, Stacks.Divisors.isPullbackDefined_of_flat _ _ hx⟩
        (Flat.stalkMap (D.subschemeι ≫ pullback.snd _ p) _)
    exact ⟨W, hxW, hrel.1⟩
  · let W : (pullback (S ↘ Spec (.of k)) p).Opens := D.support.compl
    refine ⟨W, hxs, ?_⟩
    have hc : D.comap W.ι = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
      ext y
      simp only [TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
        TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
      have hy : W.ι y ∈ (W : Set _) := by
        rw [← Scheme.Opens.range_ι]
        exact Set.mem_range_self _
      exact hy
    rw [hc]
    exact Stacks.Divisors.isEffectiveCartierDivisor_top

/-! ### Restricting a family to an open of the base -/

/-- **Effective Cartier along an open immersion, pointwise.** If every point of the source of an
open immersion `m` lands in an open on which `D` is effective Cartier, then so is `D.comap m`. -/
theorem isEffectiveCartierDivisor_comap_of_forall_mem {X Y : Scheme.{u}} (m : Y ⟶ X)
    [IsOpenImmersion m] (D : X.IdealSheafData)
    (h : ∀ y, ∃ W : X.Opens, m y ∈ W ∧ Stacks.Divisors.IsEffectiveCartierDivisor (D.comap W.ι)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (D.comap m) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_flat_universallyOpen_pointwise _
    fun y => ?_
  obtain ⟨W, hyW, hW⟩ := h y
  refine ⟨m ⁻¹ᵁ W, (m ⁻¹ᵁ W).ι, inferInstance, inferInstance, ?_, ?_⟩
  · rw [Scheme.Opens.range_ι]
    exact hyW
  · rw [← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι,
      Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.isPullbackDefined_of_flat _ _ hW

/-- `S ×_k T'` is the base change of `S ×_k T` along `g : T' ⟶ T`. -/
private theorem isPullback_map_snd (k : Type u) [Field k] [S.Over (Spec (.of k))]
    {T T' : Scheme.{u}} (p : T ⟶ Spec (.of k)) (g : T' ⟶ T) :
    IsPullback (pullback.map (S ↘ Spec (.of k)) (g ≫ p) (S ↘ Spec (.of k)) p (𝟙 S) g (𝟙 _)
        (by simp) (by simp))
      (pullback.snd (S ↘ Spec (.of k)) (g ≫ p)) (pullback.snd (S ↘ Spec (.of k)) p) g := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback (S ↘ Spec (.of k)) p)
  simp only [pullback.lift_fst, Category.comp_id]
  exact IsPullback.of_hasPullback _ _

/-- The embedding of `S ×_k T'` into `ℙᴺ_{T'}` is the base change of the one of `S ×_k T`. -/
private theorem isPullback_map_familyEmbedding (k : Type u) [Field k] [S.Over (Spec (.of k))]
    {N : ℕ} (ι : S ⟶ projectiveSpaceOver N (Spec (.of k)))
    {T T' : Scheme.{u}} (p : T ⟶ Spec (.of k)) (g : T' ⟶ T) :
    IsPullback (pullback.map (S ↘ Spec (.of k)) (g ≫ p) (S ↘ Spec (.of k)) p (𝟙 S) g (𝟙 _)
        (by simp) (by simp))
      (familyEmbedding k ι (g ≫ p)) (familyEmbedding k ι p) (projectiveSpaceOverMap N g) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_projectiveSpaceOverMap N g)
  · rw [familyEmbedding_fst, familyEmbedding_fst]
    exact isPullback_map_snd k p g
  · have e1 : familyEmbedding k ι p ≫ pullback.fst _ _ = pullback.snd _ _ :=
      familyEmbedding_fst k ι p
    have e2 : projectiveSpaceOverMap N g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g :=
      pullback.lift_fst _ _ _
    have e3 : familyEmbedding k ι (g ≫ p) ≫ pullback.fst _ _ = pullback.snd _ _ :=
      familyEmbedding_fst k ι (g ≫ p)
    have e4 : pullback.map (S ↘ Spec (.of k)) (g ≫ p) (S ↘ Spec (.of k)) p (𝟙 S) g (𝟙 _)
        (by simp) (by simp) ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g :=
      pullback.lift_snd _ _ _
    have f1 : familyEmbedding k ι p ≫ pullback.snd _ _ = pullback.fst _ _ ≫ ι ≫
        projectiveSpaceOver.toIntegralAtUniverse N _ := pullback.lift_snd _ _ _
    have f2 : projectiveSpaceOverMap N g ≫ projectiveSpaceOver.toIntegralAtUniverse N T =
        projectiveSpaceOver.toIntegralAtUniverse N T' := projectiveSpaceOverMap_snd N g
    have f3 : familyEmbedding k ι (g ≫ p) ≫ pullback.snd _ _ = pullback.fst _ _ ≫ ι ≫
        projectiveSpaceOver.toIntegralAtUniverse N _ := pullback.lift_snd _ _ _
    have f4 : pullback.map (S ↘ Spec (.of k)) (g ≫ p) (S ↘ Spec (.of k)) p (𝟙 S) g (𝟙 _)
        (by simp) (by simp) ≫ pullback.fst _ _ = pullback.fst _ _ :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [e1, e2, ← Category.assoc, e3, e4]
    · simp only [Category.assoc]
      erw [f1, f2, f3, ← Category.assoc, f4]

end

/-- A `k`-point of `T` whose closed point lies in an open `V` factors through `V`. -/
private theorem exists_lift_opensι_of_closedPoint_mem (k : Type u) [Field k] {T : Scheme.{u}}
    (V : T.Opens) (t : Spec (.of k) ⟶ T) (ht : t (IsLocalRing.closedPoint k) ∈ V) :
    ∃ t' : Spec (.of k) ⟶ V, t' ≫ V.ι = t := by
  haveI : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  refine ⟨IsOpenImmersion.lift V.ι t ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨a, rfl⟩
  rw [Scheme.Opens.range_ι, Subsingleton.elim a (IsLocalRing.closedPoint k)]
  exact ht

open ProjectiveQuot in
/-- **Finitely many families of effective Cartier divisors with fixed Hilbert polynomial.** Let `S`
be a projective scheme over an algebraically closed field `k`, `H` a very ample invertible sheaf on
`S` and `P ∈ ℚ[X]` integer-valued on `ℤ`. There are finitely many finite-type `k`-schemes `T i`,
each with finitely many irreducible components, and effective Cartier divisors
`𝒟 i ⊆ S ×_k T i`, flat over `T i`, whose fibres over all points of `T i` have Hilbert polynomial
`P` with respect to `H`, such that every effective Cartier divisor `Z ⊆ S` with
`χ(Z, H^{⊗ n}|_Z) = P(n)` for all `n ∈ ℤ` is the fibre of some `𝒟 i` over a `k`-point of `T i`. -/
@[mmp "lem_mmp_foundation_fixed_polynomial_cartier_families"]
public theorem exists_finite_isEffectiveCartierDivisor_families (k : Type u) [Field k]
    [IsAlgClosed k] (S : Scheme.{u}) [S.Over (Spec (.of k))]
    (hS : IsProjectiveMorphism (S ↘ Spec (.of k))) (H : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    (hH : Intersection.IsVeryAmple k H) (P : Polynomial ℚ)
    (hP : ∀ n : ℤ, ∃ m : ℤ, P.eval (n : ℚ) = m) :
    haveI := isProper_of_isProjectiveMorphism _ hS
    ∃ (ι : Type u) (_ : Finite ι) (T : ι → Scheme.{u}) (p : ∀ i, T i ⟶ Spec (.of k))
      (_ : ∀ i, LocallyOfFiniteType (p i)) (_ : ∀ i, QuasiCompact (p i))
      (_ : ∀ i, (irreducibleComponents (T i)).Finite)
      (𝒟 : ∀ i, (pullback (S ↘ Spec (.of k)) (p i)).IdealSheafData)
      (_ : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (𝒟 i))
      (_ : ∀ i, Flat ((𝒟 i).subschemeι ≫ pullback.snd (S ↘ Spec (.of k)) (p i)))
      (_ : ∀ (i : ι) (t : T i) (n : ℤ),
        P.eval (n : ℚ) = Mori.subschemeHilbertFunction ((T i).residueField t)
          (pullback.snd (pullback.snd (S ↘ Spec (.of k)) (p i)) ((T i).fromSpecResidueField t))
          ((𝒟 i).comap (pullback.fst (pullback.snd (S ↘ Spec (.of k)) (p i))
            ((T i).fromSpecResidueField t))).subschemeι
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd (S ↘ Spec (.of k)) (p i))
            ((T i).fromSpecResidueField t) ≫ pullback.fst (S ↘ Spec (.of k)) (p i))).obj H) n),
      ∀ Z : S.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor Z →
        (∀ n : ℤ, P.eval (n : ℚ) =
          Mori.subschemeHilbertFunction k (S ↘ Spec (.of k)) Z.subschemeι H n) →
        ∃ (i : ι) (t : Spec (.of k) ⟶ T i) (ht : t ≫ p i = 𝟙 _),
          (𝒟 i).comap (pullback.lift (𝟙 S) (S ↘ Spec (.of k) ≫ t)
            (by rw [Category.assoc, ht, Category.comp_id, Category.id_comp])) = Z := by
  haveI hprop := isProper_of_isProjectiveMorphism _ hS
  obtain ⟨N, ι, hι, hιk, ⟨eH⟩⟩ := exists_embedding k H hH
  haveI := hι
  obtain ⟨T, p, hqc, hlft, D, hflat, hcov⟩ := exists_flatFamily k ι hιk H eH P
  haveI := isClosedImmersion_familyEmbedding k ι hιk p
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsLocallyNoetherian (projectiveSpaceOver N T) :=
    LocallyOfFiniteType.isLocallyNoetherian ((projectiveSpaceOver N T ↘ T) ≫ p)
  haveI := isLocallyNoetherian_pullback (S := S) k p
  haveI := hflat
  let j := familyEmbedding k ι p
  let pr := pullback.snd (S ↘ Spec (.of k)) p
  -- the Hilbert locus
  let F := (Scheme.Modules.pushforward (D.subschemeι ≫ j)).obj (Stacks.Ample.unitModule D.subscheme)
  haveI hFfp : F.IsFinitePresentation := isFinitePresentation_pushforward_unitModule _
  haveI : Flat ((D.subschemeι ≫ j) ≫ (projectiveSpaceOver N T ↘ T)) := by
    rw [Category.assoc]
    erw [familyEmbedding_fst]
    exact hflat
  let G := C1590Private.fibreHilbertLocus P F
  have hG : IsOpen G := C1590Private.isOpen_fibreHilbertLocus P
    ⟨hFfp, Stacks.Chow.isFlatOver_pushforwardStructureSheaf (D.subschemeι ≫ j) _⟩
  -- the Cartier locus
  let X := pullback (S ↘ Spec (.of k)) p
  let Gx : Set X :=
    {x | ∃ W : X.Opens, x ∈ W ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (D.comap W.ι)}
  have hGx : IsOpen Gx := isOpen_iff_forall_mem_open.mpr fun x hx => by
    obtain ⟨W, hxW, hW⟩ := hx
    exact ⟨W, fun y hy => ⟨W, hy, hW⟩, W.2, hxW⟩
  have hB : IsClosed (pr '' Gxᶜ) := pr.isClosedMap _ hGx.isClosed_compl
  let V : T.Opens := ⟨G ∩ (pr '' Gxᶜ)ᶜ, hG.inter hB.isOpen_compl⟩
  let m := pullback.map (S ↘ Spec (.of k)) (V.ι ≫ p) (S ↘ Spec (.of k)) p (𝟙 S) V.ι (𝟙 _)
    (by simp) (by simp)
  have hm := isPullback_map_snd (S := S) k p V.ι
  haveI hmopen : IsOpenImmersion m :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hm.flip inferInstance
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace p
  refine ⟨PUnit, inferInstance, fun _ => V, fun _ => V.ι ≫ p, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => ?_, fun _ => D.comap m, fun _ => ?_, fun _ => ?_,
    fun _ v n => ?_, fun Z hZc hZ => ?_⟩
  · -- finitely many irreducible components
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (V.ι ≫ p)
    haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ p)
    haveI : IsNoetherian (V : Scheme.{u}) := {}
    change (irreducibleComponents (V : Scheme.{u})).Finite
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  · -- effective Cartier
    refine isEffectiveCartierDivisor_comap_of_forall_mem m D fun y => (?_ : m y ∈ Gx)
    by_contra hc
    have h1 : pr (m y) = V.ι (pullback.snd (S ↘ Spec (.of k)) (V.ι ≫ p) y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    have h2 : V.ι (pullback.snd (S ↘ Spec (.of k)) (V.ι ≫ p) y) ∈ (V : Set T) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _
    exact h2.2 ⟨m y, hc, h1⟩
  · -- flat
    exact MorphismProperty.of_isPullback (P := @Flat)
      ((Stacks.Bertini.isPullback_subschemeι_comap D m).flip.paste_vert hm) hflat
  · -- Hilbert polynomial on every fibre
    haveI : IsLocallyNoetherian (projectiveSpaceOver N V) :=
      LocallyOfFiniteType.isLocallyNoetherian ((projectiveSpaceOver N V ↘ V) ≫ V.ι ≫ p)
    haveI := isClosedImmersion_familyEmbedding k ι hιk (V.ι ≫ p)
    haveI := isFinitePresentation_pushforward_unitModule
      ((D.comap m).subschemeι ≫ familyEmbedding k ι (V.ι ≫ p))
    have hsq := (Stacks.Bertini.isPullback_subschemeι_comap D m).flip.paste_vert
      (isPullback_map_familyEmbedding k ι p V.ι)
    have h1 := fibreHilbert_eq_subschemeHilbertFunction k ι hιk H eH (V.ι ≫ p) (D.comap m) v n
    rw [← h1, fibreHilbert_eq_of_iso (Stacks.Chow.pullbackPushforwardStructureSheafIso hsq).symm v,
      fibreHilbert_pullback]
    have hv : V.ι v ∈ (V : Set T) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self _
    exact (hv.1 n).symm
  · -- every divisor with Hilbert function `P` is a fibre
    obtain ⟨t, ht, hDZ⟩ := hcov Z hZ
    set τ := t (IsLocalRing.closedPoint k)
    have hZ' : ∀ n : ℤ, P.eval (n : ℚ) = Mori.subschemeHilbertFunction k (S ↘ Spec (.of k))
        (D.comap (fibreSection k p t ht)).subschemeι H n := hDZ ▸ hZ
    have hτG : τ ∈ G := fun d =>
      fibreHilbert_apply_eq_of_comap_fibreSection k ι hιk H eH P p D t ht hZ' _ d
    have hfib : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (pr.fiberι τ)) :=
      isEffectiveCartierDivisor_comap_fiberι k p D t ht (hDZ ▸ hZc)
    have hτB : τ ∉ pr '' Gxᶜ := by
      rintro ⟨x, hxB, hxτ⟩
      exact hxB (exists_opens_isEffectiveCartierDivisor_of_fiberι k p D x
        (by rw [hxτ]; exact hfib))
    obtain ⟨t', ht'0⟩ := exists_lift_opensι_of_closedPoint_mem k V t ⟨hτG, hτB⟩
    have ht' : t' ≫ V.ι ≫ p = 𝟙 _ := by rw [← Category.assoc, ht'0, ht]
    refine ⟨PUnit.unit, t', ht', ?_⟩
    change (D.comap m).comap (fibreSection k (V.ι ≫ p) t' ht') = Z
    have key : ∀ (t₁ : Spec (.of k) ⟶ T) (h₁ : t₁ ≫ p = 𝟙 _), t₁ = t →
        D.comap (fibreSection k p t₁ h₁) = Z := by
      rintro _ _ rfl
      exact hDZ
    rw [← Scheme.IdealSheafData.comap_comp, fibreSection_comp_map]
    exact key _ _ ht'0

end MMP
