module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ProjectiveSpace
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDivisorProjectiveLineFibres
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.RationalPointFibre

/-!
# The topological fibres of a smooth blowup

Let `V` be a smooth scheme over `ℂ`, `T = V(I)` a smooth closed subscheme and
`b : V' = Bl_T V ⟶ V` the blowup. For a complex point `t` of `V` lying on `T`, with image `z` in
`T`, the fibre `(b^an)⁻¹(t)` of the complex realization of `b` is complex projective space
`ℙⁿ(ℂ)`, where `n + 1` is the height of the ideal of `T` in `𝒪_{V,z}`; for an irreducible centre
of codimension `c` this is `ℙ^{c-1}(ℂ)`.

The proof passes through three identifications.

* The scheme fibre `E_z` of the exceptional divisor `E ⟶ T` at `z` is the fibre of `b` over
  `Spec κ(z) ⟶ V`, by the cartesian square `E = V' ×_V T`. Since `t` is a section of the
  structure morphism, `κ(z) ⟶ ℂ` is a ring isomorphism (it is split by `ℂ ⟶ κ(z)`), so `E_z` is
  also the fibre of `b` over the `ℂ`-point `t`. For a cartesian square `P = A ×_S Spec ℂ` the map
  `P(ℂ) ⟶ A(ℂ)` is a topological embedding onto the points lying over the base point.
* `E_z ≅ ℙⁿ_{κ(z)}` by the projective bundle structure of `E ⟶ T`, and changing the coefficients
  along `κ(z) ≅ ℂ` gives `ℙⁿ_{κ(z)} ≅ ℙⁿ_ℂ` over `ℂ`.
* `ℙⁿ_ℂ(ℂ) ≃ₜ ℙⁿ(ℂ)` (`MMP.Topology.underlyingSpaceProjectiveSpaceHomeomorph`).

## Main definitions

* `MMP.Topology.underlyingSpaceHomeomorphOfIso`: an isomorphism of `K`-schemes induces a
  homeomorphism of `K`-points.
* `MMP.Topology.projPolyGradingIsoOfIso`: `Proj k[T₀,…,Tₙ] ≅ Proj k'[T₀,…,Tₙ]` for an
  isomorphism of fields `k ≅ k'`.
* `MMP.Topology.projSpaceIsoProjectiveSpace`: `ℙ^{ULift (Fin (n + 1))}_k ≅ ℙⁿ_{k'}` for an
  isomorphism of fields `k ≅ k'`.

## Main results

* `MMP.Topology.isEmbedding_mapFun_of_isPullback`: the `K`-points of a fibre over a `K`-point.
* `MMP.Topology.projSpaceIsoProjectiveSpace_hom_toSpec`: the isomorphism lies over
  `Spec.map φ.inv : Spec k ⟶ Spec k'`.
* `MMP.Topology.nonempty_homeomorph_preimage_analyticMap_blowUpToBase`: `(b^an)⁻¹(t) ≃ₜ ℙⁿ(ℂ)`.
* `MMP.Topology.nonempty_homeomorph_preimage_analyticMap_blowUpToBase_of_isIrreducible`: the
  same for an irreducible centre of codimension `c`, with `n = c - 1`.
* `MMP.Topology.height_ker_stalkMap_subschemeι_eq_codimension_closureSingleton`: for a smooth
  centre, the height of its ideal at `z` is the codimension of the component through `z`.
* `MMP.Topology.maximal_closureSingleton_subschemeι`: an irreducible component of the centre is
  a maximal irreducible closed subset of its support.
* `MMP.Topology.nonempty_homeomorph_preimage_analyticMap_blowUpToBase_of_codimension`: the
  fibre is `ℙ^{c-1}(ℂ)` for a smooth centre, not necessarily connected, all of whose maximal
  irreducible closed subsets have codimension `c`.

## References

* [Stacks Project, Tags 01OG, 0FUT]
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology

namespace MMP.Topology

section UnderlyingSpace

open MMP.UnderlyingSpace

variable {K : Type} [Field K] [TopologicalSpace K]

/-- An isomorphism of schemes over `K` induces a homeomorphism of their spaces of `K`-points. -/
def underlyingSpaceHomeomorphOfIso {X Y : Scheme.{0}} [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] (e : X ≅ Y) [e.hom.IsOver (Spec (.of K))] :
    UnderlyingSpace K X ≃ₜ UnderlyingSpace K Y :=
  { toFun := mapFun e.hom
    invFun := mapFun e.inv
    left_inv := fun p ↦ UnderlyingSpace.ext (by simp)
    right_inv := fun p ↦ UnderlyingSpace.ext (by simp)
    continuous_toFun := continuous_mapFun _
    continuous_invFun := continuous_mapFun _ }

/-- The image of a `K`-point `p` under `underlyingSpaceHomeomorphOfIso e` is `p ≫ e.hom`. -/
@[simp]
lemma toHom_underlyingSpaceHomeomorphOfIso_apply {X Y : Scheme.{0}} [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] (e : X ≅ Y) [e.hom.IsOver (Spec (.of K))]
    (p : UnderlyingSpace K X) :
    (underlyingSpaceHomeomorphOfIso e p).toHom = p.toHom ≫ e.hom :=
  rfl

/-- The image of a `K`-point `p` under `(underlyingSpaceHomeomorphOfIso e).symm` is
`p ≫ e.inv`. -/
@[simp]
lemma toHom_underlyingSpaceHomeomorphOfIso_symm_apply {X Y : Scheme.{0}} [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] (e : X ≅ Y) [e.hom.IsOver (Spec (.of K))]
    (p : UnderlyingSpace K Y) :
    ((underlyingSpaceHomeomorphOfIso e).symm p).toHom = p.toHom ≫ e.inv :=
  rfl

variable [IsTopologicalRing K] [ContinuousInv₀ K] [T1Space K]

/-- **The `K`-points of a fibre over a `K`-point.** For a cartesian square `P = A ×_S Spec K`
along a `K`-point `s` of `S`, with `P` a `K`-scheme through its second projection, the map
`P(K) → A(K)` is a topological embedding whose image is the set of `K`-points of `A` lying over
`s`. -/
theorem isEmbedding_mapFun_of_isPullback {P A S : Scheme.{0}} [P.Over (Spec (.of K))]
    [A.Over (Spec (.of K))] {fst : P ⟶ A} {f : A ⟶ S} {s : Spec (.of K) ⟶ S}
    [fst.IsOver (Spec (.of K))] (H : IsPullback fst (P ↘ Spec (.of K)) f s) :
    IsEmbedding (mapFun (K := K) fst) ∧
      Set.range (mapFun (K := K) fst) = {a | a.toHom ≫ f = s} := by
  let : (Spec (.of K)).Over (Spec (.of K)) := ⟨𝟙 _⟩
  have : (P ↘ Spec (.of K)).IsOver (Spec (.of K)) := ⟨Category.comp_id _⟩
  have : Unique (UnderlyingSpace K (Spec (.of K))) :=
    { default := ⟨𝟙 _, Category.comp_id _⟩
      uniq := fun p ↦ UnderlyingSpace.ext ((Category.comp_id _).symm.trans p.toHom_comp_over) }
  refine ⟨?_, ?_⟩
  · exact (Homeomorph.prodUnique (UnderlyingSpace K A)
      (UnderlyingSpace K (Spec (.of K)))).isEmbedding.comp
      (isEmbedding_prodMap_of_isPullback (K := K) H)
  · ext a
    refine ⟨?_, fun ha ↦ ?_⟩
    · rintro ⟨w, rfl⟩
      change (w.toHom ≫ fst) ≫ f = s
      rw [Category.assoc, H.w, ← Category.assoc, w.toHom_comp_over, Category.id_comp]
    · refine ⟨⟨H.lift a.toHom (𝟙 _) (by rw [ha, Category.id_comp]), H.lift_snd _ _ _⟩, ?_⟩
      exact UnderlyingSpace.ext (H.lift_fst _ _ _)

end UnderlyingSpace

section ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open MMP.Intersection Stacks.AlgebraicGeometry.ProjPolyChart

variable {k k' : Type} [Field k] [Field k'] (φ : CommRingCat.of k ≅ CommRingCat.of k') (n : ℕ)

/-- Coefficient change along an isomorphism of fields `k ≅ k'` identifies
`Proj k[T₀, …, Tₙ]` with `Proj k'[T₀, …, Tₙ]`. -/
def projPolyGradingIsoOfIso :
    AlgebraicGeometry.Proj (polyGrading k n) ≅ AlgebraicGeometry.Proj (polyGrading k' n) where
  hom := Proj.map (coeffGradedHom k' n φ.inv.hom) (irrelevant_le_map_coeffGradedHom k' n _)
  inv := Proj.map (coeffGradedHom k n φ.hom.hom) (irrelevant_le_map_coeffGradedHom k n _)
  hom_inv_id := by
    rw [← Proj.map_comp]
    refine (projMap_congr _ _ _ _ ?_).trans Proj.map_id
    refine GradedRingHom.ext fun p ↦ ?_
    change MvPolynomial.map φ.inv.hom (MvPolynomial.map φ.hom.hom p) = p
    rw [MvPolynomial.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
      MvPolynomial.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    refine (projMap_congr _ _ _ _ ?_).trans Proj.map_id
    refine GradedRingHom.ext fun p ↦ ?_
    change MvPolynomial.map φ.hom.hom (MvPolynomial.map φ.inv.hom p) = p
    rw [MvPolynomial.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
      MvPolynomial.map_id]

/-- **`ℙ^{ULift (Fin (n + 1))}_k ≅ ℙⁿ_{k'}`** for an isomorphism of fields `k ≅ k'`: renaming the
variables, then changing the coefficients. -/
def projSpaceIsoProjectiveSpace :
    ProjSpace k (ULift.{0} (Fin (n + 1))) ≅ AlgebraicGeometry.Proj (polyGrading k' n) :=
  ProjSpace.isoPolyGrading k n ≪≫ projPolyGradingIsoOfIso φ n

/-- The isomorphism `projSpaceIsoProjectiveSpace φ n` lies over `Spec φ⁻¹ : Spec k ⟶ Spec k'`. -/
@[reassoc]
theorem projSpaceIsoProjectiveSpace_hom_toSpec :
    (projSpaceIsoProjectiveSpace φ n).hom ≫ projToSpecCoeff k' n =
      ProjSpace.toSpec k (ULift.{0} (Fin (n + 1))) ≫ Spec.map φ.inv := by
  rw [projSpaceIsoProjectiveSpace, Iso.trans_hom, Category.assoc,
    projToSpecCoeff, projPolyGradingIsoOfIso]
  dsimp only
  rw [Proj.map_toSpecZero_assoc, ProjSpace.isoPolyGrading_hom, Proj.map_toSpecZero_assoc,
    ProjSpace.toSpec, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ Subtype.ext ?_)
  have hc : (MvPolynomial.C a : MvPolynomial (Fin (n + 1)) k') ∈ polyGrading k' n 0 :=
    MvPolynomial.isHomogeneous_C _ a
  change MvPolynomial.rename ULift.up (MvPolynomial.map φ.inv.hom
    ((DirectSum.decompose (polyGrading k' n) (MvPolynomial.C a) 0 :
      MvPolynomial (Fin (n + 1)) k'))) = MvPolynomial.C (φ.inv.hom a)
  rw [DirectSum.decompose_of_mem_same _ hc, MvPolynomial.map_C, MvPolynomial.rename_C]

end ProjSpace

section Height

open IsLocalRing TopologicalSpace

variable {k : Type} [Field k] {X : Scheme.{0}}

/-- **The ideal of a smooth centre at a point has height the codimension of the component
through it.** Let `T = V(I)` be a closed subscheme of `X` smooth over a field, `z ∈ T`, and `w` the
generic point of an irreducible component of `T` through `z`. Then the ideal of `T` in `𝒪_{X,z}`
has height the codimension in `X` of the closure of `w`. -/
theorem height_ker_stalkMap_subschemeι_eq_codimension_closureSingleton (sX : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (hI : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ sX))
    {z w : I.subscheme} (hw : closure {w} ∈ irreducibleComponents I.subscheme) (hwz : w ⤳ z) :
    (RingHom.ker (I.subschemeι.stalkMap z).hom).height =
      codimension (IrreducibleCloseds.closureSingleton (I.subschemeι w)) := by
  have := hI.smooth
  have hnorm := isNormal_of_isRegular _ (isRegular_of_smooth_over_field (I.subschemeι ≫ sX))
  set ζ := I.subschemeι w with hζ
  have hsp : ζ ⤳ I.subschemeι z := hwz.map I.subschemeι.continuous
  have hdimw : ringKrullDim (I.subscheme.presheaf.stalk w) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, ← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton,
      codimension_eq_coheight,
      (Order.coheight_eq_zero (x := IrreducibleCloseds.closureSingleton w)).mpr
        fun (W : IrreducibleCloseds I.subscheme) hW ↦ hw.2 W.isIrreducible hW]
    rfl
  have hfield : IsField (I.subscheme.presheaf.stalk w) := by
    have := hnorm.stalk_isDomain w
    have : Ring.KrullDimLE 0 (I.subscheme.presheaf.stalk w) := Ring.krullDimLE_iff.2 hdimw.le
    exact Ring.KrullDimLE.isField_of_isDomain
  have hmaxw : IdealSheafData.stalk I ζ = maximalIdeal (X.presheaf.stalk ζ) := by
    rw [hζ, ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk I w]
    let := hfield.toField
    exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _
      (SurjectiveOnStalks.stalkMap_surjective I.subschemeι w))
  rw [Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
  let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have hloc := MMP.Intersection.isLocalization_stalkSpecializes hsp
  set Q := (maximalIdeal (X.presheaf.stalk ζ)).comap (X.presheaf.stalkSpecializes hsp).hom
    with hQdef
  have hJ := Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk I z
  have hprime : (IdealSheafData.stalk I (I.subschemeι z)).IsPrime := by
    have := hnorm.stalk_isDomain z
    rw [← hJ]
    exact RingHom.ker_isPrime _
  have hmap : (IdealSheafData.stalk I (I.subschemeι z)).map
      (X.presheaf.stalkSpecializes hsp).hom = maximalIdeal (X.presheaf.stalk ζ) := by
    rw [← Stacks.Chow.idealStalk_eq_map_stalkSpecializes I hsp, hmaxw]
  have hle : IdealSheafData.stalk I (I.subschemeι z) ≤ Q := by
    rw [hQdef, ← hmap]
    exact Ideal.le_comap_map
  have hQ : Q = IdealSheafData.stalk I (I.subschemeι z) := by
    rw [hQdef, ← hmap]
    exact IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (X.presheaf.stalk ζ) hprime
      (Set.disjoint_left.mpr fun a ha hb => ha (hle hb))
  have hdim := IsLocalization.AtPrime.ringKrullDim_eq_height Q (X.presheaf.stalk ζ)
  rw [ringKrullDim_stalk_eq_coheight, hQ, ← hJ] at hdim
  exact_mod_cast hdim.symm

/-- The closure in `X` of the generic point of an irreducible component of `V(I)` is a maximal
irreducible closed subset of the support of `I`. -/
theorem maximal_closureSingleton_subschemeι (I : X.IdealSheafData) {w : I.subscheme}
    (hw : closure {w} ∈ irreducibleComponents I.subscheme) :
    Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ I.support)
      (IrreducibleCloseds.closureSingleton (I.subschemeι w)) := by
  have himg : ∀ u : I.subscheme, closure {I.subschemeι u} = I.subschemeι '' closure {u} :=
    fun u ↦ by
      rw [← Set.image_singleton,
        I.subschemeι.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
          I.subschemeι.continuous]
  have hmem : ∀ u : I.subscheme, I.subschemeι u ∈ (I.support : Set X) := fun u ↦
    I.range_subschemeι ▸ ⟨u, rfl⟩
  refine ⟨closure_minimal (Set.singleton_subset_iff.2 (hmem w)) I.support.isClosed,
    fun y hy hle ↦ ?_⟩
  have hgen := y.isIrreducible.isGenericPoint_genericPoint_closure
  rw [isGenericPoint_def, y.isClosed.closure_eq] at hgen
  obtain ⟨u, hu⟩ : y.isIrreducible.genericPoint ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hy (hgen.subst (motive := fun S ↦ y.isIrreducible.genericPoint ∈ S)
      (subset_closure (Set.mem_singleton _)))
  have hyu : (y : Set X) = I.subschemeι '' closure {u} := by rw [← himg, hu, hgen]
  have hsub : closure {w} ⊆ closure {u} := fun c hc ↦ by
    have : I.subschemeι c ∈ (y : Set X) := hle (by
      change I.subschemeι c ∈ closure {I.subschemeι w}
      rw [himg]
      exact ⟨c, hc, rfl⟩)
    rw [hyu] at this
    obtain ⟨v, hv, hvc⟩ := this
    rwa [← I.subschemeι.isClosedEmbedding.injective hvc]
  have hback := hw.2 isIrreducible_singleton.closure hsub
  change (y : Set X) ⊆ closure {I.subschemeι w}
  rw [hyu, himg]
  exact Set.image_mono hback

end Height

section BlowupFibre

open MMP.UnderlyingSpace MMP.Analytic MMP.Analytic.ComplexPoints
  Stacks.AlgebraicGeometry

/-- A complex point `t` of `V` whose image lies on the closed subscheme `V(I)` at `z` lifts to a
complex point `t'` of `V(I)` at `z`, and the residue field of `V(I)` at `z` is isomorphic to `ℂ`
compatibly with `t'`. -/
theorem exists_lift_subschemeι_isIso_residueField {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (I : V.IdealSheafData) (t : ComplexPoints sV) (z : I.subscheme)
    (hz : I.subschemeι z = t.toScheme) :
    ∃ t' : Spec (.of ℂ) ⟶ I.subscheme, t' ≫ I.subschemeι = t.hom ∧
      t' (IsLocalRing.closedPoint ℂ) = z ∧
      ∃ φ : I.subscheme.residueField (t' (IsLocalRing.closedPoint ℂ)) ⟶ CommRingCat.of ℂ,
        IsIso φ ∧ Spec.map φ ≫ I.subscheme.fromSpecResidueField _ = t' := by
  let : V.Over (Spec (.of ℂ)) := ⟨sV⟩
  let : I.subscheme.Over (Spec (.of ℂ)) := ⟨I.subschemeι ≫ sV⟩
  obtain ⟨t', ht'⟩ := exists_comp_eq_of_isClosedImmersion (K := ℂ) I.subschemeι t.hom
    ⟨z, hz.trans (congrArg t.hom (Subsingleton.elim _ _))⟩
  have hz' : t' (IsLocalRing.closedPoint ℂ) = z := by
    refine I.subschemeι.isEmbedding.injective ?_
    rw [hz]
    change _ = t.hom default
    rw [← ht', Scheme.Hom.comp_apply]
    exact congrArg _ (congrArg t' (Subsingleton.elim _ _))
  have ht's : t' ≫ I.subschemeι ≫ sV = 𝟙 _ := by
    rw [← Category.assoc, ht', t.hom_comp_structure]
  exact ⟨t', ht', hz', _, isIso_descResidueField_of_isSection (I.subschemeι ≫ sV) t' ht's,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField ℂ _ t'⟩

/-- If a complex point `g` of `V` factors through the closed subscheme `V(I)` as `t'`, and the
residue field of `V(I)` at the image of `t'` is identified with `ℂ` by `φ` compatibly with `t'`,
then the fibre of the exceptional divisor at that point is the fibre of the blowup over `g`. -/
theorem isPullback_fiberι_exceptionalIdeal_subschemeι {V : Scheme.{0}} (I : V.IdealSheafData)
    {g : Spec (.of ℂ) ⟶ V} (t' : Spec (.of ℂ) ⟶ I.subscheme) (ht' : t' ≫ I.subschemeι = g)
    (φ : I.subscheme.residueField (t' (IsLocalRing.closedPoint ℂ)) ⟶ CommRingCat.of ℂ) [IsIso φ]
    (hφ : Spec.map φ ≫ I.subscheme.fromSpecResidueField _ = t') :
    IsPullback ((exceptionalSubschemeMap I).fiberι _ ≫ (exceptionalIdeal I).subschemeι)
      ((exceptionalSubschemeMap I).fiberToSpecResidueField _ ≫ Spec.map (asIso φ).inv)
      (blowUpToBase I) g := by
  have H0 := IsPullback.of_hasPullback (exceptionalSubschemeMap I)
    (I.subscheme.fromSpecResidueField (t' (IsLocalRing.closedPoint ℂ)))
  have H1 := (isPullback_blowUpToBase_comp_subschemeι_iff I _
    ((exceptionalSubschemeMap I).fiberι _)
      ((exceptionalSubschemeMap I).fiberToSpecResidueField _)).2 H0
  refine H1.of_iso' (Iso.refl _) (Iso.refl _) (asIso (Spec.map φ)) (Iso.refl _) (by simp)
    ?_ (by simp) ?_
  · simp only [Iso.refl_hom, Category.id_comp, asIso_hom, asIso_inv, Category.assoc,
      ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.comp_id]
  · rw [asIso_hom, Iso.refl_hom, Category.comp_id, ← Category.assoc, hφ, ht']

/-- **The topological fibre of a smooth blowup over a point of the centre is `ℙⁿ(ℂ)`.**
Let `b : V' ⟶ V` be the blowup of a smooth complex scheme `V` along a smooth closed subscheme
`T = V(I)`, `t ∈ V(ℂ)` a complex point lying on `T`, and `z ∈ T` its image. If the ideal of `T`
in `𝒪_{V,z}` has height `n + 1`, then the fibre `(b^an)⁻¹(t)` of the complex realization of `b`
is homeomorphic to complex projective space `ℙⁿ(ℂ)`. -/
theorem nonempty_homeomorph_preimage_analyticMap_blowUpToBase {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (I : V.IdealSheafData) (hI : MMP.Resolution.IsSmoothBlowup sV I)
    (t : ComplexPoints sV) (z : I.subscheme) (hz : I.subschemeι z = t.toScheme) (n : ℕ)
    (hn : ((n + 1 : ℕ) : ℕ∞) = (RingHom.ker (I.subschemeι.stalkMap z).hom).height) :
    Nonempty ((analyticMap (blowUpToBase I) rfl ⁻¹' {t} : Set (analyticSpace
      (blowUpToBase I ≫ sV))) ≃ₜ complexProjectiveSpace n) := by
  let : V.Over (Spec (.of ℂ)) := ⟨sV⟩
  let : I.subscheme.Over (Spec (.of ℂ)) := ⟨I.subschemeι ≫ sV⟩
  obtain ⟨t', ht', rfl, φ, hφi, hφ⟩ := exists_lift_subschemeι_isIso_residueField sV I t z hz
  obtain ⟨-, -, -, -, hfib⟩ :=
    MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sV I hI
  obtain ⟨c, hc, e, he⟩ := hfib (t' (IsLocalRing.closedPoint ℂ))
  obtain rfl : c = n + 1 := by exact_mod_cast hc.trans hn.symm
  let sF : (exceptionalSubschemeMap I).fiber (t' (IsLocalRing.closedPoint ℂ)) ⟶ Spec (.of ℂ) :=
    (exceptionalSubschemeMap I).fiberToSpecResidueField _ ≫ Spec.map (asIso φ).inv
  have H2 : IsPullback ((exceptionalSubschemeMap I).fiberι _ ≫ (exceptionalIdeal I).subschemeι)
      sF (blowUpToBase I) t.hom := isPullback_fiberι_exceptionalIdeal_subschemeι I t' ht' φ hφ
  let : ((exceptionalSubschemeMap I).fiber (t' (IsLocalRing.closedPoint ℂ))).Over
    (Spec (.of ℂ)) := ⟨sF⟩
  let : (blowUp I).Over (Spec (.of ℂ)) := ⟨blowUpToBase I ≫ sV⟩
  have : ((exceptionalSubschemeMap I).fiberι _ ≫ (exceptionalIdeal I).subschemeι).IsOver
      (Spec (.of ℂ)) := ⟨by
    change _ ≫ blowUpToBase I ≫ sV = sF
    rw [← Category.assoc, H2.w, Category.assoc, t.hom_comp_structure, Category.comp_id]⟩
  obtain ⟨hemb, hrange⟩ := isEmbedding_mapFun_of_isPullback (K := ℂ) H2
  let : (AlgebraicGeometry.Proj (ProjPolyChart.polyGrading ℂ n)).Over
      (Spec (.of ℂ)) := ⟨ProjPolyChart.projToSpecCoeff ℂ n⟩
  let Φ := e ≪≫ projSpaceIsoProjectiveSpace (@asIso _ _ _ _ φ hφi) n
  have : Φ.hom.IsOver (Spec (.of ℂ)) := ⟨by
    change (e.hom ≫ (projSpaceIsoProjectiveSpace (@asIso _ _ _ _ φ hφi) n).hom) ≫
      ProjPolyChart.projToSpecCoeff ℂ n = sF
    refine (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·)
      (projSpaceIsoProjectiveSpace_hom_toSpec (@asIso _ _ _ _ φ hφi) n)).trans
      ((Category.assoc _ _ _).symm.trans ?_))
    exact congrArg (· ≫ Spec.map (@asIso _ _ _ _ φ hφi).inv) he⟩
  let h0 : ComplexPoints (blowUpToBase I ≫ sV) ≃ₜ UnderlyingSpace ℂ (blowUp I) :=
    homeomorphUnderlyingSpace
  have hS : h0 '' (analyticMap (blowUpToBase I) rfl ⁻¹' {t}) =
      Set.range (mapFun (K := ℂ)
        ((exceptionalSubschemeMap I).fiberι (t' (IsLocalRing.closedPoint ℂ)) ≫
          (exceptionalIdeal I).subschemeι)) := by
    rw [hrange, Homeomorph.image_eq_preimage_symm]
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ congrArg ComplexPoints.hom h, fun h ↦ ComplexPoints.ext h⟩
  exact ⟨(h0.image _).trans ((Homeomorph.setCongr hS).trans (hemb.toHomeomorph.symm.trans
    ((underlyingSpaceHomeomorphOfIso Φ).trans (underlyingSpaceProjectiveSpaceHomeomorph n
      rfl))))⟩

/-- **The topological fibre of a smooth blowup along a smooth centre of pure codimension `c` is
`ℙ^{c-1}(ℂ)`.** Let `b : V' ⟶ V` be the blowup of a smooth complex scheme `V` along a smooth
closed subscheme `T = V(I)` every maximal irreducible closed subset of which has codimension
`c ≥ 1` in `V`; `T` need not be connected. For every complex point `t` of `V` lying on `T`, the
fibre `(b^an)⁻¹(t)` is homeomorphic to `ℙ^{c-1}(ℂ)`. -/
theorem nonempty_homeomorph_preimage_analyticMap_blowUpToBase_of_codimension {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (I : V.IdealSheafData) (hI : MMP.Resolution.IsSmoothBlowup sV I)
    (c : ℕ) (hc : 1 ≤ c)
    (hcodim : ∀ Z : TopologicalSpace.IrreducibleCloseds V,
      Maximal (fun W : TopologicalSpace.IrreducibleCloseds V ↦ (W : Set V) ⊆ I.support) Z →
        codimension Z = c)
    (t : ComplexPoints sV) (ht : t.toScheme ∈ I.support) :
    Nonempty ((analyticMap (blowUpToBase I) rfl ⁻¹' {t} : Set (analyticSpace
      (blowUpToBase I ≫ sV))) ≃ₜ complexProjectiveSpace (c - 1)) := by
  obtain ⟨z, hz⟩ : t.toScheme ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact ht
  obtain ⟨C, hC, hzC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {z}
    isIrreducible_singleton
  have hgen := hC.1.isGenericPoint_genericPoint_closure
  rw [isGenericPoint_def, (isClosed_of_mem_irreducibleComponents C hC).closure_eq] at hgen
  have hwz : hC.1.genericPoint ⤳ z := by
    rw [specializes_iff_mem_closure, hgen]
    exact hzC rfl
  refine nonempty_homeomorph_preimage_analyticMap_blowUpToBase sV I hI t z hz (c - 1) ?_
  rw [Nat.sub_add_cancel hc,
    height_ker_stalkMap_subschemeι_eq_codimension_closureSingleton sV I hI.2 (by rwa [hgen]) hwz,
    hcodim _ (maximal_closureSingleton_subschemeι I (by rwa [hgen]))]

/-- **The topological fibre of a smooth blowup along an irreducible centre of codimension `c`
is `ℙ^{c-1}(ℂ)`.** Let `b : V' ⟶ V` be the blowup of a smooth complex scheme `V` along a smooth
irreducible closed subscheme `T = V(I)` of codimension `c ≥ 1`. For every complex point `t` of
`V` lying on `T`, the fibre `(b^an)⁻¹(t)` is homeomorphic to `ℙ^{c-1}(ℂ)`. -/
theorem nonempty_homeomorph_preimage_analyticMap_blowUpToBase_of_isIrreducible {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (I : V.IdealSheafData) (hI : MMP.Resolution.IsSmoothBlowup sV I)
    (hirr : IsIrreducible (I.support : Set V)) (c : ℕ) (hc : 1 ≤ c)
    (hcodim : codimension
      (⟨I.support, hirr, I.support.isClosed⟩ : TopologicalSpace.IrreducibleCloseds V) = c)
    (t : ComplexPoints sV) (ht : t.toScheme ∈ I.support) :
    Nonempty ((analyticMap (blowUpToBase I) rfl ⁻¹' {t} : Set (analyticSpace
      (blowUpToBase I ≫ sV))) ≃ₜ complexProjectiveSpace (c - 1)) :=
  nonempty_homeomorph_preimage_analyticMap_blowUpToBase_of_codimension sV I hI c hc
    (fun Z hZ ↦ by
      rw [show Z = ⟨I.support, hirr, I.support.isClosed⟩ from
        le_antisymm hZ.1 (hZ.2 (y := ⟨I.support, hirr, I.support.isClosed⟩) subset_rfl hZ.1),
        hcodim]) t ht

end BlowupFibre

end MMP.Topology
