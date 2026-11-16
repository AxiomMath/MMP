module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationSteps
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.AssemblyGeneric
public import MMP.AlgebraicGeometry.CycleMap.RefinedGysin.Family
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksHomotopyInfra
public import MMP.AlgebraicGeometry.Chow.CycleClassDescent

/-!
# The specialization step of Fulton's Theorem 19.2, from its four inputs

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes with
orientation class `u`, `g : Y' ⟶ Y`, `X' = X ×_Y Y'` and `α ∈ A_{m+d}(Y')`. This file proves the
specialization step `MMP.Chow.SpecializationFormula` at `α`,
`u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α) = g^* u ∩ cl(α)`, from the four inputs of
`MMP.Chow.SpecializationAtZero`, `MMP.Chow.SpecializationAtInfinity`,
`MMP.Chow.OrientationAtZero` and `MMP.Chow.ConeThomAtInfinity`
(`MMP.Chow.specializationFormula_of_steps`).

The proof is Fulton's: on Stacks' deformation space on the test scheme, `ρ' : W' = W ×_Y Y' ⟶ 𝐏¹`,
with the trivial family `e : X' × 𝐏¹ ⟶ W'`, `w = G^* u_x` for an orientation class `u_x` of the
trivial family `e_W : X × 𝐏¹ ⟶ W` and `a = cl(β)` for a lift `β` of `α` (Stacks 0F9J), the family
chain `w|_{ρ'⁻¹ 0} ∩ (ρ'^* u_0 ∩ a) = w|_{ρ'⁻¹ ∞} ∩ (ρ'^* u_∞ ∩ a)`
(`UnderlyingSpace.pushforward_interFibre_capProductSupportPullback_eq_of_stacksOrientationClass`)
is read at `0` as `g^* u ∩ cl(α)` (the specialization and the orientation class at zero) and at `∞`
as `u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α)` (the specialization at infinity and the cone).

## Main results

* `MMP.borelMooreHomology.pushforward_interFibre_capProductSupportPullback_forget_pullback_eq`:
  one side of the family chain, read as a cap product on `W` (or `C'`) along `κ`.
* `MMP.Chow.specializationFormula_of_steps`

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology Stacks.Chow
open MMP.UnderlyingSpace MMP.borelMooreHomology
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open MMP.Modules

namespace MMP.borelMooreHomology

open BorelMooreCross

section InterFibre

universe u

variable (R : Type u) [CommRing R]

variable {X T M N W : TopCat.{u}} {ρ : M ⟶ T} {A : Set M} (φ : (X × T) ≃ₜ A)
  (hφ : ∀ p, ρ (φ p : M) = p.2)

/-- `incl ≫ ρ' ≫ (A ∩ ρ⁻¹ t → X) = q` on `h⁻¹ D`, for `ρ' : (κ ≫ incl)⁻¹ A → incl⁻¹ A` the
restriction of `κ`. -/
lemma comp_interFibreProj_eq {t : T} (κ : W ⟶ TopCat.of (ρ ⁻¹' {t})) {S : Set W}
    (hS : S ⊆ (κ ≫ subsetInclusion _) ⁻¹' A) (q : TopCat.of S ⟶ X)
    (hq : ∀ z, (φ (q z, t) : M) = (κ ≫ subsetInclusion _) z.1) :
    subsetInclusionOfSubset hS ≫
        TopCat.ofHom (κ.hom.restrictPreimage (subsetInclusion (ρ ⁻¹' {t}) ⁻¹' A)) ≫
          (preimageInterHom (ρ ⁻¹' {t}) A ≫ subsetInclusionOfSubset (inter_comm _ A).le) ≫
            interFibreProj φ hφ t = q := by
  ext z
  change (φ.symm ⟨(κ z.1).1, _⟩).1 = q z
  have h : (⟨(κ z.1).1, hS z.2⟩ : A) = φ (q z, t) := Subtype.ext (hq z).symm
  rw [h, φ.symm_apply_apply]

/-- **One end of the family chain** (Fulton, proof of Theorem 19.2). Let `ρ : M → T`, `A ⊆ M`
closed with a homeomorphism `φ : X × T ≃ A` over `T`, `g : M → N`, `D ⊆ N` closed with
`g⁻¹ D ⊆ A`, `v ∈ H^i(N, N - D)` and `w = (g^* v)|_A`. For a proper `κ : W → ρ⁻¹ t`,
`F = κ` as a map to `M`, `h = g ∘ F`, `c ∈ H_l W` and `b = κ_* c`: the class
`w|_{ρ⁻¹ t} ∩ b`, read in `H_*(X)` along `A ∩ ρ⁻¹ t ≅ X`, is `q_* (h^* v ∩ c)` for any proper
`q : h⁻¹ D → X` with `φ (q z, t) = F z`. -/
theorem pushforward_interFibre_capProductSupportPullback_forget_pullback_eq [T1Space T] (t : T)
    (hA : IsClosed A) (hd₁ : HasProperNeighbourhoodDeformations (subsetInclusion (ρ ⁻¹' {t}) ⁻¹' A))
    (κ : W ⟶ TopCat.of (ρ ⁻¹' {t})) (hκ : IsProperMap κ) (F : W ⟶ M)
    (hF : κ ≫ subsetInclusion _ = F) (hdF : HasProperNeighbourhoodDeformations (F ⁻¹' A))
    (g : M ⟶ N) {D : Set N} (hD : IsClosed D) (hDA : g ⁻¹' D ⊆ A) (h : W ⟶ N) (hh : F ≫ g = h)
    (hdh : HasProperNeighbourhoodDeformations (h ⁻¹' D))
    (q : TopCat.of (h ⁻¹' D) ⟶ X) (hq : ∀ z, (φ (q z, t) : M) = F z.1) (hqp : IsProperMap q)
    {i l k : ℤ} (e : l = k) (v : cohomologyWithSupports R (ModuleCat.of R R) N D i)
    (c : borelMooreHomology R (ModuleCat.of R R) W l)
    (b : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (ρ ⁻¹' {t})) k)
    (hb : b = congrDegree R _ e ((pushforward R (ModuleCat.of R R) κ hκ l).hom c)) :
    (pushforward R (ModuleCat.of R R)
        ((preimageInterHom (ρ ⁻¹' {t}) A ≫ subsetInclusionOfSubset (inter_comm _ A).le) ≫
          interFibreProj φ hφ t)
        ((isProperMap_interFibreProj φ hφ t).comp
          ((isProperMap_subsetInclusionOfSubset
            ((isClosed_singleton.preimage ρ.hom.continuous).inter hA) (inter_comm _ A).le).comp
            (isProperMap_preimageInterHom (isClosed_singleton.preimage ρ.hom.continuous) hA)))
        (k - i)).hom
      (capProductSupportPullback R (subsetInclusion (ρ ⁻¹' {t})) hA hd₁ i k
        ((cohomologyWithSupports.forget R (ModuleCat.of R R) M hDA i).hom
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g D i).hom v)) b) =
      congrDegree R X (by rw [e])
        ((pushforward R (ModuleCat.of R R) q hqp (l - i)).hom
          (capProductSupportPullback R h hD hdh i l v c)) := by
  subst e
  subst hb
  subst hF
  subst hh
  have hZ : IsClosed (ρ ⁻¹' {t}) := isClosed_singleton.preimage ρ.hom.continuous
  have hS : ((κ ≫ subsetInclusion _) ≫ g) ⁻¹' D ⊆ (κ ≫ subsetInclusion _) ⁻¹' A :=
    preimage_mono hDA
  have hSc : IsClosed (((κ ≫ subsetInclusion _) ≫ g) ⁻¹' D) :=
    hD.preimage ((κ ≫ subsetInclusion _) ≫ g).hom.continuous
  have hp₁ : IsProperMap (preimageInterHom (ρ ⁻¹' {t}) A ≫
      subsetInclusionOfSubset (inter_comm (ρ ⁻¹' {t}) A).le) :=
    (isProperMap_subsetInclusionOfSubset (hZ.inter hA) (inter_comm _ A).le).comp
      (isProperMap_preimageInterHom hZ hA)
  have hP : IsProperMap ((preimageInterHom (ρ ⁻¹' {t}) A ≫
      subsetInclusionOfSubset (inter_comm (ρ ⁻¹' {t}) A).le) ≫ interFibreProj φ hφ t) :=
    (isProperMap_interFibreProj φ hφ t).comp hp₁
  have hP' : IsProperMap (TopCat.ofHom (κ.hom.restrictPreimage
      (subsetInclusion (ρ ⁻¹' {t}) ⁻¹' A)) ≫ (preimageInterHom (ρ ⁻¹' {t}) A ≫
      subsetInclusionOfSubset (inter_comm (ρ ⁻¹' {t}) A).le) ≫ interFibreProj φ hφ t) :=
    hP.comp (hκ.restrictPreimage _)
  rw [congrDegree_self, LinearEquiv.refl_apply, congrDegree_self, LinearEquiv.refl_apply,
    ← pushforward_restrictPreimage_capProductSupportPullback_comp R κ hκ _ hA hd₁ hdF,
    ← pushforward_comp_apply' R _ _ (hκ.restrictPreimage _) hP,
    capProductSupportPullback_apply, cohomologyWithSupports.pullback_forget_apply,
    ← pushforward_subsetInclusionOfSubset_capProductSupport R W hSc
      (hA.preimage (κ ≫ subsetInclusion _).hom.continuous) hdh hdF hS,
    ← pushforward_comp_apply' R _ _ (isProperMap_subsetInclusionOfSubset hSc hS) hP',
    pushforward_congr_eq R (comp_interFibreProj_eq φ hφ κ hS q hq) _ hqp,
    capProductSupportPullback_apply,
    cohomologyWithSupports.pullback_comp R _ (κ ≫ subsetInclusion _) g D i]
  rfl

end InterFibre

end MMP.borelMooreHomology

namespace MMP.Chow

attribute [local instance low] fibreProductOver
attribute [local instance] isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct testDeformationSpaceOver blowupAtInfinityOver
  testInfinityFibreOver isLocallyNoetherian_of_isComplexScheme
  isFiniteLocallyFreeOfRank_normalBundleOfRegular isQuasicoherent_fibreNormalModule
  isFiniteLocallyFreeOfRank_fibreNormalModule isComplexScheme_totalSpace_fibreNormalModule

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ}

omit [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [f.IsOver (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- `σ' ∘ G = σ ∘ g` on `ℂ`-points, for the sections at zero `σ' : Y' ⟶ W'`, `σ : Y ⟶ W`. -/
theorem ofHom_map_testZeroSection_comp :
    haveI := isOver_testZeroSection f g
    haveI := isOver_testDeformationSpace_fst f g
    haveI := isOver_blowupZeroSection (Y := Y) f.ker
    TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testZeroSection f g)) ≫
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)) =
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g) ≫
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker)) :
          TopCat.of (UnderlyingSpace ℂ Y') ⟶
            TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker))) := by
  ext z : 1
  refine UnderlyingSpace.ext ?_
  change (z.toHom ≫ testZeroSection f g) ≫ pullback.fst _ g =
    (z.toHom ≫ g) ≫ blowupZeroSection f.ker
  rw [Category.assoc, testZeroSection_fst, Category.assoc]

omit [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [IsClosedImmersion f] in
/-- `σ' ∘ G = σ ∘ g` lands in `e_W(X × 𝐏¹)` only over `g⁻¹(X(ℂ))`. -/
theorem preimage_range_lineFamily_subset_preimage_range :
    haveI := isOver_blowupZeroSection (Y := Y) f.ker
    haveI := isOver_lineFamily f
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g) ≫
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker)) :
          TopCat.of (UnderlyingSpace ℂ Y') ⟶
            TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker))) ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (lineFamily f)) ⊆
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g) :
        TopCat.of (UnderlyingSpace ℂ Y') ⟶ TopCat.of (UnderlyingSpace ℂ Y)) ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f) :=
  fun _ hz ↦ preimage_range_lineFamily_subset_range f hz

omit [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
/-- On `ℂ`-points, `e(x', t)` lies over `x' ↦ Y'`: the trivial family followed by `W' ⟶ Y'` is
`X' × 𝐏¹ ⟶ X' ⟶ Y'`. -/
theorem map_snd_trivialFamilyHomeomorph
    (p : UnderlyingSpace ℂ (pullback f g) ×
      UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))) :
    haveI := isOver_testTrivialFamily f g
    haveI := isOver_testDeformationSpace_snd f g
    UnderlyingSpace.map (K := ℂ) (pullback.snd (modificationProjection (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))) g)
        (trivialFamilyHomeomorph (testTrivialFamily f g) p :
          UnderlyingSpace ℂ (testDeformationSpace f g)) =
      UnderlyingSpace.map (K := ℂ) (pullback.snd f g) p.1 := by
  have := isOver_testTrivialFamily f g
  have := isOver_testDeformationSpace_snd f g
  rw [coe_trivialFamilyHomeomorph]
  refine UnderlyingSpace.ext ?_
  have h1 : testTrivialFamily f g ≫ pullback.snd _ g =
      pullback.fst (pullback f g ↘ Spec (.of ℂ))
        (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ)) ≫ pullback.snd f g := by
    rw [testTrivialFamily, Category.assoc, testLineMap_snd, ← Category.assoc]
    exact congrArg (· ≫ pullback.snd f g) (by
      rw [Iso.inv_comp_eq, relativeProjectiveLineIsoProjectiveLineProduct_hom_fst])
  have h2 := congrArg Prod.fst ((homeomorphProd (pullback f g)
    (relativeProjectiveLine (Spec (.of ℂ)))).apply_symm_apply p)
  rw [homeomorphProd_apply] at h2
  change (_ ≫ testTrivialFamily f g) ≫ pullback.snd _ g = p.1.toHom ≫ pullback.snd f g
  rw [Category.assoc, h1, ← Category.assoc, ← h2]
  rfl

variable (R : Type) [CommRing R]

/-- The class `w = G^* u_x ∈ H^{2d}(W', W' - e(X' × 𝐏¹))` of the family chain, for an orientation
class `u_x` of the trivial family `e_W : X × 𝐏¹ ⟶ W` and `G : W' ⟶ W`. -/
abbrev testFamilyClass
    (ux : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker)))
      (haveI := isOver_lineFamily f; range (UnderlyingSpace.map (K := ℂ) (lineFamily f)))
      (2 * d : ℕ)) :
    haveI := isOver_testTrivialFamily f g
    cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)))
      (range (UnderlyingSpace.map (K := ℂ) (testTrivialFamily f g))) (2 * d : ℕ) :=
  haveI := isOver_testDeformationSpace_fst f g
  haveI := isOver_lineFamily f
  haveI := isOver_testTrivialFamily f g
  (cohomologyWithSupports.forget R (ModuleCat.of R R) _ (preimage_range_lineFamily_subset f g)
      _).hom
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g))) _ _).hom ux)

omit [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
    [LocallyOfFiniteType g] in
omit [Y'.Over (Spec (.of ℂ))] in
/-- `A ∩ ρ'⁻¹(t) ⟶ X'(ℂ)`, `A = e(X' × 𝐏¹)`, is proper. -/
theorem isProperMap_testInterFibreProj
    (t : UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))) :
    haveI := isOver_testTrivialFamily f g
    haveI := isOver_testDeformationToLine f g
    IsProperMap ((preimageInterHom ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
            (testDeformationToLine f g)) :
          TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)) ⟶
            TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ))))) ⁻¹' {t})
            (range (UnderlyingSpace.map (K := ℂ) (testTrivialFamily f g))) ≫
          subsetInclusionOfSubset (inter_comm _ _).le) ≫
          interFibreProj (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
            (T := TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))))
            (Y := TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)))
            (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
            (trivialFamilyHomeomorph (testTrivialFamily f g))
            (map_trivialFamilyHomeomorph _ _
              (testTrivialFamily_comp_testDeformationToLine f g)) t) := by
  have := isOver_testTrivialFamily f g
  have := isOver_testDeformationToLine f g
  have hZ : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)) :
      TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)) ⟶
        TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ))))) ⁻¹' {t}) :=
    isClosed_singleton.preimage (ContinuousMap.continuous _)
  have hA := (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (testTrivialFamily f g)).isClosed_range
  exact (isProperMap_interFibreProj (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
      (T := TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))))
      (Y := TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)))
      (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
      (trivialFamilyHomeomorph (testTrivialFamily f g))
      (map_trivialFamilyHomeomorph _ _ (testTrivialFamily_comp_testDeformationToLine f g)) t).comp
    ((isProperMap_subsetInclusionOfSubset (hZ.inter hA) (inter_comm _ _).le).comp
      (isProperMap_preimageInterHom hZ hA))

omit [IsComplexScheme X] [LocallyOfFiniteType g] in
/-- **One end of the family chain on the test scheme.** For a closed immersion
`σ : Z ⟶ W'` into the fibre of `ρ'` at `t` and `h = G ∘ σ` on `ℂ`-points, the class
`w|_{ρ'⁻¹ t} ∩ σ_* c`, read in `H_*(X')`, is `h^* u_x ∩ c` read in `H_*(X')` along
`h⁻¹(e_W(X × 𝐏¹)) ⟶ X'(ℂ)` (`MMP.borelMooreHomology.familyFibreProj`). -/
theorem pushforward_interFibre_testFamilyClass_eq {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] (σ : Z ⟶ testDeformationSpace f g) [IsClosedImmersion σ]
    [σ.IsOver (Spec (.of ℂ))] (t : UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ))))
    (hσ : σ ≫ testDeformationToLine f g = Z ↘ Spec (.of ℂ) ≫ t.toHom)
    (h : TopCat.of (UnderlyingSpace ℂ Z) ⟶ TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker)))
    (hh : haveI := isOver_testDeformationSpace_fst f g
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ) ≫
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)) = h)
    (hdh : haveI := isOver_lineFamily f
      HasProperNeighbourhoodDeformations
        (h ⁻¹' range (UnderlyingSpace.map (K := ℂ) (lineFamily f))))
    (ux : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker)))
      (haveI := isOver_lineFamily f; range (UnderlyingSpace.map (K := ℂ) (lineFamily f)))
      (2 * d : ℕ))
    {l k : ℤ} (e : l = k) (c : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ Z)) l)
    (b : haveI := isOver_testDeformationToLine f g
      borelMooreHomology R (ModuleCat.of R R)
        (TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)) :
          TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)) ⟶
            TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ))))) ⁻¹' {t})) k)
    (hb : haveI := isOver_testDeformationToLine f g
      b = BorelMooreCross.congrDegree R _ e
        ((borelMooreHomology.pushforward R (ModuleCat.of R R)
          (fibrePointsHom σ (testDeformationToLine f g) t hσ)
          (isProperMap_fibrePointsHom _ _ _ _) l).hom c)) :
    haveI := isComplexScheme_testDeformationSpace f g
    haveI := isComplexScheme_blowupAtInfinity (X := Y) f.ker
    haveI := isOver_testTrivialFamily f g
    haveI := isOver_testDeformationToLine f g
    haveI := isOver_testDeformationSpace_fst f g
    haveI := isOver_lineFamily f
    (borelMooreHomology.pushforward R (ModuleCat.of R R)
        ((preimageInterHom ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
            (testDeformationToLine f g)) :
          TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)) ⟶
            TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ))))) ⁻¹' {t})
            (range (UnderlyingSpace.map (K := ℂ) (testTrivialFamily f g))) ≫
          subsetInclusionOfSubset (inter_comm _ _).le) ≫
          interFibreProj (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
            (T := TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))))
            (Y := TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)))
            (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
            (trivialFamilyHomeomorph (testTrivialFamily f g))
            (map_trivialFamilyHomeomorph _ _ (testTrivialFamily_comp_testDeformationToLine f g)) t)
        (isProperMap_testInterFibreProj f g t)
        (k - (2 * d : ℕ))).hom
      (capProductSupportPullback R (subsetInclusion (Y := TopCat.of (UnderlyingSpace ℂ
          (testDeformationSpace f g))) ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
            (testDeformationToLine f g)) :
          TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)) ⟶
            TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ))))) ⁻¹' {t}))
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (testTrivialFamily f g)).isClosed_range
        ((UnderlyingSpace.hasProperNeighbourhoodDeformations_trivialFamily (testTrivialFamily f g)
          (testDeformationToLine f g)).2.2.2.1 t)
        (2 * d : ℕ) k (testFamilyClass f g R ux) b) =
      BorelMooreCross.congrDegree R _ (by rw [e])
        ((borelMooreHomology.pushforward R (ModuleCat.of R R)
          (familyFibreProj (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
            (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
            (trivialFamilyHomeomorph (testTrivialFamily f g))
            (map_trivialFamilyHomeomorph _ _ (testTrivialFamily_comp_testDeformationToLine f g)) t
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
            (map_mem_preimage_singleton σ (testDeformationToLine f g) t hσ)
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
            (preimage_range_lineFamily_subset f g) h hh)
          (isProperMap_familyFibreProj _ _ _ _
            (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) σ) _ _
            (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range
            _ _ _) (l - (2 * d : ℕ))).hom
          (capProductSupportPullback R h
            (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range hdh
            (2 * d : ℕ) l ux c)) := by
  have := isComplexScheme_testDeformationSpace f g
  have := isComplexScheme_blowupAtInfinity (X := Y) f.ker
  have := isOver_testTrivialFamily f g
  have := isOver_testDeformationToLine f g
  have := isOver_testDeformationSpace_fst f g
  have := isOver_lineFamily f
  have hφ := map_trivialFamilyHomeomorph _ _ (testTrivialFamily_comp_testDeformationToLine f g)
  have hFt := map_mem_preimage_singleton σ (testDeformationToLine f g) t hσ
  have hq := familyFibreProj_spec (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
    (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
    (trivialFamilyHomeomorph (testTrivialFamily f g)) hφ t
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)) hFt
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
    (preimage_range_lineFamily_subset f g) h hh
  have hqp := isProperMap_familyFibreProj (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
    (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
    (trivialFamilyHomeomorph (testTrivialFamily f g)) hφ t
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) σ) hFt
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range
    (preimage_range_lineFamily_subset f g) h hh
  exact pushforward_interFibre_capProductSupportPullback_forget_pullback_eq R
    (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
    (T := TopCat.of (UnderlyingSpace ℂ (relativeProjectiveLine (Spec (.of ℂ)))))
    (M := TopCat.of (UnderlyingSpace ℂ (testDeformationSpace f g)))
    (N := TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker)))
    (W := TopCat.of (UnderlyingSpace ℂ Z))
    (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
    (trivialFamilyHomeomorph (testTrivialFamily f g)) hφ t
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (testTrivialFamily f g)).isClosed_range
    ((UnderlyingSpace.hasProperNeighbourhoodDeformations_trivialFamily (testTrivialFamily f g)
      (testDeformationToLine f g)).2.2.2.1 t)
    (fibrePointsHom σ (testDeformationToLine f g) t hσ) (isProperMap_fibrePointsHom _ _ _ _)
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ)) (fibrePointsHom_comp_subsetInclusion _ _ _ _)
    (hasProperNeighbourhoodDeformations_preimage_range_map _ σ)
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range
    (preimage_range_lineFamily_subset f g) h hh hdh _ hq hqp e ux c b hb

omit [IsComplexScheme X] [LocallyOfFiniteType g] in
/-- The map `Y' ⟶ Y ⟶ W` through the section at zero has proper neighbourhood deformations
around the inverse image of the trivial family. -/
theorem hasProperNeighbourhoodDeformations_testZeroMap :
    haveI := isOver_blowupZeroSection (Y := Y) f.ker
    haveI := isOver_lineFamily f
    HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g) ≫
        TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker)) :
          TopCat.of (UnderlyingSpace ℂ Y') ⟶
            TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker))) ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) (lineFamily f))) := by
  have := isOver_blowupZeroSection (Y := Y) f.ker
  have := isOver_lineFamily f
  have hc : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g) ≫
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker)) :
        TopCat.of (UnderlyingSpace ℂ Y') ⟶
          TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker))) =
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (g ≫ blowupZeroSection f.ker)) := by
    ext z : 1
    exact UnderlyingSpace.ext (Category.assoc _ _ _)
  rw [hc]
  have := isComplexScheme_blowupAtInfinity (X := Y) f.ker
  exact hasProperNeighbourhoodDeformations_preimage_range_map (lineFamily f)
    (g ≫ blowupZeroSection f.ker)

omit [IsComplexScheme X] [LocallyOfFiniteType g] in
/-- **The end at zero is `g^* u ∩ -`.** For an orientation class `u_x` of the trivial family and
the orientation class `u` of `f`, with `σ^* u_x = u` (`MMP.Chow.OrientationAtZero`): the class
`h^* u_x ∩ a` for `h : Y' ⟶ Y ⟶ W` through the section at zero, read in `H_*(X')` along the end
map of the family chain and then in `H_*(g⁻¹(X(ℂ)))` along `X'(ℂ) ≅ g⁻¹(X(ℂ))`, is
`g^* u ∩ a`. -/
theorem pushforward_fibreSquarePointsHom_testZeroEnd (hf : IsRegularClosedImmersionOfCodim f d)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * d : ℕ))
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R f d u)
    (hO0 : OrientationAtZero f R hf u)
    (ux : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker)))
      (haveI := isOver_lineFamily f; range (UnderlyingSpace.map (K := ℂ) (lineFamily f)))
      (2 * d : ℕ))
    (hux : haveI := isOver_lineFamily f
      MMP.Modules.IsRegularImbeddingOrientationClass R (lineFamily f) d ux)
    {l : ℤ} (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y')) l) :
    haveI := isComplexScheme_testDeformationSpace f g
    haveI := isOver_testTrivialFamily f g
    haveI := isOver_testDeformationToLine f g
    haveI := isOver_testZeroSection f g
    haveI := isClosedImmersion_testZeroSection f g
    haveI := isOver_testDeformationSpace_fst f g
    haveI := isOver_lineFamily f
    haveI := isOver_blowupZeroSection (Y := Y) f.ker
    (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (fibreSquarePointsHom (IsPullback.of_hasPullback f g).flip)
        (isProperMap_fibreSquarePointsHom (IsPullback.of_hasPullback f g).flip)
        (l - (2 * d : ℕ))).hom
      ((borelMooreHomology.pushforward R (ModuleCat.of R R)
        (familyFibreProj (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
          (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
          (trivialFamilyHomeomorph (testTrivialFamily f g))
          (map_trivialFamilyHomeomorph _ _ (testTrivialFamily_comp_testDeformationToLine f g))
          lineZeroComplexPoint (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testZeroSection f g)))
          (map_mem_preimage_singleton _ _ _ (testZeroSection_comp_testDeformationToLine f g))
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
          (preimage_range_lineFamily_subset f g) _ (ofHom_map_testZeroSection_comp f g))
        (isProperMap_familyFibreProj _ _ _ _
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (testZeroSection f g)) _ _
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range
          _ _ _) (l - (2 * d : ℕ))).hom
        (capProductSupportPullback R
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g) ≫
            TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker)))
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range
          (hasProperNeighbourhoodDeformations_testZeroMap f g) (2 * d : ℕ) l ux a)) =
      capProductSupportPullback R (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g))
        (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
        (hasProperNeighbourhoodDeformations_preimage_range_map f g) (2 * d : ℕ) l u a := by
  have := isComplexScheme_testDeformationSpace f g
  have := isOver_testTrivialFamily f g
  have := isOver_testDeformationToLine f g
  have := isOver_testZeroSection f g
  have := isClosedImmersion_testZeroSection f g
  have := isOver_testDeformationSpace_fst f g
  have := isOver_lineFamily f
  have := isOver_blowupZeroSection (Y := Y) f.ker
  have he := testTrivialFamily_comp_testDeformationToLine f g
  have hS₀ := preimage_range_lineFamily_subset_preimage_range f g
  have hv : (cohomologyWithSupports.forget R (ModuleCat.of R R) _ hS₀ _).hom
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g) ≫
          TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker))) _ _).hom ux) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g)) _ _).hom u := by
    rw [← hO0 ux hux hu, cohomologyWithSupports.pullback_forget_apply,
      cohomologyWithSupports.pullback_comp]
    rfl
  have T1 := capProductSupportPullback_eq_pushforward_of_forget_eq R
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g) ≫
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker)))
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g))
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
    (hasProperNeighbourhoodDeformations_testZeroMap f g)
    (hasProperNeighbourhoodDeformations_preimage_range_map f g) hS₀ hv l a
  have hD₀ : IsClosed ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g) ≫
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowupZeroSection f.ker)) :
        TopCat.of (UnderlyingSpace ℂ Y') ⟶
          TopCat.of (UnderlyingSpace ℂ (blowupAtInfinity f.ker))) ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) (lineFamily f))) :=
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (lineFamily f)).isClosed_range.preimage
      (ContinuousMap.continuous _)
  have hFt0 := map_mem_preimage_singleton (testZeroSection f g) (testDeformationToLine f g)
    lineZeroComplexPoint (testZeroSection_comp_testDeformationToLine f g)
  have hc₀ : familyFibreProj (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
      (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
      (trivialFamilyHomeomorph (testTrivialFamily f g)) (map_trivialFamilyHomeomorph _ _ he)
      lineZeroComplexPoint (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testZeroSection f g)))
      hFt0 (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
      (preimage_range_lineFamily_subset f g) _ (ofHom_map_testZeroSection_comp f g) ≫
        fibreSquarePointsHom (IsPullback.of_hasPullback f g).flip =
      subsetInclusionOfSubset hS₀ := by
    ext z : 1
    refine Subtype.ext ?_
    have hspec := familyFibreProj_spec (X := TopCat.of (UnderlyingSpace ℂ (pullback f g)))
      (ρ := TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testDeformationToLine f g)))
      (trivialFamilyHomeomorph (testTrivialFamily f g)) (map_trivialFamilyHomeomorph _ _ he)
      lineZeroComplexPoint (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (testZeroSection f g)))
      hFt0 (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (pullback.fst _ g)))
      (preimage_range_lineFamily_subset f g) _ (ofHom_map_testZeroSection_comp f g) z
    have := isOver_testDeformationSpace_snd f g
    have h2 := congrArg (UnderlyingSpace.map (K := ℂ) (pullback.snd (modificationProjection
      (Y ↘ Spec (.of ℂ)) (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))) g))
      hspec
    rw [map_snd_trivialFamilyHomeomorph] at h2
    refine h2.trans (UnderlyingSpace.ext ?_)
    change (z.1.toHom ≫ testZeroSection f g) ≫ pullback.snd _ g = z.1.toHom
    rw [Category.assoc, testZeroSection_snd, Category.comp_id]
  rw [T1, ← pushforward_comp_apply' R _ _ _
      (isProperMap_fibreSquarePointsHom (IsPullback.of_hasPullback f g).flip),
    pushforward_congr_eq R hc₀ _ (isProperMap_subsetInclusionOfSubset hD₀ hS₀)]

/-- **The specialization step of Fulton's Theorem 19.2, from its four inputs.** For a regular
closed immersion `f : X ⟶ Y` of codimension `d` with orientation class `u`, `g : Y' ⟶ Y` and
`α ∈ A_{m+d}(Y')`: if the specializations at `0` and `∞`
(`MMP.Chow.SpecializationAtZero`, `MMP.Chow.SpecializationAtInfinity`), the orientation class at
zero (`MMP.Chow.OrientationAtZero`) and the cone at infinity (`MMP.Chow.ConeThomAtInfinity`) hold,
then so does the specialization step `u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α) = g^* u ∩ cl(α)`. -/
theorem specializationFormula_of_steps (hf : IsRegularClosedImmersionOfCodim f d)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * d : ℕ)) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ))
    (h0 : SpecializationAtZero f g R m α) (hinf : SpecializationAtInfinity f g R m α)
    (hO0 : OrientationAtZero f R hf u) (hOinf : ConeThomAtInfinity f g R hf m α) :
    SpecializationFormula f g R hf u m α := by
  intro hu
  have := isComplexScheme_testDeformationSpace f g
  have := isComplexScheme_testInfinityFibre f g
  have := isComplexScheme_blowupAtInfinity (X := Y) f.ker
  have := isOver_testTrivialFamily f g
  have := isOver_testDeformationToLine f g
  have := isOver_testZeroSection f g
  have := isClosedImmersion_testZeroSection f g
  have := isOver_testInfinityInclusion f g
  have := isOver_testDeformationSpace_fst f g
  have := isOver_lineFamily f
  have := isOver_blowupZeroSection (Y := Y) f.ker
  obtain ⟨β, hβ⟩ : ∃ β : chowGroup (fieldChowSituation ℂ)
      (testDeformationSpace f g ↘ Spec (.of ℂ)) ((m + d + 1 : ℕ) : ℤ),
      IsModificationLift (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
        (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
        ((m + d : ℕ) : ℤ)
        (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
          (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α) β :=
    exists_isModificationLift (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
      ((m + d : ℕ) : ℤ) _
  have hT := smoothOfRelativeDimension_relativeProjectiveLine ℂ
  obtain ⟨u₀, hu₀⟩ := MMP.Modules.exists_isRegularImbeddingOrientationClass R
    (isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hT lineZeroComplexPoint)
  obtain ⟨u₁, hu₁⟩ := MMP.Modules.exists_isRegularImbeddingOrientationClass R
    (isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hT lineInfinityComplexPoint)
  obtain ⟨ux, hux⟩ := MMP.Modules.exists_isRegularImbeddingOrientationClass R
    (isRegularClosedImmersionOfCodim_lineFamily f hf)
  have he := testTrivialFamily_comp_testDeformationToLine f g
  obtain ⟨hAd, hZd, hAZd, hd₁, hd₂⟩ :=
    UnderlyingSpace.hasProperNeighbourhoodDeformations_trivialFamily (testTrivialFamily f g)
      (testDeformationToLine f g)
  have key :=
    UnderlyingSpace.pushforward_interFibre_capProductSupportPullback_eq_of_stacksOrientationClass
      (testTrivialFamily f g) hT R (testDeformationToLine f g) he hAd hZd hAZd hd₁ hd₂ d
      ((2 * (m + d + 1) : ℕ) : ℤ) (testFamilyClass f g R ux) (chowCycleClass R (m + d + 1) β)
      hu₀ hu₁
  have A₀ := pushforward_interFibre_testFamilyClass_eq f g R (testZeroSection f g)
    lineZeroComplexPoint (testZeroSection_comp_testDeformationToLine f g) _
    (ofHom_map_testZeroSection_comp f g) (hasProperNeighbourhoodDeformations_testZeroMap f g) ux
    (k := ((2 * (m + d + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ)) (by push_cast; ring)
    (chowCycleClass R (m + d) α) _ (h0 β hβ u₀ hu₀)
  have A₁ := pushforward_interFibre_testFamilyClass_eq f g R (testInfinityInclusion f g)
    lineInfinityComplexPoint (testInfinityInclusion_comp_testDeformationToLine f g) _
    (ofHom_map_testInfinityInclusion_comp f g)
    (hasProperNeighbourhoodDeformations_preimage_range_map (lineFamily f)
      (testInfinityInclusion f g ≫ pullback.fst _ g)) ux
    (k := ((2 * (m + d + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ)) (by push_cast; ring)
    _ _ (hinf β hβ u₁ hu₁)
  have K := (BorelMooreCross.congrDegree R _ _).injective (A₀.symm.trans (key.trans A₁))
  rw [← hOinf ux hux, ← K, pushforward_congrDegree_comm,
    pushforward_fibreSquarePointsHom_testZeroEnd f g R hf u hu hO0 ux hux]

end MMP.Chow
