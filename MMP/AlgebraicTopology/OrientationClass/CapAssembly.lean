module

public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Uniqueness
public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Product
public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Map
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.CapProduct.Restriction
public import MMP.AlgebraicTopology.OrientationClass.ZeroSection

/-!
# Assembling `u_{M,P} ∩ μ_P = μ_M` from the slice parametrization (Fulton, §19.1)

Local classes of cap products travel from a slice core to `M`. For an open set `V` of `P` and a
homeomorphism `φ : W ≅ V` with `φ_* a = μ_P|_V`, the restriction of cap products and the
projection formula give `(u ∩ μ_P)|_{M ∩ V} = φ'_* (φ^* (u|_V) ∩ a)`, so a local class of
`φ^* (u|_V) ∩ a` at a point `p` is one of `u ∩ μ_P` at `φ p`.

## Main definitions

* `MMP.zeroSliceHomeomorph`: the homeomorphism `X ≅ X × {0}`, `y ↦ (y, 0)`.

## Main results

* `MMP.isLocallyClassOf_capProductSupport_of_homeomorph`: if `φ^* (u|_V) ∩ a` is locally the
  class of `σ` at `p`, then `u ∩ μ_P` is locally the class of `φ ∘ σ` at `φ p`.
* `MMP.isLocallyClassOf_capProductSupportPullback_inclHom_prSnd`: the local model on an open set
  of `X × F`.
* `MMP.forget_pullback_pullback_eq`: two pull-backs of a class with supports to a slice core
  agree.
* `MMP.isLocallyClassOf_capProductSupport_forget`: enlarging the support of a cohomology class
  preserves local classes of its cap product.
-/

@[expose] public noncomputable section

open Set Topology Manifold CategoryTheory

universe u

namespace MMP

open MMP

open FundamentalClass borelMooreHomology BorelMooreCross BorelMooreCap ThomClass TensorProduct

variable (R : Type u) [CommRing R]

/-- Transporting a Borel–Moore class along an equality of degrees commutes with restriction to an
open set. -/
lemma congrDegree_restrict {Y : TopCat.{u}} [T2Space Y] (V : TopologicalSpace.Opens Y) {i i' : ℤ}
    (h : i = i') (x : borelMooreHomology R (ModuleCat.of R R) Y i) :
    congrDegree R _ h ((restrict R (ModuleCat.of R R) V i).hom x) =
      (restrict R (ModuleCat.of R R) V i').hom (congrDegree R _ h x) := by
  subst h
  rfl

/-- Let `M` be closed in `P`, `V ⊆ P` open, `φ : W ≅ V` a homeomorphism and `a ∈ H_k W` with
`φ_* a = μ_P|_V`. If `φ^* (u|_V) ∩ a` is locally the class of `σ` at `p ∈ φ⁻¹(M ∩ V)`, then
`u ∩ μ_P` is locally the class of `φ ∘ σ` at `φ p`. -/
theorem isLocallyClassOf_capProductSupport_of_homeomorph (P : TopCat.{u}) [T5Space P]
    {M : Set P} (hM : IsClosed M) (hXd : HasProperNeighbourhoodDeformations M)
    (V : TopologicalSpace.Opens P)
    (hXVd : HasProperNeighbourhoodDeformations ((inclHom V).hom ⁻¹' M)) {W : TopCat.{u}}
    (φ : W ≃ₜ V)
    (hX'd : HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (φ : C(W, V))).hom ⁻¹' ((inclHom V).hom ⁻¹' M)))
    (j k : ℤ) {n : ℕ} (hn : k - j = n) (u : cohomologyWithSupports R (ModuleCat.of R R) P M j)
    (μP : borelMooreHomology R (ModuleCat.of R R) P k)
    (a : borelMooreHomology R (ModuleCat.of R R) W k)
    (ha : (pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(W, V))) φ.isProperMap k).hom a =
      (restrict R (ModuleCat.of R R) V k).hom μP)
    {p : TopCat.of ((TopCat.ofHom (φ : C(W, V))).hom ⁻¹' ((inclHom V).hom ⁻¹' M))}
    {σ : SingularChain.Simplex
      (TopCat.of ((TopCat.ofHom (φ : C(W, V))).hom ⁻¹' ((inclHom V).hom ⁻¹' M))) n}
    (h : IsLocallyClassOf R (congrDegree R _ hn
      (capProductSupportPullback R (TopCat.ofHom (φ : C(W, V)))
        (hM.preimage (inclHom V).hom.continuous) hX'd j k
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom V) M j).hom u) a)) p σ)
    (x : M) (hx : (x : P) = (φ p.1 : P)) (τ : SingularChain.Simplex (TopCat.of M) n)
    (hτ : ∀ t, (τ t : P) = (φ (σ t).1 : P)) :
    IsLocallyClassOf R (congrDegree R _ hn (capProductSupport R P hM hXd j k u μP)) x τ := by
  have h1 := pushforward_restrictPreimage_capProductSupportPullback R
    (TopCat.ofHom (φ : C(W, V))) φ.isProperMap (hM.preimage (inclHom V).hom.continuous) hXVd
    hX'd j k ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom V) M j).hom u) a
  rw [ha, ← capProductSupportPullback_apply R (inclHom V) hM,
    ← pushforward_opensInterMap_restrict_capProductSupport R P V hM hXd hXVd j k u μP] at h1
  have h3 := h.pushforward
    (TopCat.ofHom ((TopCat.ofHom (φ : C(W, V))).hom.restrictPreimage ((inclHom V).hom ⁻¹' M)))
    (φ.isProperMap.restrictPreimage _)
    (fun _ hq ↦ Subtype.ext (φ.injective (congrArg Subtype.val hq)))
  erw [pushforward_congrDegree_apply, h1] at h3
  have h4 := h3.pushforward (opensInterInv V M) (isProperMap_opensInterInv V M)
    (fun q hq ↦ (opensInterHomeo V M).symm.injective hq)
  erw [pushforward_congrDegree_apply, pushforward_comp_apply R _ _ _ _
    (by rw [opensInterMap_opensInterInv]; exact isProperMap_id),
    pushforward_id_apply' R _ _ (opensInterMap_opensInterInv V M), congrDegree_restrict] at h4
  convert IsLocallyClassOf.of_restrict _ h4 using 1
  · exact Subtype.ext hx
  · ext t
    exact hτ t

section Slice

variable {X : Type u} [TopologicalSpace X] [T2Space X] {F : Type u} [NormedAddCommGroup F]

/-- The slice `X ≅ X × {0}`, `y ↦ (y, 0)`. -/
def zeroSliceHomeomorph : X ≃ₜ prPre (TopCat.of X) ({0} : Set (TopCat.of F)) where
  toFun y := ⟨(y, 0), rfl⟩
  invFun p := (p : X × F).1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨y, w⟩, hw⟩
    obtain rfl : w = 0 := hw
    rfl
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

omit [T2Space X] in
/-- The first projection `X × {0} → X` followed by `zeroSliceHomeomorph` is the identity of
`X × {0}`. -/
lemma prPreFst_comp_zeroSliceHomeomorph :
    prPreFst (TopCat.of X) ({0} : Set (TopCat.of F)) ≫
      TopCat.ofHom (zeroSliceHomeomorph (X := X) (F := F) :
        C(X, prPre (TopCat.of X) ({0} : Set (TopCat.of F)))) = 𝟙 _ := by
  ext ⟨⟨y, w⟩, hw⟩
  · rfl
  · exact (hw : w = 0).symm

end Slice

section LocalModel

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H] {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  [TopologicalSpace.MetrizableSpace X]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
/-- **The local model, restricted to an open set `O` of `X × F`.** If the class
`pr_* (pr^* u₀ ∩ (μ_X × μ_F)) ∈ H_n X` is locally the class of `σ` at `y`, and `(y, 0) ∈ O`,
then `ι_O^* pr^* u₀ ∩ (μ_X × μ_F)|_O` is locally the class of `(σ, 0)` at `(y, 0)`. -/
theorem isLocallyClassOf_capProductSupportPullback_inclHom_prSnd {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) n)
    (μF : borelMooreHomology R (ModuleCat.of R R) (TopCat.of F) (2 * Module.finrank ℂ F : ℕ))
    (u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0}
      (2 * Module.finrank ℂ F : ℕ))
    (hXd : HasProperNeighbourhoodDeformations
      (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))
    (hdeg : (n : ℤ) + (2 * Module.finrank ℂ F : ℕ) - (2 * Module.finrank ℂ F : ℕ) = (n : ℕ))
    (O : TopologicalSpace.Opens (TopCat.of (TopCat.of X × TopCat.of F)))
    (hOd : HasProperNeighbourhoodDeformations
      ((inclHom O).hom ⁻¹' (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F)))))
    {y : X} {σ : SingularChain.Simplex (TopCat.of X) n}
    (hA : IsLocallyClassOf R
      ((pushforward R (ModuleCat.of R R) (prPreFst (TopCat.of X) ({0} : Set (TopCat.of F)))
        (isProperMap_prPreFst _ _) n).hom
        (congrDegree R _ hdeg
          (capProductSupportPullback R (prSnd (TopCat.of X) (TopCat.of F)) isClosed_singleton hXd
            (2 * Module.finrank ℂ F : ℕ) ((n : ℤ) + (2 * Module.finrank ℂ F : ℕ)) u₀
            (borelMooreHomology.exteriorProduct R (TopCat.of X) (TopCat.of F) n
              (2 * Module.finrank ℂ F : ℕ) (μ ⊗ₜ μF))))) y σ)
    (q : TopCat.of ((inclHom O).hom ⁻¹'
      (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F)))))
    (hq : ((q : O) : X × F) = (y, 0))
    (τ : SingularChain.Simplex (TopCat.of ((inclHom O).hom ⁻¹'
      (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))) n)
    (hτ : ∀ t, ((τ t : O) : X × F) = (σ t, 0)) :
    IsLocallyClassOf R (congrDegree R _ hdeg
      (capProductSupportPullback R (inclHom O)
        (isClosed_singleton.preimage (prSnd (TopCat.of X) (TopCat.of F)).hom.continuous) hOd
        (2 * Module.finrank ℂ F : ℕ) ((n : ℤ) + (2 * Module.finrank ℂ F : ℕ))
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd (TopCat.of X) (TopCat.of F))
          {0} _).hom u₀)
        ((restrict R (ModuleCat.of R R) O _).hom
          (borelMooreHomology.exteriorProduct R (TopCat.of X) (TopCat.of F) n
              (2 * Module.finrank ℂ F : ℕ) (μ ⊗ₜ μF))))) q τ := by
  set φ := zeroSliceHomeomorph (X := X) (F := F)
  have h1 := hA.pushforward
    (TopCat.ofHom (φ : C(X, prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F)))))
    φ.isProperMap (fun z hz ↦ φ.injective hz)
  have hp : IsProperMap (prPreFst (TopCat.of X) ({0} : Set (TopCat.of F)) ≫
      TopCat.ofHom
        (φ : C(X, prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))) := by
    rw [prPreFst_comp_zeroSliceHomeomorph]
    exact isProperMap_id
  erw [pushforward_comp_apply R _ _ _ _ hp,
    pushforward_id_apply' R _ _ prPreFst_comp_zeroSliceHomeomorph] at h1
  have hmem : ∀ x : X, (x, (0 : F)) ∈ O →
      φ x ∈ opensInter O (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))) :=
    fun x hx ↦ hx
  have hσO : ∀ t, (σ t, (0 : F)) ∈ O := fun t ↦ hτ t ▸ (τ t : O).2
  have hyO : (y, (0 : F)) ∈ O := hq ▸ (q : O).2
  let Δ : SingularChain.Simplex (TopCat.of
      (opensInter O (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))) n :=
    ⟨fun t ↦ ⟨φ (σ t), hmem _ (hσO t)⟩, (φ.continuous.comp σ.continuous).subtype_mk _⟩
  have h2 := IsLocallyClassOf.restrict
    (U := opensInter O (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))
    (x := ⟨φ y, hmem _ hyO⟩) (Δ := Δ) h1
  rw [← congrDegree_restrict] at h2
  have h3 := h2.pushforward
    (opensInterMap O (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))
    (isProperMap_opensInterMap O _) (fun z hz ↦ (opensInterHomeo O _).injective hz)
  erw [pushforward_congrDegree_apply, pushforward_opensInterMap_restrict_capProductSupport R
    (TopCat.of (TopCat.of X × TopCat.of F)) O
    (isClosed_singleton.preimage (prSnd (TopCat.of X) (TopCat.of F)).hom.continuous) hXd hOd] at h3
  have hq' : (opensInterMap O (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))
      ⟨φ y, hmem _ hyO⟩ = q :=
    Subtype.ext (Subtype.ext hq.symm)
  have hτ' : (opensInterMap O
      (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F)))).hom.comp Δ = τ :=
    ContinuousMap.ext fun t ↦ Subtype.ext (Subtype.ext (hτ t).symm)
  rwa [hq', hτ'] at h3

end LocalModel

section Forget

/-- Pulling back relative singular cohomology along `f` and then along `g` is pulling back along
`g ≫ f`. -/
lemma relativeSingularCohomology.map_map_apply {Y'' Y' Y : TopCat.{u}} (g : Y'' ⟶ Y')
    (f : Y' ⟶ Y) {A'' : Set Y''} {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A')
    (hf : A' ⊆ f ⁻¹' A) (j : ℤ) (x : relativeSingularCohomology R (ModuleCat.of R R) Y A j) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) g hg j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f hf j).hom x) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (g ≫ f) (fun _ hx ↦ hf (hg hx)) j).hom
        x := by
  rw [relativeSingularCohomology.map_comp]
  rfl

/-- **The two pull-backs of a class with supports to the slice core agree.** If
`f^* u = pr^* u₀` on `Y` and `φ ≫ ι_V = ι_O ≫ f`, then the pull-back
`ι_O^* pr^* u₀`, with its support enlarged to `φ⁻¹(ι_V⁻¹ M)`, is `φ^* ι_V^* u`. -/
lemma forget_pullback_pullback_eq {W Y V P T : TopCat.{u}} (f : Y ⟶ P) (ιO : W ⟶ Y)
    (φ : W ⟶ V) (ιV : V ⟶ P) (hcomm : φ ≫ ιV = ιO ≫ f) {M : Set P} (pr : Y ⟶ T) {S : Set T}
    (h : (pr ⁻¹' S)ᶜ ⊆ f ⁻¹' Mᶜ) {j : ℤ} (u : cohomologyWithSupports R (ModuleCat.of R R) P M j)
    (u₀ : cohomologyWithSupports R (ModuleCat.of R R) T S j)
    (hA : (relativeSingularCohomology.map R (ModuleCat.of R R) f h j).hom u =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) pr S j).hom u₀)
    (hsub : ιO ⁻¹' (pr ⁻¹' S) ⊆ φ ⁻¹' (ιV ⁻¹' M)) :
    (cohomologyWithSupports.forget R (ModuleCat.of R R) W hsub j).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) ιO (pr ⁻¹' S) j).hom
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) pr S j).hom u₀)) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) φ (ιV ⁻¹' M) j).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) ιV M j).hom u) := by
  rw [← hA]
  change (relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 W)
      (A' := (φ ⁻¹' (ιV ⁻¹' M))ᶜ) (A := (ιO ⁻¹' (pr ⁻¹' S))ᶜ)
      (fun _ hx hx' ↦ hx (hsub hx')) j).hom
      ((relativeSingularCohomology.map R (ModuleCat.of R R) ιO
        (A' := (ιO ⁻¹' (pr ⁻¹' S))ᶜ) (A := (pr ⁻¹' S)ᶜ) (fun _ hx ↦ hx) j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f h j).hom u)) =
    (relativeSingularCohomology.map R (ModuleCat.of R R) φ
      (A' := (φ ⁻¹' (ιV ⁻¹' M))ᶜ) (A := (ιV ⁻¹' M)ᶜ) (fun _ hx ↦ hx) j).hom
      ((relativeSingularCohomology.map R (ModuleCat.of R R) ιV
        (A' := (ιV ⁻¹' M)ᶜ) (A := Mᶜ) (fun _ hx ↦ hx) j).hom u)
  have key : ∀ (g : W ⟶ P) (hg : (φ ⁻¹' (ιV ⁻¹' M))ᶜ ⊆ g ⁻¹' Mᶜ), g = φ ≫ ιV →
      (relativeSingularCohomology.map R (ModuleCat.of R R) g hg j).hom u =
        (relativeSingularCohomology.map R (ModuleCat.of R R) (φ ≫ ιV)
          (A' := (φ ⁻¹' (ιV ⁻¹' M))ᶜ) (A := Mᶜ) (fun _ hx ↦ hx) j).hom u := by
    rintro g hg rfl
    rfl
  calc _ = _ := relativeSingularCohomology.map_map_apply R (𝟙 W) ιO _ _ j _
    _ = _ := relativeSingularCohomology.map_map_apply R _ f _ h j u
    _ = (relativeSingularCohomology.map R (ModuleCat.of R R) (φ ≫ ιV)
          (A' := (φ ⁻¹' (ιV ⁻¹' M))ᶜ) (A := Mᶜ) (fun _ hx ↦ hx) j).hom u :=
        key _ _ (by simp [hcomm])
    _ = _ := (relativeSingularCohomology.map_map_apply R φ ιV _ _ j u).symm

/-- **Forgetting supports keeps local classes.** For closed `X ⊆ X'` with arbitrarily small proper
neighbourhood deformations, if `c ∩ a ∈ H_n X` is locally the class of `τ` at `q`, then
`c' ∩ a ∈ H_n X'` (`c'` the image of `c`) is locally the class of `τ` at `q`, read in `X'`. -/
theorem isLocallyClassOf_capProductSupport_forget (Y : TopCat.{u}) [T2Space Y] {X X' : Set Y}
    (hX : IsClosed X) (hX' : IsClosed X') (hXd : HasProperNeighbourhoodDeformations X)
    (hX'd : HasProperNeighbourhoodDeformations X') (hXX' : X ⊆ X') (j k : ℤ) {n : ℕ}
    (hn : k - j = n) (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (c' : cohomologyWithSupports R (ModuleCat.of R R) Y X' j)
    (hc : (cohomologyWithSupports.forget R (ModuleCat.of R R) Y hXX' j).hom c = c')
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) {q : TopCat.of X}
    {τ : SingularChain.Simplex (TopCat.of X) n}
    (h : IsLocallyClassOf R (congrDegree R _ hn (capProductSupport R Y hX hXd j k c a)) q τ)
    (q' : TopCat.of X') (hq : (q' : Y) = q) (τ' : SingularChain.Simplex (TopCat.of X') n)
    (hτ : ∀ t, (τ' t : Y) = τ t) :
    IsLocallyClassOf R (congrDegree R _ hn (capProductSupport R Y hX' hX'd j k c' a)) q' τ' := by
  have h1 := h.pushforward (subsetInclusionOfSubset hXX')
    (isProperMap_subsetInclusionOfSubset hX hXX') (fun z hz ↦ Set.inclusion_injective hXX' hz)
  erw [pushforward_congrDegree_apply, pushforward_subsetInclusionOfSubset_capProductSupport R Y
    hX hX' hXd hX'd hXX', hc] at h1
  have hq' : subsetInclusionOfSubset hXX' q = q' := Subtype.ext hq.symm
  have hτ' : (subsetInclusionOfSubset hXX').hom.comp τ = τ' :=
    ContinuousMap.ext fun t ↦ Subtype.ext (hτ t).symm
  rwa [hq', hτ'] at h1

end Forget

end MMP
