module

public import MMP.AlgebraicTopology.BorelMoore.FibreClassConstancy
public import MMP.AlgebraicGeometry.CycleMap.AlgebraicEquivalence.StacksSpecialization
public import MMP.AlgebraicTopology.RefinedGysin.CapSwap
public import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced

/-!
# Constancy of fibre cycle classes along a locally trivial family, on Stacks cycles

Let `f : V → T` be a dominant morphism from a complex variety of dimension `n + 1` to a
non-singular complex curve, `W ⊆ T(ℂ)` a connected open subset and `ψ : X × W ≃ₜ f⁻¹(W)` a
product structure over `W`. For parameter points `t, t'` over `W`, the cycle classes of Stacks'
cycles `[V_t]_n` and `[V_{t'}]_n` of the scheme-theoretic fibres, carried to `H_{2n}(X)`, agree:
both are `f^* u_s ∩ cl(V)` carried to `X` (Fulton's Lemma 19.1.3 at a fibre,
`MMP.ParameterPoint.pushforward_cycleClass_fibre_eq_capProductSupportPullback`), and these do not
depend on `s ∈ W` (Fulton, Lemma 19.2(c)), by
`Fourfold.pushforward_fibreTransportHom_capProductSupportPullback_eq_of_isLocalOrientationClass`.

## Main results

* `MMP.Fourfold.pushforward_fibreTransportHom_cycleClass_eq`: the cycle classes of the fibres
  `V_t`, carried to `X` along a product structure of `f⁻¹(W)`, do not depend on `t ∈ W`.
* `MMP.Fourfold.pushforward_fibreTransportHom_fibreAmbientPointsHom_cycleClass_eq`: the ambient
  form, for `f = ι ≫ g` with `ι : V → G` proper and a product structure of the ambient family
  `g⁻¹(W) ⊆ G(ℂ)`, which need not preserve `ι(V)`.
* `MMP.Chow.map_cycleClass_cycleAssociatedToClosedSubscheme_of_isReduced`: for a reduced closed
  subscheme, an additive map sends the class of its `n`-dimensional cycle to the sum of the images
  of the classes of its generic points of delta-dimension `n`.
* `MMP.Fourfold.finsum_pushforward_fibreTransportHom_fibreAmbientPointsHom_pointCycleClass_eq`: for
  reduced fibres, the sums of the classes of the `n`-dimensional components of `V_t`, read in `X`
  through the ambient product structure, do not depend on `t ∈ W`.
* `MMP.Fourfold.pushforward_fibrePointsTransportHom_pointCycleClass_eq_of_range_eq`: for reduced
  fibres with pairwise disjoint components, generic points of components of `V_t` and `V_{t'}`
  with the same image in `X` have the same class in `X`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1–19.2.
-/

@[expose] public section

open CategoryTheory Set Topology MMP MMP.borelMooreHomology AlgebraicGeometry Stacks.Chow
open MMP.UnderlyingSpace
open MMP.Intersection.Scheme (dimension)

namespace MMP.Chow

variable {R : Type} [CommRing R] {X W : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

open Classical in
/-- **The class of a reduced closed subscheme, read through an additive map.** For a closed
immersion `j : W ⟶ X` of a reduced scheme and an additive map `φ` out of `H_{2n}(X)`, `φ` of the
class of the `n`-dimensional part `[j(W)]_n` of the fundamental cycle of `W` (Stacks, Tag 02QU)
is the sum of `φ(cl_X(x))` over the images `x` of the generic points of `W` of
delta-dimension `n`. -/
theorem map_cycleClass_cycleAssociatedToClosedSubscheme_of_isReduced {M : Type*}
    [AddCommMonoid M] {n : ℕ} (φ : BMHomology R X (2 * n) →+ M) (j : W ⟶ X)
    [IsClosedImmersion j] [IsReduced W] :
    φ (cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        (X ↘ Spec (.of ℂ)) j n)) =
      ∑ᶠ (x : {x : X // relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (X ↘ Spec (.of ℂ)) x = n})
        (_ : ∃ ξ : genericPoints W, j.base ξ.1 = x.1), φ (pointCycleClass R x.1 x.2) := by
  set α := cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) j (n : ℤ)
  have hS := finite_support_cycle α
  have hval : ∀ x : X, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = n →
      α.1 x = if ∃ ξ : genericPoints W, j.base ξ.1 = x then 1 else 0 := by
    intro x hx
    split_ifs with h
    · obtain ⟨ξ, rfl⟩ := h
      rw [cycleAssociatedToClosedSubscheme_apply (fieldChowSituation ℂ) _ j _ ξ hx,
        componentMultiplicity_eq_one_of_reduced]
    · exact cycleAssociatedToClosedSubscheme_apply_eq_zero _ _ j _ x
        fun ⟨ξ, hξ, _⟩ ↦ h ⟨ξ, hξ⟩
  have hdim : ∀ x ∈ hS.toFinset, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = n := fun x hx ↦
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation ℂ) _ _ α.1).mp α.2 x
      (hS.mem_toFinset.mp hx)
  rw [cycleClass_eq_sum, map_sum,
    finsum_cond_eq_sum_of_cond_iff _ (t := hS.toFinset.subtype fun x ↦
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n)
      fun {x} _ ↦ by
        rw [Finset.mem_subtype, hS.mem_toFinset, Function.mem_support, hval x.1 x.2]
        split_ifs with h
        · exact iff_of_true h one_ne_zero
        · exact iff_of_false h fun h' ↦ h' rfl]
  rw [show (∑ x ∈ hS.toFinset.subtype fun x ↦
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n,
        φ (pointCycleClass R x.1 x.2)) =
      ∑ x ∈ hS.toFinset.subtype fun x ↦
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n,
        φ (pointCycleClassOrZero R n x.1) from
      Finset.sum_congr rfl fun x _ ↦ by rw [pointCycleClassOrZero, dite_eq_left x.2],
    Finset.sum_subtype_eq_sum_filter (f := fun x ↦ φ (pointCycleClassOrZero R n x)),
    Finset.filter_true_of_mem hdim]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hne : α.1 x ≠ 0 := hS.mem_toFinset.mp hx
  rw [hval x (hdim x hx)] at hne ⊢
  rw [ite_eq_left (by by_contra h; exact hne (ite_eq_right h)), one_smul]

end MMP.Chow

namespace MMP.Fourfold

variable {R : Type} [CommRing R] {T : Scheme.{0}} [T.Over (Spec (.of ℂ))]
  [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))] {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
  [IsComplexScheme V] [IsIntegral V]

/-- **Fibre cycle classes are constant along a local trivialization** (Fulton, Lemma 19.1.3 and
Lemma 19.2(c)). Let `f : V → T` be a dominant morphism from a complex variety of dimension
`n + 1` to a non-singular complex curve, `W ⊆ T(ℂ)` a connected open subset and
`ψ : X × W ≃ₜ f⁻¹(W)` a product structure over `W`. For parameter points `t, t'` over `W`, the
cycle classes `cl([V_t]_n)` and `cl([V_{t'}]_n)` of Stacks' cycles of the scheme-theoretic fibres,
carried to `H_{2n}(X)` along `V_t(ℂ) ≅ f⁻¹(t) ≅ X`, agree. -/
theorem pushforward_fibreTransportHom_cycleClass_eq
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ)))
    (f : V ⟶ T) [f.IsOver (Spec (.of ℂ))] [IsDominant f] {n : ℕ}
    (hn : ((n + 1 : ℕ) : WithBot ℕ∞) = dimension V) {X : TopCat.{0}}
    [TopologicalSpace.MetrizableSpace X]
    (W : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T)))
    [ConnectedSpace W] (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t t' : ParameterPoint T) (ht : t.complexPoint ∈ W) (ht' : t'.complexPoint ∈ W) :
    (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ ht)
        (isProperMap_fibreTransportHom ψ hψ ht) (2 * n : ℕ)).hom
        ((pushforward R (ModuleCat.of R R) (ParameterPoint.fibreComplexPointsHom f t)
          (ParameterPoint.isProperMap_fibreComplexPointsHom f t) (2 * n : ℕ)).hom
          (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
            (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) (𝟙 _) n))) =
      (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ ht')
        (isProperMap_fibreTransportHom ψ hψ ht') (2 * n : ℕ)).hom
        ((pushforward R (ModuleCat.of R R) (ParameterPoint.fibreComplexPointsHom f t')
          (ParameterPoint.isProperMap_fibreComplexPointsHom f t') (2 * n : ℕ)).hom
          (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
            (ParameterPoint.fibre f t' ↘ Spec (.of ℂ)) (𝟙 _) n))) := by
  have hTo := isOrientedAtlas_of_isManifold_complex
    (E := EuclideanSpace ℂ (Fin 1)) (TopCat.of (UnderlyingSpace ℂ T))
  obtain ⟨u, hu⟩ := exists_isLocalOrientationClass (R := R) hTo (by norm_num)
    curveOrientationBasis t.complexPoint
  obtain ⟨u', hu'⟩ := exists_isLocalOrientationClass (R := R) hTo (by norm_num)
    curveOrientationBasis t'.complexPoint
  obtain ⟨μ, hμ, -⟩ := existsUnique_isVarietyFundamentalClass R hn
  have h₁ := ParameterPoint.pushforward_cycleClass_fibre_eq_capProductSupportPullback R hT f hn t
    hu hμ
  have h₂ := ParameterPoint.pushforward_cycleClass_fibre_eq_capProductSupportPullback R hT f hn t'
    hu' hμ
  erw [h₁, h₂, pushforward_congrDegree_comm, pushforward_congrDegree_comm]
  congr 1
  exact pushforward_fibreTransportHom_capProductSupportPullback_eq_of_isLocalOrientationClass
    hTo (by norm_num) curveOrientationBasis ψ hψ
    (hasProperNeighbourhoodDeformations_preimage_singleton f) _ μ ht ht' hu hu'

variable {G : Scheme.{0}} [G.Over (Spec (.of ℂ))] [IsComplexScheme G]

/-- **Ambient fibre cycle classes are constant along a local trivialization** (Fulton,
Lemma 19.1.3 and Lemma 19.2(c)). Let `g : G → T` be a morphism of complex schemes to a
non-singular complex curve, `ι : V → G` a proper morphism from a complex variety of dimension
`n + 1` with `f = ι ≫ g` dominant, `W ⊆ T(ℂ)` a connected open subset and `ψ : X × W ≃ₜ g⁻¹(W)`
a product structure of the ambient family over `W` (not required to preserve `ι(V)`). For
parameter points `t, t'` over `W`, the cycle classes `cl([V_t]_n)` and `cl([V_{t'}]_n)` of Stacks'
cycles of the scheme-theoretic fibres of `f`, pushed into `H_{2n}(g⁻¹ t)` and `H_{2n}(g⁻¹ t')` and
carried to `H_{2n}(X)` along `g⁻¹(t) ≅ X ≅ g⁻¹(t')`, agree. -/
theorem pushforward_fibreTransportHom_fibreAmbientPointsHom_cycleClass_eq
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (ι : V ⟶ G) [ι.IsOver (Spec (.of ℂ))]
    [IsProper ι] (g : G ⟶ T) [g.IsOver (Spec (.of ℂ))] (f : V ⟶ T) [f.IsOver (Spec (.of ℂ))]
    [IsDominant f] (hf : ι ≫ g = f) {n : ℕ} (hn : ((n + 1 : ℕ) : WithBot ℕ∞) = dimension V)
    {X : TopCat.{0}} [TopologicalSpace.MetrizableSpace X]
    (W : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T)))
    [ConnectedSpace W] (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) g)) W)
    (hψ : ∀ p, map (K := ℂ) g (ψ p : UnderlyingSpace ℂ G) = (p.2 : UnderlyingSpace ℂ T))
    (t t' : ParameterPoint T) (ht : t.complexPoint ∈ W) (ht' : t'.complexPoint ∈ W) :
    (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ ht)
        (isProperMap_fibreTransportHom ψ hψ ht) (2 * n : ℕ)).hom
        ((pushforward R (ModuleCat.of R R) (fibreAmbientPointsHom ι g hf t)
          (isProperMap_fibreAmbientPointsHom ι g hf t) (2 * n : ℕ)).hom
          (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
            (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) (𝟙 _) n))) =
      (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ ht')
        (isProperMap_fibreTransportHom ψ hψ ht') (2 * n : ℕ)).hom
        ((pushforward R (ModuleCat.of R R) (fibreAmbientPointsHom ι g hf t')
          (isProperMap_fibreAmbientPointsHom ι g hf t') (2 * n : ℕ)).hom
          (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
            (ParameterPoint.fibre f t' ↘ Spec (.of ℂ)) (𝟙 _) n))) := by
  have hTo := isOrientedAtlas_of_isManifold_complex
    (E := EuclideanSpace ℂ (Fin 1)) (TopCat.of (UnderlyingSpace ℂ T))
  obtain ⟨u, hu⟩ := exists_isLocalOrientationClass (R := R) hTo (by norm_num)
    curveOrientationBasis t.complexPoint
  obtain ⟨u', hu'⟩ := exists_isLocalOrientationClass (R := R) hTo (by norm_num)
    curveOrientationBasis t'.complexPoint
  obtain ⟨μ, hμ, -⟩ := existsUnique_isVarietyFundamentalClass R hn
  have h₁ := ParameterPoint.pushforward_cycleClass_fibre_eq_capProductSupportPullback R hT f hn t
    hu hμ
  have h₂ := ParameterPoint.pushforward_cycleClass_fibre_eq_capProductSupportPullback R hT f hn t'
    hu' hμ
  have hι : IsProperMap (TopCat.ofHom (map (K := ℂ) ι)) := isProperMap_map (K := ℂ) ι
  have hφ := fibreAmbientPointsHom_aux ι g hf
  have e₁ := pushforward_comp_apply' R (ParameterPoint.fibreComplexPointsHom f t)
    (preimageRestrictHom _ _ hφ {t.complexPoint})
    (ParameterPoint.isProperMap_fibreComplexPointsHom f t)
    (isProperMap_preimageRestrictHom hι _ hφ _)
    (2 * n : ℕ) (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) (𝟙 _) n))
  have e₂ := pushforward_comp_apply' R (ParameterPoint.fibreComplexPointsHom f t')
    (preimageRestrictHom _ _ hφ {t'.complexPoint})
    (ParameterPoint.isProperMap_fibreComplexPointsHom f t')
    (isProperMap_preimageRestrictHom hι _ hφ _)
    (2 * n : ℕ) (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
      (ParameterPoint.fibre f t' ↘ Spec (.of ℂ)) (𝟙 _) n))
  erw [e₁, e₂, h₁, h₂]
  simp only [pushforward_congrDegree_comm]
  rw [pushforward_preimageRestrictHom_capProductSupportPullback hι _ hφ isClosed_singleton
      (hasProperNeighbourhoodDeformations_preimage_singleton g _),
    pushforward_preimageRestrictHom_capProductSupportPullback hι _ hφ isClosed_singleton
      (hasProperNeighbourhoodDeformations_preimage_singleton g _)]
  congr 1
  exact pushforward_fibreTransportHom_capProductSupportPullback_eq_of_isLocalOrientationClass
    hTo (by norm_num) curveOrientationBasis ψ hψ
    (hasProperNeighbourhoodDeformations_preimage_singleton g) _
    ((pushforward R (ModuleCat.of R R) _ hι _).hom μ) ht ht' hu hu'

/-- **Sums of fibre component classes are constant along an ambient local trivialization**
(Fulton, Lemma 19.1.3 and Lemma 19.2(c)). In the setting of
`pushforward_fibreTransportHom_fibreAmbientPointsHom_cycleClass_eq`, let the fibres `V_t` and
`V_{t'}` be reduced. Then the sums of the cycle classes `cl(x)` of the generic points `x` of
delta-dimension `n` of `V_t` and of `V_{t'}`, read in `X` through `ι` and the product structure
`ψ` of the ambient family, agree. -/
theorem finsum_pushforward_fibreTransportHom_fibreAmbientPointsHom_pointCycleClass_eq
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (ι : V ⟶ G) [ι.IsOver (Spec (.of ℂ))]
    [IsProper ι] (g : G ⟶ T) [g.IsOver (Spec (.of ℂ))] (f : V ⟶ T) [f.IsOver (Spec (.of ℂ))]
    [IsDominant f] (hf : ι ≫ g = f) {n : ℕ} (hn : ((n + 1 : ℕ) : WithBot ℕ∞) = dimension V)
    {X : TopCat.{0}} [TopologicalSpace.MetrizableSpace X]
    (W : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T)))
    [ConnectedSpace W] (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) g)) W)
    (hψ : ∀ p, map (K := ℂ) g (ψ p : UnderlyingSpace ℂ G) = (p.2 : UnderlyingSpace ℂ T))
    (t t' : ParameterPoint T) (ht : t.complexPoint ∈ W) (ht' : t'.complexPoint ∈ W)
    [IsReduced (ParameterPoint.fibre f t)] [IsReduced (ParameterPoint.fibre f t')] :
    ∑ᶠ (x : {x : ParameterPoint.fibre f t // relativeDimension
          (fieldChowSituation ℂ).dimensionFunction (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) x =
            n})
        (_ : x.1 ∈ genericPoints (ParameterPoint.fibre f t)),
        (pushforward R (ModuleCat.of R R)
          (fibreAmbientPointsHom ι g hf t ≫ fibreTransportHom ψ hψ ht)
          ((isProperMap_fibreTransportHom ψ hψ ht).comp
            (isProperMap_fibreAmbientPointsHom ι g hf t)) (2 * n : ℕ)).hom
          (Chow.pointCycleClass R x.1 x.2) =
      ∑ᶠ (x : {x : ParameterPoint.fibre f t' // relativeDimension
          (fieldChowSituation ℂ).dimensionFunction (ParameterPoint.fibre f t' ↘ Spec (.of ℂ)) x =
            n})
        (_ : x.1 ∈ genericPoints (ParameterPoint.fibre f t')),
        (pushforward R (ModuleCat.of R R)
          (fibreAmbientPointsHom ι g hf t' ≫ fibreTransportHom ψ hψ ht')
          ((isProperMap_fibreTransportHom ψ hψ ht').comp
            (isProperMap_fibreAmbientPointsHom ι g hf t')) (2 * n : ℕ)).hom
          (Chow.pointCycleClass R x.1 x.2) := by
  have key : ∀ (s : ParameterPoint T) (hs : s.complexPoint ∈ W)
      [IsReduced (ParameterPoint.fibre f s)],
      (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ hs)
          (isProperMap_fibreTransportHom ψ hψ hs) (2 * n : ℕ)).hom
          ((pushforward R (ModuleCat.of R R) (fibreAmbientPointsHom ι g hf s)
            (isProperMap_fibreAmbientPointsHom ι g hf s) (2 * n : ℕ)).hom
            (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
              (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) (𝟙 _) n))) =
        ∑ᶠ (x : {x : ParameterPoint.fibre f s // relativeDimension
            (fieldChowSituation ℂ).dimensionFunction
              (ParameterPoint.fibre f s ↘ Spec (.of ℂ)) x = n})
          (_ : x.1 ∈ genericPoints (ParameterPoint.fibre f s)),
          (pushforward R (ModuleCat.of R R)
            (fibreAmbientPointsHom ι g hf s ≫ fibreTransportHom ψ hψ hs)
            ((isProperMap_fibreTransportHom ψ hψ hs).comp
              (isProperMap_fibreAmbientPointsHom ι g hf s)) (2 * n : ℕ)).hom
            (Chow.pointCycleClass R x.1 x.2) := by
    intro s hs _
    have h := Chow.map_cycleClass_cycleAssociatedToClosedSubscheme_of_isReduced (R := R)
      ((pushforward R (ModuleCat.of R R)
        (fibreAmbientPointsHom ι g hf s ≫ fibreTransportHom ψ hψ hs)
        ((isProperMap_fibreTransportHom ψ hψ hs).comp
          (isProperMap_fibreAmbientPointsHom ι g hf s)) (2 * n : ℕ)).hom.toAddMonoidHom)
      (𝟙 (ParameterPoint.fibre f s))
    rw [← pushforward_comp_apply']
    refine h.trans (finsum_congr fun x ↦ ?_)
    exact finsum_congr_Prop (propext ⟨fun ⟨ξ, hξ⟩ ↦ by rw [← hξ]; exact ξ.2,
      fun hx ↦ ⟨⟨_, hx⟩, rfl⟩⟩) fun _ ↦ rfl
  rw [← key t ht, ← key t' ht']
  exact pushforward_fibreTransportHom_fibreAmbientPointsHom_cycleClass_eq hT ι g f hf hn W ψ hψ
    t t' ht ht'

section componentPiece

variable {f : V ⟶ T} [f.IsOver (Spec (.of ℂ))] {X : TopCat.{0}}
  {W : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T))}

/-- The map from the complex points of the closure of a point `y` of the fibre `V_t` to `X`,
given by the closed immersion into `V_t` followed by the product structure `ψ : X × W ≃ₜ f⁻¹(W)`.
-/
noncomputable def componentTransportHom
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) (y : ParameterPoint.fibre f t) :
    TopCat.of (UnderlyingSpace ℂ (integralComponentAt y).subscheme) ⟶ X :=
  TopCat.ofHom (map (K := ℂ) (integralComponentAt y).subschemeι) ≫
    fibrePointsTransportHom ψ hψ t ht

omit [IsIntegral V] in
/-- `componentTransportHom` is the closed immersion of `closure {y}` followed by
`fibrePointsTransportHom`. -/
theorem coe_componentTransportHom
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) (y : ParameterPoint.fibre f t) :
    ⇑(componentTransportHom ψ hψ t ht y) =
      fibrePointsTransportHom ψ hψ t ht ∘ map (K := ℂ) (integralComponentAt y).subschemeι :=
  rfl

omit [IsIntegral V] in
/-- `componentTransportHom` is a closed embedding. -/
theorem isClosedEmbedding_componentTransportHom
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) (y : ParameterPoint.fibre f t) :
    Topology.IsClosedEmbedding (componentTransportHom ψ hψ t ht y) :=
  (isClosedEmbedding_fibrePointsTransportHom ψ hψ t ht).comp
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (integralComponentAt y).subschemeι)

omit [IsIntegral V] in
/-- The range of `componentTransportHom` is the image in `X` of the complex points of
`closure {y}`. -/
theorem range_componentTransportHom
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) (y : ParameterPoint.fibre f t) :
    Set.range (componentTransportHom ψ hψ t ht y) =
      fibrePointsTransportHom ψ hψ t ht '' pointsOver (K := ℂ) (closure {y}) := by
  rw [coe_componentTransportHom, Set.range_comp, range_map_of_isClosedImmersion,
    Scheme.IdealSheafData.range_subschemeι,
    coe_support_integralComponentAt]

omit [IsIntegral V] in
/-- The class of a point `y` of `V_t`, read in `X`, is a push-forward along
`componentTransportHom` of some class on the complex points of `closure {y}`. -/
theorem exists_pushforward_fibrePointsTransportHom_pointCycleClass_eq
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) {n : ℕ} (y : ParameterPoint.fibre f t)
    (hy : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) y = n) :
    ∃ c, (pushforward R (ModuleCat.of R R) (fibrePointsTransportHom ψ hψ t ht)
        (isClosedEmbedding_fibrePointsTransportHom ψ hψ t ht).isProperMap (2 * n : ℕ)).hom
        (Chow.pointCycleClass R y hy) =
      (pushforward R (ModuleCat.of R R) (componentTransportHom ψ hψ t ht y)
        (isClosedEmbedding_componentTransportHom ψ hψ t ht y).isProperMap (2 * n : ℕ)).hom c :=
  ⟨_, (pushforward_comp_apply' R _ _ _ _ _ _).symm⟩

omit [IsIntegral V] in
/-- If the irreducible components of `V_t` are pairwise disjoint, the image in `X` of the closure
of a generic point of `V_t` is open. -/
theorem isOpen_range_componentTransportHom
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W)
    (hdisj : ∀ A ∈ irreducibleComponents (ParameterPoint.fibre f t),
      ∀ B ∈ irreducibleComponents (ParameterPoint.fibre f t), A ≠ B → Disjoint A B)
    {y : ParameterPoint.fibre f t} (hy : y ∈ genericPoints (ParameterPoint.fibre f t)) :
    IsOpen (Set.range (componentTransportHom ψ hψ t ht y)) := by
  have : IsLocallyNoetherian (ParameterPoint.fibre f t) :=
    LocallyOfFiniteType.isLocallyNoetherian ((ParameterPoint.fibre f t) ↘ Spec (.of ℂ))
  have : CompactSpace (ParameterPoint.fibre f t) :=
    (quasiCompact_iff_compactSpace (ParameterPoint.fibre f t ↘ Spec (.of ℂ))).mp inferInstance
  have : AlgebraicGeometry.IsNoetherian (ParameterPoint.fibre f t) := ⟨⟩
  have hce := isClosedEmbedding_fibrePointsTransportHom ψ hψ t ht
  have hbij : Function.Bijective (fibrePointsTransportHom ψ hψ t ht) :=
    ⟨hce.injective, surjective_fibrePointsTransportHom ψ hψ t ht⟩
  have hCo : IsOpen (closure {y} : Set (ParameterPoint.fibre f t)) :=
    isOpen_of_mem_irreducibleComponents_of_disjoint hy hdisj
  have hPo : IsOpen (pointsOver (K := ℂ) (closure {y} : Set (ParameterPoint.fibre f t))) := by
    convert isOpen_setOf_le_preimage (K := ℂ) (⟨_, hCo⟩ : TopologicalSpace.Opens _) using 1
    ext p
    exact (top_le_preimage_iff p ⟨_, hCo⟩).symm
  rw [range_componentTransportHom, ← compl_compl (pointsOver (K := ℂ) _),
    Set.image_compl_eq hbij]
  exact (hce.isClosedMap _ hPo.isClosed_compl).isOpen_compl

omit [IsIntegral V] in
/-- If the irreducible components of `V_t` are pairwise disjoint, the images in `X` of the
closures of two distinct generic points of `V_t` are disjoint. -/
theorem disjoint_range_componentTransportHom
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W)
    (hdisj : ∀ A ∈ irreducibleComponents (ParameterPoint.fibre f t),
      ∀ B ∈ irreducibleComponents (ParameterPoint.fibre f t), A ≠ B → Disjoint A B)
    {y z : ParameterPoint.fibre f t} (hy : y ∈ genericPoints (ParameterPoint.fibre f t))
    (hz : z ∈ genericPoints (ParameterPoint.fibre f t)) (hyz : y ≠ z) :
    Disjoint (Set.range (componentTransportHom ψ hψ t ht y))
      (Set.range (componentTransportHom ψ hψ t ht z)) := by
  rw [range_componentTransportHom, range_componentTransportHom,
    Set.disjoint_image_iff (isClosedEmbedding_fibrePointsTransportHom ψ hψ t ht).injective]
  have hne : (closure {y} : Set (ParameterPoint.fibre f t)) ≠ closure {z} := fun h ↦
    hyz (inseparable_iff_closure_eq.mpr h).eq
  exact (hdisj _ hy _ hz hne).preimage _

omit [IsIntegral V] in
/-- **The piece of the fibre class on one component.** Let `V_t` be a reduced fibre whose
irreducible components are pairwise disjoint and `y` the generic point of a component of
delta-dimension `n`. Restricting the class of `[V_t]_n`, read in `X`, to the clopen image `Ω` of
`closure {y}` and pushing it back gives the class of `y`, read in `X`. -/
theorem pushforward_inclHom_restrict_cycleClass_eq [T2Space X]
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) [IsReduced (ParameterPoint.fibre f t)]
    (hdisj : ∀ A ∈ irreducibleComponents (ParameterPoint.fibre f t),
      ∀ B ∈ irreducibleComponents (ParameterPoint.fibre f t), A ≠ B → Disjoint A B)
    {n : ℕ} {y : ParameterPoint.fibre f t} (hyg : y ∈ genericPoints (ParameterPoint.fibre f t))
    (hy : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) y = n)
    (Ω : TopologicalSpace.Opens X)
    (hΩ : (Ω : Set X) = Set.range (componentTransportHom ψ hψ t ht y))
    (hp : IsProperMap (inclHom Ω)) :
    (pushforward R (ModuleCat.of R R) (inclHom Ω) hp (2 * n : ℕ)).hom
        ((restrict R (ModuleCat.of R R) Ω (2 * n : ℕ)).hom
          ((pushforward R (ModuleCat.of R R) (fibrePointsTransportHom ψ hψ t ht)
            (isClosedEmbedding_fibrePointsTransportHom ψ hψ t ht).isProperMap (2 * n : ℕ)).hom
            (Chow.cycleClass R n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
              (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) (𝟙 _) n)))) =
      (pushforward R (ModuleCat.of R R) (fibrePointsTransportHom ψ hψ t ht)
        (isClosedEmbedding_fibrePointsTransportHom ψ hψ t ht).isProperMap (2 * n : ℕ)).hom
        (Chow.pointCycleClass R y hy) := by
  classical
  set φ := (((pushforward R (ModuleCat.of R R) (inclHom Ω) hp (2 * n : ℕ)).hom.toAddMonoidHom.comp
    (restrict R (ModuleCat.of R R) Ω (2 * n : ℕ)).hom.toAddMonoidHom).comp
    (pushforward R (ModuleCat.of R R) (fibrePointsTransportHom ψ hψ t ht)
      (isClosedEmbedding_fibrePointsTransportHom ψ hψ t ht).isProperMap
      (2 * n : ℕ)).hom.toAddMonoidHom) with hφ
  have h := Chow.map_cycleClass_cycleAssociatedToClosedSubscheme_of_isReduced (R := R) φ
    (𝟙 (ParameterPoint.fibre f t))
  have hφy : φ (Chow.pointCycleClass R y hy) =
      (pushforward R (ModuleCat.of R R) (fibrePointsTransportHom ψ hψ t ht)
        (isClosedEmbedding_fibrePointsTransportHom ψ hψ t ht).isProperMap (2 * n : ℕ)).hom
        (Chow.pointCycleClass R y hy) := by
    obtain ⟨c, hc⟩ :=
      exists_pushforward_fibrePointsTransportHom_pointCycleClass_eq (R := R) ψ hψ t ht y hy
    simp only [hφ, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hc]
    exact pushforward_inclHom_restrict_pushforward_of_range_subset _ _ _ hΩ.symm.subset _ _ _
  have hφz : ∀ z (hz : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) z = n),
      z ∈ genericPoints (ParameterPoint.fibre f t) → z ≠ y →
      φ (Chow.pointCycleClass R z hz) = 0 := by
    intro z hz hzg hzy
    obtain ⟨c, hc⟩ :=
      exists_pushforward_fibrePointsTransportHom_pointCycleClass_eq (R := R) ψ hψ t ht z hz
    simp only [hφ, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hc, restrict_pushforward_eq_zero_of_disjoint, map_zero]
    rw [hΩ]
    exact disjoint_range_componentTransportHom ψ hψ t ht hdisj hzg hyg hzy
  change φ _ = _
  rw [h, finsum_eq_single _ ⟨y, hy⟩, finsum_eq_if,
    ite_eq_left ⟨⟨y, hyg⟩, rfl⟩, hφy]
  intro z hzy
  rw [finsum_eq_if]
  split_ifs with hz
  · obtain ⟨ξ, hξ⟩ := hz
    exact hφz z.1 z.2 (by rw [← hξ]; exact ξ.2) fun h ↦ hzy (Subtype.ext h)
  · rfl

/-- **Fibre component classes are constant along a local trivialization**, on Stacks cycles. Let
`f : V → T` be a dominant morphism from a complex variety of dimension `n + 1` to a non-singular
complex curve, `ψ : X × W ≃ₜ f⁻¹(W)` a product structure over a connected open `W ⊆ T(ℂ)`, and
`t, t'` parameter points over `W` whose fibres are reduced with pairwise disjoint components. If
generic points `x ∈ V_t` and `x' ∈ V_{t'}` of components of delta-dimension `n` have closures with
the same image in `X`, their cycle classes, read in `X`, agree. -/
theorem pushforward_fibrePointsTransportHom_pointCycleClass_eq_of_range_eq
    [TopologicalSpace.MetrizableSpace X]
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) [IsDominant f] {n : ℕ}
    (hn : ((n + 1 : ℕ) : WithBot ℕ∞) = dimension V) [ConnectedSpace W]
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t t' : ParameterPoint T) (ht : t.complexPoint ∈ W) (ht' : t'.complexPoint ∈ W)
    [IsReduced (ParameterPoint.fibre f t)] [IsReduced (ParameterPoint.fibre f t')]
    (hdisj : ∀ A ∈ irreducibleComponents (ParameterPoint.fibre f t),
      ∀ B ∈ irreducibleComponents (ParameterPoint.fibre f t), A ≠ B → Disjoint A B)
    (hdisj' : ∀ A ∈ irreducibleComponents (ParameterPoint.fibre f t'),
      ∀ B ∈ irreducibleComponents (ParameterPoint.fibre f t'), A ≠ B → Disjoint A B)
    {x : ParameterPoint.fibre f t} (hxg : x ∈ genericPoints (ParameterPoint.fibre f t))
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f t ↘ Spec (.of ℂ)) x = n)
    {x' : ParameterPoint.fibre f t'} (hxg' : x' ∈ genericPoints (ParameterPoint.fibre f t'))
    (hx' : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (ParameterPoint.fibre f t' ↘ Spec (.of ℂ)) x' = n)
    (hxx' : Set.range (componentTransportHom ψ hψ t ht x) =
      Set.range (componentTransportHom ψ hψ t' ht' x')) :
    (pushforward R (ModuleCat.of R R) (fibrePointsTransportHom ψ hψ t ht)
        (isClosedEmbedding_fibrePointsTransportHom ψ hψ t ht).isProperMap (2 * n : ℕ)).hom
        (Chow.pointCycleClass R x hx) =
      (pushforward R (ModuleCat.of R R) (fibrePointsTransportHom ψ hψ t' ht')
        (isClosedEmbedding_fibrePointsTransportHom ψ hψ t' ht').isProperMap (2 * n : ℕ)).hom
        (Chow.pointCycleClass R x' hx') := by
  have hD := pushforward_fibreTransportHom_cycleClass_eq (R := R) hT f hn W ψ hψ t t' ht ht'
  rw [← pushforward_comp_apply', ← pushforward_comp_apply'] at hD
  set Ω : TopologicalSpace.Opens X :=
    ⟨_, isOpen_range_componentTransportHom ψ hψ t ht hdisj hxg⟩ with hΩ
  have hp : IsProperMap (inclHom Ω) :=
    (Topology.IsClosedEmbedding.subtypeVal
      (isClosedEmbedding_componentTransportHom ψ hψ t ht x).isClosed_range).isProperMap
  rw [← pushforward_inclHom_restrict_cycleClass_eq ψ hψ t ht hdisj hxg hx Ω rfl hp,
    ← pushforward_inclHom_restrict_cycleClass_eq ψ hψ t' ht' hdisj' hxg' hx' Ω hxx' hp]
  exact congrArg _ (congrArg _ hD)

end componentPiece

end MMP.Fourfold
