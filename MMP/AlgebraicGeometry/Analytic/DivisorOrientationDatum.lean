module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksRestrict
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksNormalFibreChart
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksLineSectionZero
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionCartier

/-!
# The line bundle and canonical section of an effective Cartier divisor

Let `D ⊆ X` be an effective Cartier divisor, with invertible sheaf `𝒪_X(D)` and canonical
section `1_D ∈ Γ(X, 𝒪_X(D))` (`Stacks.Divisors.divisorSheaf`,
`Stacks.Divisors.divisorSheafGlobalSection`). The line bundle of `D` is the vector bundle
`𝐕(𝒪_X(D)^∨) = Spec_X Sym(𝒪_X(D)^∨)`, and `1_D` gives a section `σ_D : X ⟶ 𝐕(𝒪_X(D)^∨)`
(`MMP.Modules.globalSectionMap`), whose zero scheme is Stacks' zero scheme `Z(1_D) = D`
([Stacks, Tag 02OQ]). Since `D` is a regular imbedding of codimension one, the normal fibres of
`σ_D` are everything, and `(𝒪_X(D)^∨, σ_D, V, 𝐕(𝒪_X(D)^∨)(ℂ)|_V)` is an orientation datum of `D`:
its quotient bundle is the line bundle itself.

## Main definitions

* `MMP.Topology.divisorDualSheaf`: `𝒪_X(D)^∨`, so that `𝐕(𝒪_X(D)^∨)` is the line bundle of `D`.
* `MMP.Topology.canonicalSectionMap`: the canonical section `σ_D : X ⟶ 𝐕(𝒪_X(D)^∨)`.
* `MMP.Topology.canonicalCoord`: its coordinate in a chart of `𝒪_X(D)^∨`, a local equation of `D`.
* `MMP.Topology.divisorOrientationDatum`: the orientation datum
  `(𝒪_X(D)^∨, σ_D, V, 𝐕(𝒪_X(D)^∨)(ℂ)|_V)` of `D`.

## Main results

* `MMP.Topology.zeroLocus_canonicalSectionMap`: `Z(σ_D) = D`.
* `MMP.Topology.ideal_eq_span_canonicalCoord`: the chart coordinates of `σ_D` generate the ideal
  of `D`.
* `MMP.Topology.map_canonicalCoord_eq_mul`: they change by the transition functions.
* `MMP.Topology.divisorOrientationDatum_quot_mk`: the quotient map of the datum is the identity.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, Appendix B.4.
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Bundle
open MMP.Modules MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)

namespace MMP.Topology

section Divisor

variable {X : Scheme.{0}} (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- `𝒪_X(D)` is invertible, in the spelling of `Stacks.Ample`. -/
instance isInvertibleModule_divisorSheaf :
    Stacks.Ample.IsInvertibleModule X (Stacks.Divisors.divisorSheaf D) :=
  Stacks.Divisors.isInvertible_divisorSheaf D

/-- `𝒪_X(D)^∨`: its vector bundle `𝐕(𝒪_X(D)^∨)` is the line bundle of `D`. -/
abbrev divisorDualSheaf : X.Modules := Scheme.Modules.dual (Stacks.Divisors.divisorSheaf D)

/-- **The canonical section `σ_D : X ⟶ 𝐕(𝒪_X(D)^∨)`** of the line bundle of `D`, given by the
canonical section `1_D` of `𝒪_X(D)`. -/
def canonicalSectionMap : X ⟶ totalSpace (divisorDualSheaf D) :=
  globalSectionMap (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.divisorSheafGlobalSection D)

/-- The canonical section `σ_D` is a section of the projection `𝐕(𝒪_X(D)^∨) ⟶ X`. -/
@[reassoc (attr := simp)]
lemma canonicalSectionMap_proj : canonicalSectionMap D ≫ proj (divisorDualSheaf D) = 𝟙 X :=
  globalSectionMap_proj _ _

/-- The preimage under `σ_D` of the preimage of an open `V ⊆ X` under the projection is `V`. -/
lemma preimage_proj_preimage_canonicalSectionMap (V : X.Opens) :
    canonicalSectionMap D ⁻¹ᵁ (proj (divisorDualSheaf D) ⁻¹ᵁ V) = V :=
  preimage_proj_preimage_globalSectionMap _ _ V

/-- **The zero scheme of the canonical section is the divisor**: `Z(σ_D) = D`. -/
theorem zeroLocus_canonicalSectionMap :
    zeroLocus (divisorDualSheaf D) (canonicalSectionMap D) = D :=
  (zeroLocus_globalSectionMap _ _).trans (Stacks.Divisors.zeroScheme_canonicalSection D)

/-- The zero scheme of `σ_D` is the kernel of the closed immersion `D ⟶ X`. -/
lemma zeroLocus_canonicalSectionMap_eq_ker :
    zeroLocus (divisorDualSheaf D) (canonicalSectionMap D) = D.subschemeι.ker := by
  rw [zeroLocus_canonicalSectionMap, Scheme.IdealSheafData.ker_subschemeι]

/-- An effective Cartier divisor is a regular imbedding of codimension one. -/
theorem isRegularClosedImmersionOfCodim_subschemeι :
    IsRegularClosedImmersionOfCodim D.subschemeι 1 :=
  Stacks.Chow.isRegularClosedImmersionOfCodim_one_of_isEffectiveCartierDivisor _
    (by rw [Scheme.IdealSheafData.ker_subschemeι]; infer_instance)

/-- The coordinate `σ_D^♯ λ = λ(1_D)` of the canonical section in a chart `(V, λ)` of
`𝒪_X(D)^∨`. -/
def canonicalCoord (c : Chart (divisorDualSheaf D) 1) : Γ(X, c.1.1) :=
  sectionCoord (canonicalSectionMap D) c (preimage_proj_preimage_canonicalSectionMap D c.1.1).ge 0

/-- The coordinate of `σ_D` in a chart `(V, λ)` is the evaluation `λ(1_D)`. -/
lemma canonicalCoord_eq_evalGlobal (c : Chart (divisorDualSheaf D) 1) :
    canonicalCoord D c = Scheme.Modules.evalGlobal (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.divisorSheafGlobalSection D) (c.2 0) :=
  sectionCoord_globalSectionMap _ _ c 0

/-- **The chart coordinates of `σ_D` are local equations of `D`**: on an affine open `W` inside
the domain of a chart, the ideal of `D` is generated by the coordinate of `σ_D`. -/
theorem ideal_eq_span_canonicalCoord (c : Chart (divisorDualSheaf D) 1) (W : X.affineOpens)
    (hW : W.1 ≤ c.1.1) :
    D.ideal W = Ideal.span {X.presheaf.map (homOfLE hW).op (canonicalCoord D c)} := by
  have h := ideal_zeroLocus (canonicalSectionMap D) c W
    (hW.trans (preimage_proj_preimage_canonicalSectionMap D _).ge)
  rw [zeroLocus_canonicalSectionMap] at h
  rw [h, Set.range_unique, canonicalCoord, sectionCoord, sectionCoord,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  rfl

/-- **The chart coordinates of `σ_D` change by the transition functions**: on a basic open
`D(a) ⊆ V ∩ V'` of charts `c' = (V', λ')`, `c = (V, λ)`, with `λ = g λ'` there, the coordinate of
`σ_D` in `c` is `g` times the one in `c'`. -/
theorem map_canonicalCoord_eq_mul (c c' : Chart (divisorDualSheaf D) 1) (a : Γ(X, c'.1.1))
    (ha : X.basicOpen a ≤ c.1.1) :
    X.presheaf.map (homOfLE ha).op (canonicalCoord D c) =
      transitionSection c' c a ha 0 0 *
        X.presheaf.map (homOfLE (X.basicOpen_le a)).op (canonicalCoord D c') := by
  rw [canonicalCoord_eq_evalGlobal, canonicalCoord_eq_evalGlobal,
    ← Scheme.Modules.evalGlobal_map, ← Scheme.Modules.evalGlobal_map,
    restrict_eq_sum_transitionSection c' c a ha 0, Fin.sum_univ_one,
    Scheme.Modules.evalGlobal_smul]

variable [X.Over (Spec (.of ℂ))]

/-- The canonical section `σ_D` is a morphism over `Spec ℂ`. -/
instance isOver_canonicalSectionMap : (canonicalSectionMap D).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change canonicalSectionMap D ≫ proj (divisorDualSheaf D) ≫ X ↘ Spec (.of ℂ) =
      X ↘ Spec (.of ℂ)
    rw [canonicalSectionMap_proj_assoc]⟩

end Divisor

section GenericDatum

variable {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] (E : Y.Modules) [E.IsQuasicoherent] {r : ℕ}
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- The base of the bundle `𝐕(ℰ)(ℂ)` used for the orientation datum: all of `Y(ℂ)`. -/
abbrev univInclusion : C(↥(Set.univ : Set (UnderlyingSpace ℂ Y)), UnderlyingSpace ℂ Y) :=
  ⟨Subtype.val, continuous_subtype_val⟩

variable (r) in
/-- The identity `𝐕(ℰ)(ℂ) → 𝐕(ℰ)(ℂ)`, as a map to the topological bundle over `Y(ℂ)`. -/
def fibreQuot (p : {p : UnderlyingSpace ℂ (totalSpace E) //
    mapFun (proj E) p ∈ (Set.univ : Set (UnderlyingSpace ℂ Y))}) :
    TotalSpace (Fin r → ℂ) (⇑(univInclusion (Y := Y)) *ᵖ (Fibre E r)) :=
  ⟨⟨mapFun (proj E) p.1, p.2⟩, (⟨p.1, rfl⟩ : Fibre E r (mapFun (proj E) p.1))⟩

/-- The map `fibreQuot E r` is continuous. -/
theorem continuous_fibreQuot : Continuous (fibreQuot E r) := by
  rw [(inducing_pullbackTotalSpaceEmbedding (Fin r → ℂ) (Fibre E r) _).continuous_iff]
  exact (((continuous_mapFun _).comp continuous_subtype_val).subtype_mk _).prodMk
    ((totalSpaceHomeomorph E r).symm.continuous.comp continuous_subtype_val)

omit [SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r] in
/-- A point `p` of `𝐕(ℰ)(ℂ)` lying over `y` defines the same point of the pullback bundle whether
its base point is written `y` or the projection of `p`. -/
lemma mk_fibreQuot_eq {p : UnderlyingSpace ℂ (totalSpace E)}
    {y : UnderlyingSpace ℂ Y} (hp : mapFun (proj E) p = y) (h1 h2) :
    (⟨⟨mapFun (proj E) p, h1⟩, (⟨p, rfl⟩ : Fibre E r (mapFun (proj E) p))⟩ :
      TotalSpace (Fin r → ℂ) (⇑(univInclusion (Y := Y)) *ᵖ (Fibre E r))) =
      ⟨⟨y, h2⟩, (⟨p, hp⟩ : Fibre E r y)⟩ := by
  subst hp
  rfl

/-- In each chart, `𝐕(ℰ)(ℂ) → 𝐕(ℰ)(ℂ)` is a linear isomorphism on the fibres. -/
theorem exists_linearMap_fibreQuot_chartInv_eq (c : Chart E r) (y : UnderlyingSpace ℂ Y)
    (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1) :
    ∃ L : (Fin r → ℂ) →ₗ[ℂ] (⇑(univInclusion (Y := Y)) *ᵖ (Fibre E r)) ⟨y, Set.mem_univ y⟩,
      (∀ w, fibreQuot E r ⟨chartInv c y hy w, Set.mem_univ _⟩ = ⟨⟨y, Set.mem_univ y⟩, L w⟩) ∧
      Function.Surjective L ∧ LinearMap.ker L = ⊥ := by
  have hb : Function.Bijective (fibreCoord c y) := by
    rw [show ⇑(fibreCoord c y) = fibreEquiv c y hy from funext (fibreCoord_apply c y hy)]
    exact (fibreEquiv c y hy).bijective
  let e := LinearEquiv.ofBijective (fibreCoord c y) hb
  refine ⟨e.symm.toLinearMap, fun w ↦ ?_, e.symm.surjective,
    LinearMap.ker_eq_bot.2 e.symm.injective⟩
  have hL : e.symm w = fibreChartInv c y hy w := by
    rw [e.symm_apply_eq]
    change w = fibreCoord c y (fibreChartInv c y hy w)
    rw [fibreCoord_apply c y hy]
    exact (coord_chartInv c y hy w).symm
  exact (mk_fibreQuot_eq E (mapFun_proj_chartInv c y hy w) _ _).trans
    (congrArg (TotalSpace.mk _) hL.symm)

end GenericDatum

section DivisorDatum

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [D.subscheme.Over (Spec (.of ℂ))] [D.subschemeι.IsOver (Spec (.of ℂ))]

/-- The fibre condition of the orientation datum of `D`: the normal fibres of `σ_D` along `D`
have dimension one, so they are everything, and `𝐕(𝒪_X(D)^∨)(ℂ) → 𝐕(𝒪_X(D)^∨)(ℂ)` has kernel
`0`, a complement. -/
theorem exists_linearMap_isCompl_normalFibre (c : Chart (divisorDualSheaf D) 1)
    (y : UnderlyingSpace ℂ X) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
    (hyN : y ∈ (Set.univ : Set (UnderlyingSpace ℂ X))) :
    ∃ L : (Fin 1 → ℂ) →ₗ[ℂ] (⇑(univInclusion (Y := X)) *ᵖ (Fibre (divisorDualSheaf D) 1)) ⟨y, hyN⟩,
      (∀ w, fibreQuot (divisorDualSheaf D) 1 ⟨chartInv c y hy w, by rwa [mapFun_proj_chartInv]⟩ =
        ⟨⟨y, hyN⟩, L w⟩) ∧ Function.Surjective L ∧
      (y ∈ Set.range (UnderlyingSpace.map D.subschemeι) →
        IsCompl (LinearMap.ker L) (normalFibre (canonicalSectionMap D) c y)) := by
  obtain ⟨L, hL, hs, hk⟩ := exists_linearMap_fibreQuot_chartInv_eq (divisorDualSheaf D) c y hy
  refine ⟨L, hL, hs, ?_⟩
  rintro ⟨x, rfl⟩
  have hN : normalFibre (canonicalSectionMap D) c (UnderlyingSpace.map D.subschemeι x) = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((finrank_normalFibre D.subschemeι
      (isRegularClosedImmersionOfCodim_subschemeι D) (canonicalSectionMap_proj D)
      (zeroLocus_canonicalSectionMap_eq_ker D) c x hy).trans (Module.finrank_fin_fun ℂ).symm)
  rw [hk, hN]
  exact isCompl_bot_top

/-- A neighbourhood `V` of `D(ℂ)` on which `σ_D` vanishes only along `D(ℂ)`. -/
lemma exists_isOpen_canonicalSectionMap_mem_range_zeroSection :
    ∃ V ⊆ (Set.univ : Set (UnderlyingSpace ℂ X)), IsOpen V ∧
      Set.range (UnderlyingSpace.map (K := ℂ) D.subschemeι) ⊆ V ∧
      ∀ y : (Set.univ : Set (UnderlyingSpace ℂ X)), y.1 ∈ V →
        fibreQuot (divisorDualSheaf D) 1 ⟨mapFun (canonicalSectionMap D) y, by
          rw [mapFun_proj_mapFun_section (canonicalSectionMap_proj D)]; exact y.2⟩ ∈
          Set.range (Bundle.zeroSection (Fin 1 → ℂ)
            (⇑(univInclusion (Y := X)) *ᵖ (Fibre (divisorDualSheaf D) 1))) →
        y.1 ∈ Set.range (UnderlyingSpace.map (K := ℂ) D.subschemeι) :=
  exists_isOpen_sectionBar_mem_range_zeroSection D.subschemeι
    (isRegularClosedImmersionOfCodim_subschemeι D) (canonicalSectionMap D)
    (canonicalSectionMap_proj D) (zeroLocus_canonicalSectionMap_eq_ker D) isOpen_univ
    (Set.subset_univ _) (fibreQuot _ 1) (continuous_fibreQuot _)
    (exists_linearMap_isCompl_normalFibre D)

/-- **The orientation datum of an effective Cartier divisor**
`(𝒪_X(D)^∨, σ_D, V, 𝐕(𝒪_X(D)^∨)(ℂ)|_V)`: its module is `𝒪_X(D)^∨`, its section the canonical
section `σ_D`, and its quotient bundle the line bundle `𝐕(𝒪_X(D)^∨)(ℂ)` itself, on a
neighbourhood `V` of `D(ℂ)` on which `σ_D` vanishes only along `D(ℂ)`. -/
def divisorOrientationDatum : RegularImbeddingOrientationDatum D.subschemeι 1 :=
  have h := exists_isOpen_canonicalSectionMap_mem_range_zeroSection D
  RegularImbeddingOrientationDatum.ofRestrict le_rfl (divisorDualSheaf D)
    (canonicalSectionMap D) (canonicalSectionMap_proj D) (zeroLocus_canonicalSectionMap_eq_ker D)
    (Module.finrank_fin_fun ℂ) (fibreQuot _ 1) (continuous_fibreQuot _) (fun _ ↦ rfl)
    (exists_linearMap_isCompl_normalFibre D) h.choose h.choose_spec.1 h.choose_spec.2.1
    h.choose_spec.2.2.1 h.choose_spec.2.2.2

/-- The orientation datum of `D` has rank one. -/
lemma divisorOrientationDatum_rank : (divisorOrientationDatum D).rank = 1 :=
  rfl

/-- The module of the orientation datum of `D` is `𝒪_X(D)^∨`. -/
lemma divisorOrientationDatum_E : (divisorOrientationDatum D).E = divisorDualSheaf D :=
  rfl

/-- The section of the orientation datum of `D` is the canonical section `σ_D`. -/
lemma divisorOrientationDatum_σ : (divisorOrientationDatum D).σ = canonicalSectionMap D :=
  rfl

/-- The quotient map of the orientation datum of `D` is the identity of the line bundle. -/
lemma divisorOrientationDatum_quot_mk (y : (divisorOrientationDatum D).nbhd)
    (w : Fibre (divisorDualSheaf D) 1 y.1)
    (h : mapFun (proj (divisorDualSheaf D)) w.1 ∈ (divisorOrientationDatum D).nbhd) :
    (divisorOrientationDatum D).quot ⟨w.1, h⟩ =
      (⟨y, w⟩ : TotalSpace (divisorOrientationDatum D).F (divisorOrientationDatum D).Q) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨q, hq⟩ := w
  change mapFun _ q = y at hq
  subst hq
  rfl

end DivisorDatum

end MMP.Topology
