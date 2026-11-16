module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.MinimalModel.RadialWeakModelInterval
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalLimitNefReduction
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefModelEquivalence
import MMP.AlgebraicGeometry.Singularities.RealKltRationalDecomposition
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Divisor.Pullback

/-!
# Finiteness of nef weak models along a convergent terminal comparison sequence

Let `Y` be a projective `ℚ`-factorial complex threefold over a projective variety `S`, with
canonical divisor `K_Y`, and let `C_i` be real terminal boundaries on `Y` whose positive supports
are one finite set `F` of prime divisors, converging coefficientwise to a real terminal boundary
`B`. Suppose that every `(Y, C_i)` has a `ℚ`-factorial nef weak model `φ_i : Y ⤏ Z_i` over `S`
whose comparison divisor `p^*(K_Y + C_i) - q^*(K_{Z_i} + φ_{i*} C_i)` has coefficient zero at the
strict transform of every prime of `F`. Then the nef models `(Z_i, φ_{i*} C_i)` fall into finitely
many equivalence classes: there is a finite set `J` of indices such that every model is
equivalent, through the birational map `φ_j ∘ φ_i⁻¹`, to the model of some `j ∈ J`.

## Main results

* `MMP.Fourfold.finite_isNefModelEquivalent_of_tendsto_isRealTerminalPair`: the finiteness.

## Implementation notes

* Convergence in the coefficient space `ℝ^F` is coefficientwise convergence: since every `C_i`
  vanishes off `F`, so does the limit `B`.
* The comparison coefficient at a prime `P` of `Y` is the coefficient of
  `p^*(K_Y + C_i) - q^*(K_{Z_i} + φ_{i*} C_i)` at the strict transform of `P` on a common
  projective resolution `p : W ⟶ Y`, `q : W ⟶ Z_i`; it is independent of the resolution, and the
  hypothesis asks for one resolution, of the kind in `MMP.Fourfold.IsNefWeakModel`, on which it
  vanishes along `F`.
* The birational map `Z_i ⤏ Z_j` identifying the function fields is `φ_j ∘ φ_i⁻¹`, written as the
  rational map of `e_i⁻¹ ≫ e_j` for partial isomorphisms `e_i`, `e_j` representing `φ_i`, `φ_j`.

## References

* [OAI4] the fourfold source, *Finiteness for a convergent terminal comparison sequence*.
-/

@[expose] public section

section

namespace Proof_thm_fourfold_terminal_comparison_models_finite

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology MMP.Mori MMP.Fourfold

universe u

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Partial isomorphisms and composition of rational maps -/

section PartialIso

variable {X Y Z : Scheme.{u}}

private theorem isoOfLE_inv_ι' {U V : X.Opens} (h : U ≤ V) :
    (Scheme.Opens.isoOfLE h).inv ≫ (V.ι ⁻¹ᵁ U).ι = X.homOfLE h := by
  rw [← cancel_mono V.ι]; simp

private theorem restrictSource_iso_hom_ι (e : X.PartialIso Y) (U : X.Opens) (hU : Dense (U : Set X))
    (hU' : U ≤ e.source) :
    (e.restrictSource U hU hU').iso.hom ≫ (e.restrictSource U hU hU').target.ι =
      X.homOfLE hU' ≫ e.iso.hom ≫ e.target.ι := by
  simp [Scheme.PartialIso.restrictSource, reassoc_of% isoOfLE_inv_ι']

private theorem restrictSource_target_le (e : X.PartialIso Y) (U : X.Opens) (hU : Dense (U : Set X))
    (hU' : U ≤ e.source) : (e.restrictSource U hU hU').target ≤ e.target := by
  change e.target.ι ''ᵁ _ ≤ e.target
  exact (Scheme.Hom.image_le_opensRange _ _).trans (by simp)

private theorem restrictSource_iso_hom_homOfLE (e : X.PartialIso Y) (U : X.Opens)
    (hU : Dense (U : Set X))
    (hU' : U ≤ e.source) :
    (e.restrictSource U hU hU').iso.hom ≫ Y.homOfLE (restrictSource_target_le e U hU hU') =
      X.homOfLE hU' ≫ e.iso.hom := by
  refine (cancel_mono e.target.ι).1 ?_
  exact (Category.assoc _ _ _).trans ((congrArg _ (Scheme.homOfLE_ι _ _)).trans
    ((restrictSource_iso_hom_ι e U hU hU').trans (Category.assoc _ _ _).symm))

private theorem restrictTarget_source_le (e : X.PartialIso Y) (V : Y.Opens) (hV : Dense (V : Set Y))
    (hV' : V ≤ e.target) : (e.restrictTarget V hV hV').source ≤ e.source :=
  restrictSource_target_le e.symm V hV hV'

private theorem restrictTarget_iso_hom_ι (e : X.PartialIso Y) (V : Y.Opens) (hV : Dense (V : Set Y))
    (hV' : V ≤ e.target) :
    (e.restrictTarget V hV hV').iso.hom ≫ V.ι =
      X.homOfLE (restrictTarget_source_le e V hV hV') ≫ e.iso.hom ≫ e.target.ι := by
  have h2 := restrictSource_iso_hom_homOfLE e.symm V hV hV'
  change (e.symm.restrictSource V hV hV').iso.inv ≫ V.ι = _
  refine (Iso.inv_comp_eq _).2 ?_
  refine Eq.trans ?_ ((reassoc_of% h2) (e.iso.hom ≫ e.target.ι)).symm
  exact (by simp : V.ι = Y.homOfLE hV' ≫ e.iso.inv ≫ e.iso.hom ≫ e.target.ι)

private theorem isDominant_toPartialMap_hom (e : X.PartialIso Y) :
    IsDominant e.toPartialMap.hom := by
  change IsDominant (e.iso.hom ≫ e.target.ι)
  haveI : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  infer_instance

private theorem comp_toRationalMap_eq {X Y Z : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) {O : X.Opens}
    (hO : Dense (O : Set X)) (hOf : O ≤ f.domain) (β : O.toScheme ⟶ g.domain.toScheme)
    (hβ : β ≫ g.domain.ι = X.homOfLE hOf ≫ f.hom) :
    f.toRationalMap.comp g.toRationalMap = (⟨O, hO, β ≫ g.hom⟩ : X.PartialMap Z).toRationalMap := by
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.PartialMap.toRationalMap_eq_iff]
  have hOc : O ≤ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain := by
    intro x hx
    let y : O.toScheme := ⟨x, hx⟩
    have h1 : f.hom (X.homOfLE hOf y) = g.domain.ι (β y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hβ]
    refine ⟨X.homOfLE hOf y, ?_, ?_⟩
    · show f.hom (X.homOfLE hOf y) ∈ g.domain
      rw [h1]; exact (β y).2
    · show f.domain.ι (X.homOfLE hOf y) = x
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]; rfl
  have key2 : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      (f.hom ⁻¹ᵁ g.domain).ι = X.homOfLE hOf := by
    rw [← cancel_mono f.domain.ι]
    simp only [Category.assoc]
    rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have key : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      f.hom ∣_ g.domain = β := by
    rw [← cancel_mono g.domain.ι, hβ, ← key2]
    simp only [Category.assoc, morphismRestrict_ι]
  refine ⟨O, hO, hOc, le_rfl, ?_⟩
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.comp_hom, Scheme.homOfLE_rfl,
    Category.id_comp]
  rw [← key]
  rfl

private theorem toRationalMap_trans'_eq [IsIntegral X] [Nonempty Y] (f : X.PartialIso Y)
    (g : Y.PartialIso Z) (F : X.PartialIso Y) (G : Y.PartialIso Z) (e : F.target = G.source)
    (hFs : F.source ≤ f.source) (hGs : G.source ≤ g.source)
    (hF : F.iso.hom ≫ F.target.ι = X.homOfLE hFs ≫ f.iso.hom ≫ f.target.ι)
    (hG : G.iso.hom ≫ G.target.ι = Y.homOfLE hGs ≫ g.iso.hom ≫ g.target.ι) :
    haveI := isDominant_toPartialMap_hom f
    (F.trans' G e).toRationalMap = f.toRationalMap.comp g.toRationalMap := by
  haveI := isDominant_toPartialMap_hom f
  have hFs' : F.source ≤ f.toPartialMap.domain := hFs
  have hGs' : G.source ≤ g.toPartialMap.domain := hGs
  rw [comp_toRationalMap_eq f.toPartialMap g.toPartialMap (O := F.source) F.dense_source hFs'
    (F.iso.hom ≫ (Y.isoOfEq e).hom ≫ Y.homOfLE hGs') (by
      rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.isoOfEq_hom_ι]
      exact hF)]
  change (F.trans' G e).toPartialMap.toRationalMap = _
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change (F.iso.hom ≫ (Y.isoOfEq e).hom ≫ G.iso.hom) ≫ G.target.ι =
    (X.isoOfEq rfl).hom ≫ ((F.iso.hom ≫ (Y.isoOfEq e).hom ≫ Y.homOfLE hGs') ≫
      g.iso.hom ≫ g.target.ι)
  simp [hG]
  rfl

private theorem toRationalMap_trans [IsIntegral X] [Nonempty Y] (f : X.PartialIso Y)
    (g : Y.PartialIso Z) [f.toRationalMap.IsDominant] :
    (f.trans g).toRationalMap = f.toRationalMap.comp g.toRationalMap := by
  have hV := f.dense_target.inter_of_isOpen_right g.dense_source g.source.2
  haveI := isDominant_toPartialMap_hom f
  exact toRationalMap_trans'_eq f g _ _ rfl (restrictTarget_source_le f _ hV inf_le_left)
    inf_le_right (restrictTarget_iso_hom_ι f _ hV inf_le_left)
    (restrictSource_iso_hom_ι g _ hV inf_le_right)

private theorem isDominant_toRationalMap (e : X.PartialIso Y) : e.toRationalMap.IsDominant := by
  have := isDominant_toPartialMap_hom e
  infer_instance

private theorem isDominant_of_isBirational {X Y : Scheme.{u}} {φ : X.RationalMap Y}
    (hφ : RationalMap.IsBirational φ) : φ.IsDominant := by
  obtain ⟨e, rfl⟩ := hφ
  have := isDominant_toPartialMap_hom e
  infer_instance

private theorem toRationalMap_ι_comp {X Z : Scheme.{u}} {U : X.Opens} (hU : Dense (U : Set X))
    (q : X ⟶ Z) :
    (⟨U, hU, U.ι ≫ q⟩ : X.PartialMap Z).toRationalMap = q.toRationalMap := by
  change _ = q.toPartialMap.toRationalMap
  rw [← Scheme.PartialMap.restrict_toRationalMap q.toPartialMap U hU le_top]
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change U.ι ≫ q = (X.isoOfEq rfl).hom ≫ (X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom ≫ q)
  simp [Scheme.topIso_hom]

/-- A birational map followed by its inverse is the identity. -/
private theorem comp_eq_id_of_isInverse {X Y : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    {f : X.RationalMap Y} [f.IsDominant] {h : Y.RationalMap X}
    (H : RationalMap.IsInverse f h) : f.comp h = Scheme.RationalMap.id X := by
  obtain ⟨e, rfl, rfl⟩ := H
  have := isDominant_toPartialMap_hom e
  rw [comp_toRationalMap_eq e.toPartialMap e.symm.toPartialMap (O := e.source) e.dense_source le_rfl
    e.iso.hom (by
      change e.iso.hom ≫ e.target.ι = X.homOfLE le_rfl ≫ e.iso.hom ≫ e.target.ι
      rw [Scheme.homOfLE_rfl, Category.id_comp])]
  have : (⟨e.source, e.dense_source, e.iso.hom ≫ e.symm.toPartialMap.hom⟩ : X.PartialMap X) =
      ⟨e.source, e.dense_source, e.source.ι ≫ 𝟙 X⟩ := by
    congr 1
    change e.iso.hom ≫ e.iso.inv ≫ e.source.ι = _
    simp
  exact (congrArg Scheme.PartialMap.toRationalMap this).trans (toRationalMap_ι_comp _ (𝟙 X))

/-- The composite `e⁻¹ ∘ e` of a partial isomorphism with its inverse represents the identity. -/
private theorem toRationalMap_symm_trans_self [IsIntegral X] [Nonempty Y] (e : Y.PartialIso X) :
    (e.symm.trans e).toRationalMap = Scheme.RationalMap.id X := by
  haveI := isDominant_toRationalMap e.symm
  rw [toRationalMap_trans]
  exact comp_eq_id_of_isInverse ⟨e.symm, rfl, rfl⟩

private theorem comp_eq_comp_of_eq {X Y Z : Scheme.{u}} [IrreducibleSpace X] [Nonempty Y]
    {f f' : X.RationalMap Y} [f.IsDominant] [f'.IsDominant] (h : f = f') (g : Y.RationalMap Z) :
    f.comp g = f'.comp g := by
  subst h; rfl

/-- If `e ∘ k = id`, then `k` is the rational map of `e⁻¹`. -/
private theorem symm_toRationalMap_eq_of_comp_eq_id {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (e : X.PartialIso Y) {k : Y.RationalMap X}
    [e.toRationalMap.IsDominant] (hk : e.toRationalMap.comp k = Scheme.RationalMap.id X) :
    e.symm.toRationalMap = k := by
  haveI := isDominant_toRationalMap e.symm
  haveI := isDominant_toRationalMap e.symm.symm
  calc e.symm.toRationalMap = e.symm.toRationalMap.comp (Scheme.RationalMap.id X) :=
        (Scheme.RationalMap.comp_id _).symm
    _ = e.symm.toRationalMap.comp (e.toRationalMap.comp k) := by rw [hk]
    _ = (e.symm.toRationalMap.comp e.toRationalMap).comp k :=
        (Scheme.RationalMap.comp_assoc _ _ _).symm
    _ = (Scheme.RationalMap.id Y).comp k :=
        comp_eq_comp_of_eq (comp_eq_id_of_isInverse ⟨e.symm, rfl, rfl⟩) k
    _ = k := Scheme.RationalMap.id_comp k

/-- `φ_i ∘ φ_j⁻¹` is the inverse of `φ_j ∘ φ_i⁻¹`. -/
private theorem toRationalMap_symm_trans_symm {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (eᵢ : X.PartialIso Y) (eⱼ : X.PartialIso Z) :
    (eᵢ.symm.trans eⱼ).symm.toRationalMap = (eⱼ.symm.trans eᵢ).toRationalMap := by
  haveI := isDominant_toRationalMap eᵢ
  haveI := isDominant_toRationalMap eᵢ.symm
  haveI := isDominant_toRationalMap eⱼ
  haveI := isDominant_toRationalMap eⱼ.symm
  haveI := isDominant_toRationalMap (eᵢ.symm.trans eⱼ)
  haveI := isDominant_toRationalMap (eⱼ.symm.trans eᵢ)
  have hj : eⱼ.toRationalMap.comp eⱼ.symm.toRationalMap = Scheme.RationalMap.id X :=
    comp_eq_id_of_isInverse ⟨eⱼ, rfl, rfl⟩
  have hi : eᵢ.symm.toRationalMap.comp eᵢ.toRationalMap = Scheme.RationalMap.id Y :=
    comp_eq_id_of_isInverse ⟨eᵢ.symm, rfl, rfl⟩
  refine symm_toRationalMap_eq_of_comp_eq_id _ ?_
  calc (eᵢ.symm.trans eⱼ).toRationalMap.comp (eⱼ.symm.trans eᵢ).toRationalMap
      = (eᵢ.symm.toRationalMap.comp eⱼ.toRationalMap).comp
          (eⱼ.symm.toRationalMap.comp eᵢ.toRationalMap) := by
        simp only [toRationalMap_trans]
    _ = eᵢ.symm.toRationalMap.comp ((eⱼ.toRationalMap.comp eⱼ.symm.toRationalMap).comp
          eᵢ.toRationalMap) := by
        simp only [Scheme.RationalMap.comp_assoc]
    _ = Scheme.RationalMap.id Y := by
        simp only [hj, Scheme.RationalMap.id_comp, hi]

/-- **Transport of partial isomorphisms along a birational map.** If `e₁`, `e₂` represent
`φ₁ ∘ Ψ`, `φ₂ ∘ Ψ` for a birational map `Ψ : Y ⤏ X`, then there are partial isomorphisms
`f₁`, `f₂` representing `φ₁`, `φ₂` with `f₂ ∘ f₁⁻¹ = e₂ ∘ e₁⁻¹` as rational maps. -/
private theorem exists_partialIso_trans_eq {X Y Z₁ Z₂ : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z₁] [IsIntegral Z₂] (Ψ : Y.RationalMap X) [Ψ.IsDominant]
    (hh : ∃ eh : Y.PartialIso X, eh.toRationalMap = Ψ)
    (φ₁ : X.RationalMap Z₁) (φ₂ : X.RationalMap Z₂) (e₁ : Y.PartialIso Z₁)
    (e₂ : Y.PartialIso Z₂) (he₁ : e₁.toRationalMap = Ψ.comp φ₁)
    (he₂ : e₂.toRationalMap = Ψ.comp φ₂) :
    ∃ (f₁ : X.PartialIso Z₁) (f₂ : X.PartialIso Z₂), f₁.toRationalMap = φ₁ ∧
      f₂.toRationalMap = φ₂ ∧
        (f₁.symm.trans f₂).toRationalMap = (e₁.symm.trans e₂).toRationalMap := by
  obtain ⟨eh, heh⟩ := hh
  haveI := isDominant_toRationalMap eh
  haveI := isDominant_toRationalMap eh.symm
  haveI := isDominant_toRationalMap eh.symm.symm
  haveI := isDominant_toRationalMap e₁
  haveI := isDominant_toRationalMap e₁.symm
  haveI := isDominant_toRationalMap e₁.symm.symm
  haveI := isDominant_toRationalMap e₂
  have hcomp : ∀ {W : Scheme.{u}} (e : Y.PartialIso W) (φ : X.RationalMap W),
      e.toRationalMap = Ψ.comp φ → (eh.symm.trans e).toRationalMap = φ := by
    intro W e φ he
    have h1 : eh.symm.toRationalMap.comp eh.toRationalMap = Scheme.RationalMap.id X :=
      comp_eq_id_of_isInverse ⟨eh.symm, rfl, rfl⟩
    rw [toRationalMap_trans, he, ← comp_eq_comp_of_eq heh φ, ← Scheme.RationalMap.comp_assoc]
    simp only [h1, Scheme.RationalMap.id_comp]
  refine ⟨eh.symm.trans e₁, eh.symm.trans e₂, hcomp e₁ φ₁ he₁, hcomp e₂ φ₂ he₂, ?_⟩
  haveI := isDominant_toRationalMap (eh.symm.trans e₁)
  haveI := isDominant_toRationalMap (eh.symm.trans e₁).symm
  haveI := isDominant_toRationalMap (e₁.symm.trans eh)
  have hehe : eh.toRationalMap.comp eh.symm.toRationalMap = Scheme.RationalMap.id Y :=
    comp_eq_id_of_isInverse ⟨eh, rfl, rfl⟩
  have hsymm := toRationalMap_symm_trans_symm eh e₁
  calc ((eh.symm.trans e₁).symm.trans (eh.symm.trans e₂)).toRationalMap
      = (eh.symm.trans e₁).symm.toRationalMap.comp (eh.symm.trans e₂).toRationalMap :=
        toRationalMap_trans _ _
    _ = (e₁.symm.trans eh).toRationalMap.comp (eh.symm.trans e₂).toRationalMap :=
        comp_eq_comp_of_eq hsymm _
    _ = (e₁.symm.toRationalMap.comp eh.toRationalMap).comp
          (eh.symm.toRationalMap.comp e₂.toRationalMap) := by
        simp only [toRationalMap_trans]
    _ = e₁.symm.toRationalMap.comp ((eh.toRationalMap.comp eh.symm.toRationalMap).comp
          e₂.toRationalMap) := by
        simp only [Scheme.RationalMap.comp_assoc]
    _ = (e₁.symm.trans e₂).toRationalMap := by
        simp only [hehe, Scheme.RationalMap.id_comp, toRationalMap_trans]

end PartialIso

/-! ### Reflexivity of the equivalence of nef models -/

/-- A nef weak model is equivalent to itself, through `e⁻¹ ∘ e` for any partial isomorphism `e`
representing it. -/
private theorem exists_isNefModelEquivalent_self {X S Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ]
    {πX : X ⟶ S} {πZ : Z ⟶ S} {K : Divisor X} {B : RDivisor X} {φ : X.RationalMap Z}
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hφ : IsNefWeakModel sX sZ sS πX πZ K B φ) :
    ∃ (e e' : X.PartialIso Z), e.toRationalMap = φ ∧ e'.toRationalMap = φ ∧
      IsNefModelEquivalent sZ sZ sS πZ πZ
        (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ B)
        (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ B)
        (e.symm.trans e').toRationalMap := by
  obtain ⟨e, he⟩ := hφ.isBirational
  haveI : IsSeparated sS := (instIsProperVarietyOfIsProjectiveVariety ℂ sS).toIsProper.toIsSeparated
  haveI := isDominant_of_isBirational hφ.isBirational
  refine ⟨e, e, he, he, ?_⟩
  refine (IsNefWeakModel.eq_of_isRCartierPullback_and_isNefModelEquivalent hφ hφ).2 _ ?_
  rw [toRationalMap_symm_trans_self, Scheme.RationalMap.comp_id]

/-! ### The hypotheses, bundled -/

/-- A reflexive and symmetric relation on `ℕ` such that every subsequence has two distinct
related terms has a finite set of representatives. -/
private theorem exists_finset_of_forall_exists_ne {R : ℕ → ℕ → Prop} (hrefl : ∀ i, R i i)
    (hsymm : ∀ i j, R i j → R j i)
    (hsub : ∀ σ : ℕ → ℕ, StrictMono σ → ∃ m n, m ≠ n ∧ R (σ m) (σ n)) :
    ∃ F : Finset ℕ, ∀ i, ∃ j ∈ F, R i j := by
  classical
  by_cases hinf : ∀ F : Finset ℕ, {i | ∀ j ∈ F, ¬ R i j}.Infinite
  · exfalso
    choose g hg using fun (F : Finset ℕ) (N : ℕ) => (hinf F).exists_gt N
    let P : ℕ → Finset ℕ := fun n => Nat.rec ∅ (fun _ Q => insert (g Q (Q.sup id)) Q) n
    let a : ℕ → ℕ := fun n => g (P n) ((P n).sup id)
    have hPsucc : ∀ n, P (n + 1) = insert (a n) (P n) := fun n => rfl
    have hmem : ∀ m n, m < n → a m ∈ P n := by
      intro m n hmn
      induction n with
      | zero => exact absurd hmn (Nat.not_lt_zero _)
      | succ n ih =>
        rw [hPsucc]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with h | h
        · exact Finset.mem_insert_of_mem (ih h)
        · exact h ▸ Finset.mem_insert_self _ _
    have hmono : StrictMono a := by
      intro m n hmn
      have h1 : a m ≤ (P n).sup id := Finset.le_sup (f := id) (hmem m n hmn)
      exact lt_of_le_of_lt h1 (hg (P n) ((P n).sup id)).2
    have hbad : ∀ m n, m < n → ¬ R (a n) (a m) := fun m n hmn =>
      (hg (P n) ((P n).sup id)).1 _ (hmem m n hmn)
    obtain ⟨m, n, hmn, hR⟩ := hsub a hmono
    rcases lt_or_gt_of_ne hmn with h | h
    · exact hbad m n h (hsymm _ _ hR)
    · exact hbad n m h hR
  · push Not at hinf
    obtain ⟨F₀, hF₀⟩ := hinf
    have hfin : {i | ∀ j ∈ F₀, ¬ R i j}.Finite := hF₀
    refine ⟨F₀ ∪ hfin.toFinset, fun i => ?_⟩
    by_cases hi : ∀ j ∈ F₀, ¬ R i j
    · exact ⟨i, Finset.mem_union_right _ (hfin.mem_toFinset.mpr hi), hrefl i⟩
    · push Not at hi
      obtain ⟨j, hj, hR⟩ := hi
      exact ⟨j, Finset.mem_union_left _ hj, hR⟩

section Data

variable {S : Scheme.{0}} (sS : S ⟶ Spec (.of ℂ))

/-- On some common projective resolution `p : W ⟶ Y`, `q : W ⟶ Z` of the kind in
`MMP.Fourfold.IsNefWeakModel`, the comparison `p^*(K_Y + C) - q^*(K_Z + φ_* C)` has coefficient
zero at the strict transform of every prime divisor `P` of `Y` with `Q P`. -/
private def HasComparison {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (sY : Y ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) (KY : Divisor Y) (C : RDivisor Y) (φ : Y.RationalMap Z)
    (Q : MMP.Mori.PrimeDivisor Y → Prop) : Prop :=
  ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
    (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
    (h : Y.RationalMap W),
    MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ = sW ∧
      IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
      IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
      h.compHom q = φ ∧
      ∃ GY GZ : RDivisor W,
        MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KY C) GY ∧
        MMP.Flips.IsRCartierPullback q
          (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ KY)
            (MMP.Mori.RationalMap.transformDivisor φ C)) GZ ∧
        ∀ P, Q P → ∃ P' : MMP.Mori.PrimeDivisor W,
          MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧ (GY - GZ).coeff P' = 0

private theorem HasComparison.mono {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sY : Y ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {KY : Divisor Y} {C : RDivisor Y} {φ : Y.RationalMap Z}
    {Q Q' : MMP.Mori.PrimeDivisor Y → Prop} (h : HasComparison sY sZ KY C φ Q)
    (hQ : ∀ P, Q' P → Q P) : HasComparison sY sZ KY C φ Q' := by
  obtain ⟨W, h1, h2, h3, sW, p, q, g, hW1, hW2, hW3, hW4, hW5, hW6, hW7, hW8, hW9, hW10, GY, GZ,
    hGY, hGZ, hP⟩ := h
  exact ⟨W, h1, h2, h3, sW, p, q, g, hW1, hW2, hW3, hW4, hW5, hW6, hW7, hW8, hW9, hW10, GY, GZ,
    hGY, hGZ, fun P hP' => hP P (hQ P hP')⟩

/-- The hypotheses of the theorem on a sequence of boundaries `C_i → B` on `Y` with nef weak
models `φ_i : Y ⤏ Z_i`. -/
private structure IsComparisonData {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ)) (πY : Y ⟶ S) (KY : Divisor Y)
    (F : Finset (MMP.Mori.PrimeDivisor Y)) (C : ℕ → RDivisor Y) (B : RDivisor Y)
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, Y.RationalMap (Z i)) : Prop where
  hY : MMP.Mori.IsProjectiveVariety ℂ sY
  hYQ : IsQFactorial sY
  hdim : topologicalKrullDim Y = 3
  hS : MMP.Mori.IsProjectiveVariety ℂ sS
  hπY : πY ≫ sS = sY
  hC : ∀ i, IsRealTerminalPair sY (C i)
  hB : IsRealTerminalPair sY B
  hF : ∀ i P, P ∈ F ↔ 0 < (C i).coeff P
  hlim : ∀ P, Tendsto (fun i => (C i).coeff P) atTop (𝓝 (B.coeff P))
  hφ : ∀ i, IsNefWeakModel sY (sZ i) sS πY (πZ i) KY (C i) (φ i)
  hZQ : ∀ i, IsQFactorial (sZ i)
  hcomp : ∀ i, HasComparison sY (sZ i) KY (C i) (φ i) (· ∈ F)

/-- The models of the indices `i` and `j` are equivalent through `φ_j ∘ φ_i⁻¹`. -/
private def ModelRel {Y : Scheme.{0}} (KY : Divisor Y) (C : ℕ → RDivisor Y)
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, Y.RationalMap (Z i)) (i j : ℕ) : Prop :=
  ∃ (eᵢ : Y.PartialIso (Z i)) (eⱼ : Y.PartialIso (Z j)),
    eᵢ.toRationalMap = φ i ∧ eⱼ.toRationalMap = φ j ∧
    IsNefModelEquivalent (sZ i) (sZ j) sS (πZ i) (πZ j)
      (MMP.Mori.RationalMap.transformDivisor (φ i) KY)
      (MMP.Mori.RationalMap.transformDivisor (φ i) (C i))
      (MMP.Mori.RationalMap.transformDivisor (φ j) KY)
      (MMP.Mori.RationalMap.transformDivisor (φ j) (C j))
      (eᵢ.symm.trans eⱼ).toRationalMap

/-- The statement proved by induction on `d`: a sequence whose differences `C_i - B` span a
space of dimension at most `d` has two equivalent models. -/
private def HasEquivalentPair (d : ℕ) : Prop :=
  ∀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (πY : Y ⟶ S) (KY : Divisor Y)
    (F : Finset (MMP.Mori.PrimeDivisor Y)) (C : ℕ → RDivisor Y) (B : RDivisor Y)
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, Y.RationalMap (Z i)),
    IsComparisonData sS sY πY KY F C B sZ πZ φ →
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => C i - B)) ≤ d →
    ∃ i j, i ≠ j ∧ ModelRel sS KY C sZ πZ φ i j

variable {sS}

section Lemmas

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {πY : Y ⟶ S} {KY : Divisor Y}
  {F : Finset (MMP.Mori.PrimeDivisor Y)} {C : ℕ → RDivisor Y} {B : RDivisor Y}
  {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
  [∀ i, IsNormal (Z i)] {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)} [∀ i, QuasiCompact (sZ i)]
  {πZ : ∀ i, Z i ⟶ S} {φ : ∀ i, Y.RationalMap (Z i)}

/-- The models of `i` and `j` are equivalent if those of `j` and `i` are. -/
private theorem ModelRel.symm (hS : MMP.Mori.IsProjectiveVariety ℂ sS) {i j : ℕ}
    (h : ModelRel sS KY C sZ πZ φ i j) : ModelRel sS KY C sZ πZ φ j i := by
  obtain ⟨eᵢ, eⱼ, hi, hj, hE⟩ := h
  haveI : IsSeparated sS :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sS).toIsProper.toIsSeparated
  exact ⟨eⱼ, eᵢ, hj, hi, (isNefModelEquivalent_equivalence_and_refinement (k := ℂ)).2.1 _ _ sS
    _ _ _ _ _ _ _ _ hE ⟨eᵢ.symm.trans eⱼ, rfl, toRationalMap_symm_trans_symm eᵢ eⱼ⟩⟩

/-- The model of `i` is equivalent to itself. -/
private theorem modelRel_self (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hφ : ∀ i, IsNefWeakModel sY (sZ i) sS πY (πZ i) KY (C i) (φ i)) (i : ℕ) :
    ModelRel sS KY C sZ πZ φ i i :=
  exists_isNefModelEquivalent_self hS (hφ i)

/-- Off `F` the boundaries vanish. -/
private theorem IsComparisonData.coeff_eq_zero (hD : IsComparisonData sS sY πY KY F C B sZ πZ φ)
    (i : ℕ) {P : MMP.Mori.PrimeDivisor Y} (hP : P ∉ F) : (C i).coeff P = 0 := by
  by_contra h
  exact hP ((hD.hF i P).mpr ((hD.hC i).1.2.1 P h).1)

/-- Off `F` the limit boundary vanishes. -/
private theorem IsComparisonData.coeff_limit_eq_zero
    (hD : IsComparisonData sS sY πY KY F C B sZ πZ φ) {P : MMP.Mori.PrimeDivisor Y}
    (hP : P ∉ F) : B.coeff P = 0 :=
  tendsto_nhds_unique (hD.hlim P) (by simp only [hD.coeff_eq_zero _ hP]; exact tendsto_const_nhds)

/-- The differences `C_i - B` are supported on `F`. -/
private theorem IsComparisonData.span_le_supported
    (hD : IsComparisonData sS sY πY KY F C B sZ πZ φ) :
    Submodule.span ℝ (Set.range fun i => C i - B) ≤
      Finsupp.supported ℝ ℝ (↑F : Set (MMP.Mori.PrimeDivisor Y)) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Finsupp.mem_supported]
  intro P hP
  by_contra hPF
  apply Finsupp.mem_support_iff.mp hP
  have h1 := hD.coeff_eq_zero i hPF
  have h2 := hD.coeff_limit_eq_zero hPF
  rw [DivisorWithCoeffs.coeff_apply] at h1 h2
  rw [Finsupp.sub_apply, h1, h2, sub_zero]

private theorem finiteDimensional_supported (F : Finset (MMP.Mori.PrimeDivisor Y)) :
    FiniteDimensional ℝ (Finsupp.supported ℝ ℝ (↑F : Set (MMP.Mori.PrimeDivisor Y))) :=
  Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := ℝ) (R := ℝ)
    (↑F : Set (MMP.Mori.PrimeDivisor Y))).symm

/-- A subsequence satisfies the hypotheses again. -/
private theorem IsComparisonData.comp_strictMono
    (hD : IsComparisonData sS sY πY KY F C B sZ πZ φ) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    IsComparisonData sS sY πY KY F (fun i => C (σ i)) B (Z := fun i => Z (σ i))
      (fun i => sZ (σ i)) (fun i => πZ (σ i)) (fun i => φ (σ i)) where
  hY := hD.hY
  hYQ := hD.hYQ
  hdim := hD.hdim
  hS := hD.hS
  hπY := hD.hπY
  hC i := hD.hC (σ i)
  hB := hD.hB
  hF i := hD.hF (σ i)
  hlim P := (hD.hlim P).comp hσ.tendsto_atTop
  hφ i := hD.hφ (σ i)
  hZQ i := hD.hZQ (σ i)
  hcomp i := hD.hcomp (σ i)

/-- The span of the differences of a subsequence is no larger. -/
private theorem IsComparisonData.finrank_comp_le
    (hD : IsComparisonData sS sY πY KY F C B sZ πZ φ) (σ : ℕ → ℕ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => C (σ i) - B)) ≤
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => C i - B)) := by
  haveI := finiteDimensional_supported F
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range fun i => C i - B)) :=
    Submodule.finiteDimensional_of_le hD.span_le_supported
  refine Submodule.finrank_mono (Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨σ i, rfl⟩

end Lemmas

variable (sS)

end Data

/-! ### Directions on a sphere and a transverse hyperplane -/

/-- **Cutting radial segments by a transverse hyperplane.** Let `u_n` be unit vectors of a
subspace `V` of `ℝ^ι` (sup norm) and `r > 0`. Along a subsequence `u_{σ n}` there are lengths
`0 < λ_n < r` such that the points `λ_n u_{σ n}` converge to a point `v` of norm `< r` and
the differences `λ_n u_{σ n} - v` span a space of dimension `< dim V`: if `u_{σ n} → w`, the
points lie on the hyperplane `ℓ(x) = a` of a functional `ℓ` with `ℓ(w) > 0`. -/
private theorem exists_strictMono_hyperplane {ι : Type*} [Fintype ι] (V : Submodule ℝ (ι → ℝ))
    (u : ℕ → ι → ℝ) (hu1 : ∀ n, ‖u n‖ = 1) (huV : ∀ n, u n ∈ V) {r : ℝ} (hr : 0 < r) :
    ∃ (σ : ℕ → ℕ) (_ : StrictMono σ) (l : ℕ → ℝ) (v : ι → ℝ),
      (∀ n, 0 < l n ∧ l n < r) ∧ ‖v‖ < r ∧
      Tendsto (fun n => l n • u (σ n)) atTop (𝓝 v) ∧
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun n => l n • u (σ n) - v)) <
        Module.finrank ℝ V := by
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_sphere (0 : ι → ℝ) 1).tendsto_subseq
    (x := u) fun n => by simp [hu1 n]
  have hw1 : ‖w‖ = 1 := by simpa using hw
  have hwV : w ∈ V := (Submodule.closed_of_finiteDimensional V).mem_of_tendsto hlim
    (Eventually.of_forall fun n => huV _)
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw1
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (funext h)
  set ℓ : (ι → ℝ) →ₗ[ℝ] ℝ := w j • LinearMap.proj j with hℓ
  have hℓapp : ∀ y, ℓ y = w j * y j := fun y => by simp [hℓ]
  set q := ℓ w with hq
  have hqpos : 0 < q := by rw [hq, hℓapp]; exact mul_self_pos.mpr hj
  have hℓlim : Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 q) := by
    have : Continuous fun y : ι → ℝ => w j * y j := by fun_prop
    simp_rw [hℓapp]
    exact (this.tendsto w).comp hlim
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hℓlim.eventually (lt_mem_nhds (half_lt_self hqpos)))
  set σ : ℕ → ℕ := fun n => φ (n + N) with hσ
  have hσm : StrictMono σ := fun a b hab => hφ (by omega)
  set a := r * q / 4 with ha
  have hapos : 0 < a := by positivity
  have hℓσ : ∀ n, q / 2 < ℓ (u (σ n)) := fun n => hN _ (by omega)
  have hℓσpos : ∀ n, 0 < ℓ (u (σ n)) := fun n => lt_trans (by positivity) (hℓσ n)
  set l : ℕ → ℝ := fun n => a / ℓ (u (σ n)) with hl
  set v : ι → ℝ := (a / q) • w with hv
  refine ⟨σ, hσm, l, v, fun n => ⟨div_pos hapos (hℓσpos n), ?_⟩, ?_, ?_, ?_⟩
  · rw [hl, div_lt_iff₀ (hℓσpos n)]
    have := hℓσ n
    rw [ha]; nlinarith
  · rw [hv, norm_smul, hw1, mul_one, Real.norm_eq_abs, abs_of_pos (div_pos hapos hqpos), ha]
    rw [div_lt_iff₀ hqpos]; nlinarith
  · have h1 : Tendsto (fun n => u (σ n)) atTop (𝓝 w) :=
      hlim.comp (tendsto_add_atTop_nat N)
    have h2 : Tendsto (fun n => ℓ (u (σ n))) atTop (𝓝 q) :=
      hℓlim.comp (tendsto_add_atTop_nat N)
    exact ((tendsto_const_nhds (x := a)).div h2 hqpos.ne').smul h1
  · set W := V ⊓ LinearMap.ker ℓ
    have hle : Submodule.span ℝ (Set.range fun n => l n • u (σ n) - v) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      refine ⟨V.sub_mem (V.smul_mem _ (huV _)) (V.smul_mem _ hwV), ?_⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hl, hv]
      rw [← hq, div_mul_cancel₀ _ (hℓσpos n).ne', div_mul_cancel₀ _ hqpos.ne', sub_self]
    have hlt : W < V := by
      refine lt_of_le_of_ne inf_le_left fun h => ?_
      have : w ∈ W := h ▸ hwV
      exact hqpos.ne' (LinearMap.mem_ker.mp this.2)
    exact lt_of_le_of_lt (Submodule.finrank_mono hle) (Submodule.finrank_lt_finrank_of_lt hlt)

/-! ### Coefficient vectors on a finite set of primes -/

section Coefficients

variable {Y : Scheme.{0}} (F : Finset (MMP.Mori.PrimeDivisor Y))

/-- The real divisor `∑_{P ∈ F} y_P P` of a coefficient vector `y ∈ ℝ^F`. -/
private noncomputable def ofCoeffs : (F → ℝ) →ₗ[ℝ] RDivisor Y :=
  ∑ P : F, (Finsupp.lsingle (P : MMP.Mori.PrimeDivisor Y)).comp (LinearMap.proj P)

private theorem ofCoeffs_apply (y : F → ℝ) :
    ofCoeffs F y = ∑ P : F, Finsupp.single (P : MMP.Mori.PrimeDivisor Y) (y P) := by
  simp [ofCoeffs]

open Classical in
private theorem coeff_ofCoeffs (y : F → ℝ) (P : MMP.Mori.PrimeDivisor Y) :
    (ofCoeffs F y).coeff P = if hP : P ∈ F then y ⟨P, hP⟩ else 0 := by
  rw [ofCoeffs_apply, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  split_ifs with hP
  · rw [Finset.sum_eq_single ⟨P, hP⟩ (fun Q _ hQ => by
        rw [Finsupp.single_apply, if_neg fun h => hQ (Subtype.ext h)])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  · exact Finset.sum_eq_zero fun Q _ => by
      rw [Finsupp.single_apply,
        if_neg fun h : (Q : MMP.Mori.PrimeDivisor Y) = P => hP (h ▸ Q.2)]

private theorem coeff_ofCoeffs_of_mem (y : F → ℝ) (P : F) :
    (ofCoeffs F y).coeff P = y P := by
  rw [coeff_ofCoeffs, dif_pos P.2]

private theorem coeff_ofCoeffs_of_notMem (y : F → ℝ) {P : MMP.Mori.PrimeDivisor Y} (hP : P ∉ F) :
    (ofCoeffs F y).coeff P = 0 := by
  rw [coeff_ofCoeffs, dif_neg hP]

private theorem ofCoeffs_coeff {D : RDivisor Y} (hD : ∀ P, P ∉ F → D.coeff P = 0) :
    ofCoeffs F (fun P => D.coeff P) = D := by
  refine Finsupp.ext fun P => ?_
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply, coeff_ofCoeffs]
  split_ifs with hP
  · rfl
  · exact (hD P hP).symm

private theorem ofCoeffs_injective : Function.Injective (ofCoeffs F) := by
  intro x y h
  funext P
  have := congrArg (fun D : RDivisor Y => D.coeff P) h
  simpa only [coeff_ofCoeffs_of_mem] using this

end Coefficients

/-- A positive function on a finite type is bounded below by a positive constant. -/
private theorem exists_pos_forall_lt_of_pos {ι : Type*} [Finite ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ δ > 0, ∀ i, δ < f i := by
  cases isEmpty_or_nonempty ι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀ / 2, half_pos (hf i₀), fun i => lt_of_lt_of_le (half_lt_self (hf i₀)) (hi₀ i)⟩

/-- **Terminality is open on a fixed support**
(`MMP.Fourfold.eventually_isRealKltPair_and_isRealTerminalPair`): near a terminal coefficient
vector `b`, every nonnegative coefficient vector is terminal. -/
private theorem exists_pos_forall_isRealTerminalPair {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYQ : IsQFactorial sY)
    (F : Finset (MMP.Mori.PrimeDivisor Y)) (b : F → ℝ)
    (hb : IsRealTerminalPair sY (ofCoeffs F b)) :
    ∃ ρ > 0, ∀ y : F → ℝ, 0 ≤ y → dist y b < ρ → IsRealTerminalPair sY (ofCoeffs F y) := by
  have hev := (eventually_isRealKltPair_and_isRealTerminalPair sY
    (IsProjectiveVariety.isQuasiProjectiveVariety ℂ _) hYQ
    (fun P : F => (P : MMP.Mori.PrimeDivisor Y)) b).2 (by rwa [← ofCoeffs_apply])
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨ρ, hρ, fun y hy hyb => ?_⟩
  rw [ofCoeffs_apply]
  exact hball ⟨Metric.mem_ball.mpr hyb, hy⟩

/-! ### Terminal pairs are klt -/

section Klt

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The log discrepancy of a prime divisor `P` of `X` with respect to `B` with `K + B`
`ℝ`-Cartier is `1 - coeff_P B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor [CompactSpace X] (hX : IsNormalVariety ℂ sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX P)
      (1 - B.coeff P) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) (hC i)
  have hC'P : ∀ i, (C' i).coeff P = (C i).coeff P := fun i =>
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) P P rfl (hC i) (hC' i)
  have hord : (DivisorOver.ofPrimeDivisor ℂ hX P).ordPullback ω = P.ordForm ω :=
    DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P ω
  have hsumΓ : ∀ Γ, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ := fun Γ => by
    rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
  refine ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C,
    C', hC, hsumΓ, fun i => ⟨_, hC' i⟩, ?_⟩
  change 1 - B.coeff P = 1 + ((DivisorOver.ofPrimeDivisor ℂ hX P).ordPullback ω : ℝ) -
    ∑ i, r i * ((C' i).coeff P : ℝ)
  simp_rw [hC'P, hord]
  rw [← hsumΓ P]
  ring

/-- The coefficients of a real canonical boundary are less than one. -/
private theorem coeff_lt_one_of_isRealTerminalPair {B : RDivisor X} (hB : IsRealTerminalPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P < 1 := by
  by_cases h : B.coeff P = 0
  · rw [h]; exact one_pos
  · exact (hB.1.2.1 P h).2

/-- The coefficients of a real canonical boundary are nonnegative. -/
private theorem coeff_nonneg_of_isRealTerminalPair {B : RDivisor X} (hB : IsRealTerminalPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : 0 ≤ B.coeff P := by
  by_cases h : B.coeff P = 0
  · rw [h]
  · exact (hB.1.2.1 P h).1.le

/-- **A real terminal pair is klt**: exceptional divisors have log discrepancy `> 1`, and a
non-exceptional divisor has the valuation of a prime divisor `P` of `X`, with log discrepancy
`1 - coeff_P B > 0`. -/
private theorem isRealKltPair_of_isRealTerminalPair [CompactSpace X] {B : RDivisor X}
    (hB : IsRealTerminalPair sX B) : IsRealKltPair sX B := by
  have hlt := coeff_lt_one_of_isRealTerminalPair hB
  obtain ⟨⟨hX, -, ⟨n, K, hK, hKB⟩, -⟩, hterm⟩ := hB
  refine ⟨hX, hlt, ⟨n, K, hK, hKB⟩, fun m E a ha => ?_⟩
  by_cases hE : E.IsExceptional
  · linarith [hterm m E a hE ha]
  · obtain ⟨P, hP⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX E hE
    have h1 := isLogDiscrepancy_ofPrimeDivisor hX hK hKB P
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha h1 hP]
    linarith [hlt P]

/-- **Rational null-decomposition data exist** for a real klt boundary on a projective
`ℚ`-factorial variety. -/
private theorem nonempty_rationalNullData [CompactSpace X] (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hQ : IsQFactorial sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : RDivisor X} (hB0 : ∀ P, 0 ≤ B.coeff P) (hB : IsRealKltPair sX B) :
    Nonempty (RationalNullData sX K B) := by
  have hB0' : 0 ≤ B := fun P => by
    simpa only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_zero, Pi.zero_apply] using hB0 P
  obtain ⟨s, Bs, r, m, E, hE, hklt, hhull, hr, hr1, hm, hsum, hEm, -⟩ :=
    exists_convexCombination_isKltPair_of_isRealKltPair sX hX hQ K hK B hB0' hB
  refine ⟨RationalNullData.mk hQ hX ⟨n, hK⟩ hB0 hB s Bs (fun i P => (hklt i).1.nonneg P) hklt
    hhull r hr hr1 ?_ m hm fun i => ⟨E i, hE i, fun P => ?_⟩⟩
  · simp_rw [smul_add] at hsum
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, hr1, one_smul] at hsum
    exact add_left_cancel hsum
  · have := congrArg (fun D : QDivisor X => D P) (hEm i)
    simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at this
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply]
    exact this.symm

end Klt

/-! ### Strict transforms of prime divisors through generic points -/

section Transforms

/-- The strict transform of a prime divisor `P` under `Φ` is the prime divisor whose generic point
is the image of `η_P` under a representative of `Φ` defined at `η_P`. -/
private theorem transformPrimeDivisor_eq_some_iff_of_mem_domain {X Z : Scheme.{u}} [IsReduced X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {Φ : X.RationalMap Z} (g : X.PartialMap Z)
    (hg : g.toRationalMap = Φ) (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g.domain)
    (Q : MMP.Mori.PrimeDivisor Z) :
    MMP.Mori.RationalMap.transformPrimeDivisor Φ P = some Q ↔
      Q.genericPoint = g.hom ⟨P.genericPoint, hP⟩ := by
  refine ⟨fun h => MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g hg hP,
    fun hQ => MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
      ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g, hP, hg⟩, ?_⟩⟩
  have h1 : MMP.Mori.RationalMap.transform Φ P.idealSheaf.support = Q.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g hg P hP, ← hQ]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure Q).symm
  have := Q.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- The composite `a ∘ b` of partial maps has a representative defined at every point `x` of the
domain of `a` with `a(x)` in the domain of `b`, with value `b(a(x))`. -/
private theorem exists_rep_comp_apply {X Y Z : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    (a : X.PartialMap Y) [IsDominant a.hom] (b : Y.PartialMap Z) {x : X} (hx : x ∈ a.domain)
    (hax : a.hom ⟨x, hx⟩ ∈ b.domain) :
    ∃ c : X.PartialMap Z, c.toRationalMap = a.toRationalMap.comp b.toRationalMap ∧
      ∃ hxc : x ∈ c.domain, c.hom ⟨x, hxc⟩ = b.hom ⟨a.hom ⟨x, hx⟩, hax⟩ := by
  let O : X.Opens := a.domain.ι ''ᵁ a.hom ⁻¹ᵁ b.domain
  have hO : Dense (O : Set X) := (a.comp b).dense_domain
  have hOf : O ≤ a.domain := (Scheme.Hom.image_le_opensRange _ _).trans (by simp)
  let β : O.toScheme ⟶ b.domain.toScheme :=
    (Scheme.Hom.isoImage a.domain.ι (a.hom ⁻¹ᵁ b.domain)).inv ≫ a.hom ∣_ b.domain
  have key2 : (Scheme.Hom.isoImage a.domain.ι (a.hom ⁻¹ᵁ b.domain)).inv ≫
      (a.hom ⁻¹ᵁ b.domain).ι = X.homOfLE hOf := by
    rw [← cancel_mono a.domain.ι, Category.assoc, ← Scheme.Hom.isoImage_hom_ι,
      Iso.inv_hom_id_assoc, Scheme.homOfLE_ι]
  have hβ : β ≫ b.domain.ι = X.homOfLE hOf ≫ a.hom := by
    show ((Scheme.Hom.isoImage a.domain.ι (a.hom ⁻¹ᵁ b.domain)).inv ≫ a.hom ∣_ b.domain) ≫
      b.domain.ι = _
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, key2]
  have hxO : x ∈ O := ⟨⟨x, hx⟩, hax, rfl⟩
  let pt : O.toScheme := ⟨x, hxO⟩
  have h4 : X.homOfLE hOf pt = ⟨x, hx⟩ := by
    apply a.domain.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    rfl
  have h2 : β pt = ⟨a.hom ⟨x, hx⟩, hax⟩ := by
    apply b.domain.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply, h4]
    rfl
  refine ⟨⟨O, hO, β ≫ b.hom⟩, (comp_toRationalMap_eq a b hO hOf β hβ).symm, hxO, ?_⟩
  exact (Scheme.Hom.comp_apply β b.hom pt).trans (congrArg b.hom h2)

/-- Linear extensions of partial maps on prime divisors agree on a divisor when the maps agree on
its support. -/
private theorem mapPrimeDivisors_congr {X Y : Scheme.{u}} {R : Type*} [AddCommMonoid R]
    {φ φ' : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} (h : ∀ P, D P ≠ 0 → φ P = φ' P) :
    DivisorWithCoeffs.mapPrimeDivisors φ D = DivisorWithCoeffs.mapPrimeDivisors φ' D := by
  classical
  simp only [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply]
  exact Finsupp.sum_congr fun P hP => by rw [h P (Finsupp.mem_support_iff.mp hP)]

/-- Linear extensions of partial maps on prime divisors compose. -/
private theorem mapPrimeDivisors_mapPrimeDivisors_eq {X Y T : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (χ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (ξ : MMP.Mori.PrimeDivisor Y → Option (MMP.Mori.PrimeDivisor T))
    (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors ξ (DivisorWithCoeffs.mapPrimeDivisors χ D) =
      DivisorWithCoeffs.mapPrimeDivisors (fun G => (χ G).bind ξ) D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, map_add, hD, hD']
  | single G r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases χ G with _ | D'
    · simp
    · simp [DivisorWithCoeffs.mapPrimeDivisors_single]

/-- **Transforms along a step of a program.** Let `f : X ⟶ V` and `u : X' ⟶ V` be proper
birational morphisms onto a normal scheme, `ψ : X' ⤏ X` the map with `f ∘ ψ = u`, and `Φ : X ⤏ Z`
a map defined in codimension one. For a divisor `D` of `X` supported off the exceptional set of
`f`, the transform of the strict transform `u⁻¹_* f_* D` along `Φ ∘ ψ` is the transform of `D`
along `Φ`. -/
private theorem transformDivisor_comp_flipTransform {X X' V Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsSeparated (V ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)]
    (f : X ⟶ V) (u : X' ⟶ V) [IsProper f] [IsProper u] (hf : IsBirationalMorphism f)
    (hu : IsBirationalMorphism u) (ψ : X'.RationalMap X) [ψ.IsDominant]
    (hψ : ψ.compHom f = u.toRationalMap) (Φ : X.RationalMap Z)
    (hΦ : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Φ.domain) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X)
    (hD : ∀ E : MMP.Mori.PrimeDivisor X, D E ≠ 0 → f E.genericPoint ∈ biregularLocus f) :
    MMP.Mori.RationalMap.transformDivisor (ψ.comp Φ) (flipTransform f u D) =
      MMP.Mori.RationalMap.transformDivisor Φ D := by
  classical
  haveI := hf.isDominant
  haveI := hu.isDominant
  have hus : Function.Surjective u := fun y => by
    rw [← Set.mem_range, ← u.isClosedMap.isClosed_range.closure_eq, u.denseRange.closure_range]
    trivial
  change DivisorWithCoeffs.mapPrimeDivisors _ (DivisorWithCoeffs.mapPrimeDivisors _
    (DivisorWithCoeffs.mapPrimeDivisors _ D)) = DivisorWithCoeffs.mapPrimeDivisors _ D
  rw [mapPrimeDivisors_mapPrimeDivisors_eq, mapPrimeDivisors_mapPrimeDivisors_eq]
  refine mapPrimeDivisors_congr fun P hP => ?_
  -- the point `y = f(η_P)` of codimension one of `V`
  have hy := hD P hP
  have hcy : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hy]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  set Q₀ : MMP.Mori.PrimeDivisor V := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcy
  have hQ₀ : Q₀.genericPoint = f P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcy
  have htf : MMP.Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap P = some Q₀ :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q₀).mpr hQ₀.symm
  -- its strict transform on `X'`
  have hyu : f P.genericPoint ∈ biregularLocus u :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal u hu hcy.le
  obtain ⟨x', hx'⟩ := hus (f P.genericPoint)
  have hcx' : Order.coheight x' = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus u (by rw [hx']; exact hyu), hx', hcy]
  set P' : MMP.Mori.PrimeDivisor X' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hcx'
  have hP' : P'.genericPoint = x' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcx'
  have hinv : MMP.Mori.inverseTransformPrimeDivisor u Q₀ = some P' :=
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (by rw [hP', hx', hQ₀]) (by rw [hP', hx']; exact hyu)
  -- `ψ` sends `η_{P'}` to `η_P`
  have hdom : P'.genericPoint ∈ ψ.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one u f ψ hψ
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
  obtain ⟨a, haP, ha⟩ := Scheme.RationalMap.mem_domain.mp hdom
  haveI : IsDominant a.hom :=
    (Scheme.PartialMap.isDominant_toRationalMap_iff a).mp (ha ▸ inferInstance)
  have hval : f (a.hom ⟨P'.genericPoint, haP⟩) = f P.genericPoint := by
    have h := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
      (g := a.compHom f) (g' := u.toPartialMap)
      (by rw [Scheme.RationalMap.compHom_toRationalMap, ha, hψ]) haP
      (trivial : P'.genericPoint ∈ (⊤ : X'.Opens))
    have e1 : (a.compHom f).hom ⟨P'.genericPoint, haP⟩ = f (a.hom ⟨P'.genericPoint, haP⟩) :=
      Scheme.Hom.comp_apply _ _ _
    have e2 : u.toPartialMap.hom ⟨P'.genericPoint, trivial⟩ = u P'.genericPoint :=
      (Scheme.Hom.comp_apply _ _ _).trans (by rw [Scheme.topIso_hom]; rfl)
    exact e1.symm.trans (h.trans (e2.trans (by rw [hP', hx'])))
  have hηP : a.hom ⟨P'.genericPoint, haP⟩ = P.genericPoint := by
    have := Q₀.isDiscreteValuationRing_localRing
    exact MMP.Fourfold.eq_of_map_eq_of_valuationRing hf.functionFieldMap_bijective
      (y := Q₀.genericPoint) (by rw [hval, hQ₀]) hQ₀.symm
  -- a representative of `Φ` at `η_P`, and of the composite at `η_{P'}`
  obtain ⟨b, hbP, hb⟩ := Scheme.RationalMap.mem_domain.mp
    (hΦ P.genericPoint (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le)
  have hab : a.hom ⟨P'.genericPoint, haP⟩ ∈ b.domain := by rw [hηP]; exact hbP
  obtain ⟨c, hcrep', hc, hcval⟩ := exists_rep_comp_apply a b haP hab
  have hcrep : c.toRationalMap = ψ.comp Φ := by
    rw [hcrep']
    subst ha hb
    rfl
  have hfin : MMP.Mori.RationalMap.transformPrimeDivisor (ψ.comp Φ) P' =
      MMP.Mori.RationalMap.transformPrimeDivisor Φ P := by
    refine Option.ext fun Q => ?_
    rw [transformPrimeDivisor_eq_some_iff_of_mem_domain c hcrep P' hc Q,
      transformPrimeDivisor_eq_some_iff_of_mem_domain b hb P hbP Q, hcval]
    have : b.hom ⟨a.hom ⟨P'.genericPoint, haP⟩, hab⟩ = b.hom ⟨P.genericPoint, hbP⟩ :=
      congrArg b.hom (Subtype.ext hηP)
    rw [this]
  rw [htf]
  change (MMP.Mori.inverseTransformPrimeDivisor u Q₀).bind
    (MMP.Mori.RationalMap.transformPrimeDivisor (ψ.comp Φ)) = _
  rw [hinv]
  exact hfin

/-- The strict transform under the inverse of a proper birational morphism `p` onto a normal
scheme of a prime divisor is a prime divisor. -/
private theorem exists_transformPrimeDivisor_eq_some_of_isInverse {W X : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsSeparated (W ↘ ⊤_ Scheme)] [IsSeparated (X ↘ ⊤_ Scheme)] (p : W ⟶ X) [IsProper p]
    (hp : IsBirationalMorphism p) {h : X.RationalMap W}
    (hh : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor W, MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' := by
  obtain ⟨e, he, rfl⟩ := hh
  have hsrc : e.source.ι ≫ p = e.iso.hom ≫ e.target.ι :=
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm
  have hcomp : e.symm.toRationalMap.compHom p = (𝟙 X : X ⟶ X).toRationalMap := by
    rw [← Scheme.RationalMap.compHom_toRationalMap]
    have : e.symm.toPartialMap.compHom p = ⟨e.target, e.dense_target, e.target.ι ≫ 𝟙 X⟩ := by
      change (⟨e.target, e.dense_target, (e.iso.inv ≫ e.source.ι) ≫ p⟩ : X.PartialMap X) = _
      congr 1
      rw [Category.assoc, hsrc, Iso.inv_hom_id_assoc, Category.comp_id]
    rw [this]
    exact toRationalMap_ι_comp _ _
  have hdom : P.genericPoint ∈ e.symm.toRationalMap.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p _ hcomp
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  obtain ⟨g, hgP, hg⟩ := Scheme.RationalMap.mem_domain.mp hdom
  have hpg : p (g.hom ⟨P.genericPoint, hgP⟩) = P.genericPoint := by
    have h := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
      (g := g.compHom p) (g' := (𝟙 X : X ⟶ X).toPartialMap)
      (by rw [Scheme.RationalMap.compHom_toRationalMap, hg, hcomp]) hgP
      (trivial : P.genericPoint ∈ (⊤ : X.Opens))
    have e1 : (g.compHom p).hom ⟨P.genericPoint, hgP⟩ = p (g.hom ⟨P.genericPoint, hgP⟩) :=
      Scheme.Hom.comp_apply _ _ _
    have e2 : (𝟙 X : X ⟶ X).toPartialMap.hom ⟨P.genericPoint, trivial⟩ = P.genericPoint :=
      (Scheme.Hom.comp_apply _ _ _).trans (by rw [Scheme.topIso_hom]; rfl)
    exact e1.symm.trans (h.trans e2)
  have hbir := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal p hp
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  have hco : Order.coheight (g.hom ⟨P.genericPoint, hgP⟩) = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus p (by rw [hpg]; exact hbir), hpg]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (transformPrimeDivisor_eq_some_iff_of_mem_domain g hg P hgP _).mpr
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco)⟩

/-- `(f ∘ g) ∘ h = f ∘ (g ∘ h)` for a morphism `h`. -/
private theorem comp_compHom {X Y Z T : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    (f : X.RationalMap Y) [f.IsDominant] (g : Y.RationalMap Z) (h : Z ⟶ T) :
    (f.comp g).compHom h = f.comp (g.compHom h) := by
  obtain ⟨g, rfl⟩ := g.exists_rep
  rw [Scheme.RationalMap.comp_def, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap, Scheme.RationalMap.comp_def]
  congr 1

/-- `(φ ∘ f) ∘ g = φ ∘ (g ∘ f)` for morphisms `f`, `g`. -/
private theorem compHom_compHom {X Y Z T : Scheme.{u}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

end Transforms

/-! ### Changing the canonical divisors of equivalent nef models -/

section Principal

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]

/-- A principal divisor has intersection number zero with every proper curve. -/
private theorem isRIntersectionNumber_principalDivisor (Γ : ProperCurve sX)
    (φ : (MMP.Mori.RationalFunctions X)ˣ) :
    MMP.Flips.IsRIntersectionNumber ℂ sX (Divisor.toRDivisor (MMP.Mori.principalDivisor φ)) ![1]
      ![MMP.Mori.principalDivisor φ] Γ 0 := by
  have hc := MMP.Mori.Divisor.isCartier_principalDivisor φ
  have h := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX Γ ![1]
    ![MMP.Mori.principalDivisor φ] (fun j => by fin_cases j; exact hc)
  have hdeg : (MMP.Mori.principalDivisor φ).degreeOn ℂ sX Γ.ι Γ.dim_le hc = 0 := by
    have hiso := (MMP.Mori.Divisor.linearlyEquivalent_principalDivisor_zero φ).divisorialSheafIso
    have := hc.isInvertibleModule_divisorialSheaf
    have := (MMP.Mori.Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
    have h1 : (MMP.Mori.principalDivisor φ).degreeOn ℂ sX Γ.ι Γ.dim_le hc =
        (0 : Divisor X).degreeOn ℂ sX Γ.ι Γ.dim_le MMP.Mori.Divisor.isCartier_zero :=
      MMP.Mori.degreeOn_eq_of_iso ℂ sX Γ.ι Γ.dim_le hiso
    rw [h1, MMP.Mori.Divisor.degreeOn_zero' ℂ sX Γ.ι Γ.dim_le]
  simpa [hdeg] using h

/-- Adding a principal divisor does not change which presentations meet a curve in degree zero. -/
private theorem forall_isRIntersectionNumber_eq_zero_add_iff (Γ : ProperCurve sX) (D : RDivisor X)
    (φ : (MMP.Mori.RationalFunctions X)ˣ) :
    (∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sX (D + Divisor.toRDivisor (MMP.Mori.principalDivisor φ))
        r L Γ x → x = 0) ↔
    (∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sX D r L Γ x → x = 0) := by
  have hP := isRIntersectionNumber_principalDivisor Γ φ
  constructor
  · intro h m r L x hx
    have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX Γ).2 _ _ r L ![1]
      ![MMP.Mori.principalDivisor φ] _ 0 1 1 hx hP
    simp only [one_smul, mul_zero, add_zero, one_mul] at hlin
    exact h _ _ _ _ hlin
  · intro h m r L x hx
    have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX Γ).2 _ _ r L ![1]
      ![MMP.Mori.principalDivisor φ] _ 0 1 (-1) hx hP
    simp only [one_smul, mul_zero, add_zero, one_mul, neg_smul, add_neg_cancel_right] at hlin
    exact h _ _ _ _ hlin

/-- Relative nefness is unchanged by adding a principal divisor. -/
private theorem isRelativelyNef_add_principalDivisor {T : Scheme.{0}} (π : X ⟶ T) {D : RDivisor X}
    (hD : MMP.Flips.IsRelativelyNef ℂ sX π D) (φ : (MMP.Mori.RationalFunctions X)ˣ) :
    MMP.Flips.IsRelativelyNef ℂ sX π (D + Divisor.toRDivisor (MMP.Mori.principalDivisor φ)) := by
  obtain ⟨m, r, L, hL, hDe, hnef⟩ := hD
  refine ⟨m + 1, Fin.snoc r 1, Fin.snoc L (MMP.Mori.principalDivisor φ), fun j => ?_, ?_,
    fun Γ hΓ x hx => ?_⟩
  · induction j using Fin.lastCases with
    | last => simpa using MMP.Mori.Divisor.isCartier_principalDivisor φ
    | cast j => simpa using hL j
  · simp [Fin.sum_univ_castSucc, hDe]
  · have h0 := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX Γ r L hL
    rw [← hDe] at h0
    have hlin := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX Γ).2 _ _ r L ![1]
      ![MMP.Mori.principalDivisor φ] _ 0 1 1 h0 (isRIntersectionNumber_principalDivisor Γ φ)
    simp only [one_smul, mul_zero, add_zero, one_mul] at hlin
    rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX Γ).1 _ _ _ _ _ _ _ hx hlin]
    exact hnef Γ hΓ _ h0

end Principal

/-- The pull-back of `D + div(φ)` is the pull-back of `D` plus a principal divisor. -/
private theorem exists_isRCartierPullback_add_principalDivisor {W X : Scheme.{0}} [IsIntegral W]
    [IsIntegral X] [CompactSpace W] [CompactSpace X] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian X] [IsNormal X] (p : W ⟶ X) [IsDominant p] {D : RDivisor X}
    {G : RDivisor W} (hG : MMP.Flips.IsRCartierPullback p D G)
    (φ : (MMP.Mori.RationalFunctions X)ˣ) :
    ∃ φ' : (MMP.Mori.RationalFunctions W)ˣ, MMP.Flips.IsRCartierPullback p
      (D + Divisor.toRDivisor (MMP.Mori.principalDivisor φ))
      (G + Divisor.toRDivisor (MMP.Mori.principalDivisor φ')) := by
  have hφ : ∀ Z : irreducibleComponents W,
      p (componentGenericPoint W Z) ∉ (MMP.Mori.principalDivisor φ).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p _
  refine ⟨MMP.Mori.pullbackRationalFunction p φ hφ, ?_⟩
  obtain ⟨m, r, L, L', hL, hD, hpb, hG⟩ := hG
  refine ⟨m + 1, Fin.snoc r 1, Fin.snoc L (MMP.Mori.principalDivisor φ),
    Fin.snoc L' (MMP.Mori.principalDivisor (MMP.Mori.pullbackRationalFunction p φ hφ)),
    fun j => ?_, ?_, fun j => ?_, ?_⟩
  · induction j using Fin.lastCases with
    | last => simpa using MMP.Mori.Divisor.isCartier_principalDivisor φ
    | cast j => simpa using hL j
  · simp [Fin.sum_univ_castSucc, hD]
  · induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact ⟨hφ, MMP.Mori.Divisor.isPullback_principalDivisor φ hφ⟩
    | cast j =>
      simp only [Fin.snoc_castSucc]
      exact hpb j
  · simp [Fin.sum_univ_castSucc, hG]

/-- **Equivalence of nef models does not depend on the canonical divisors.** Canonical divisors of
a normal variety differ by principal divisors, which pull back to principal divisors, of degree
zero on every curve. -/
private theorem IsNefModelEquivalent.of_isCanonicalDivisor {Z₁ Z₂ S : Scheme.{0}} [IsIntegral Z₁]
    [IsLocallyNoetherian Z₁] [IsNormal Z₁] [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
    {s₁ : Z₁ ⟶ Spec (.of ℂ)} {s₂ : Z₂ ⟶ Spec (.of ℂ)} [QuasiCompact s₁] [QuasiCompact s₂]
    {sS : S ⟶ Spec (.of ℂ)} {π₁ : Z₁ ⟶ S} {π₂ : Z₂ ⟶ S} {K₁ K₁' : Divisor Z₁}
    {C₁ : RDivisor Z₁} {K₂ K₂' : Divisor Z₂} {C₂ : RDivisor Z₂} {ψ : Z₁.RationalMap Z₂}
    (E : IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ)
    (h₁ : ∃ m : ℕ, K₁'.IsCanonicalDivisor s₁ m) (h₂ : ∃ m : ℕ, K₂'.IsCanonicalDivisor s₂ m) :
    IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁' C₁ K₂' C₂ ψ := by
  haveI : CompactSpace Z₁ := QuasiCompact.compactSpace_of_compactSpace s₁
  haveI : CompactSpace Z₂ := QuasiCompact.compactSpace_of_compactSpace s₂
  obtain ⟨m₁, hK₁'⟩ := h₁
  obtain ⟨m₂, hK₂'⟩ := h₂
  obtain ⟨n₁, hK₁⟩ := E.isCanonicalDivisor₁
  obtain ⟨n₂, hK₂⟩ := E.isCanonicalDivisor₂
  obtain ⟨φ₁, hφ₁⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor s₁
    E.isNormalVariety₁ hK₁' hK₁
  obtain ⟨φ₂, hφ₂⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor s₂
    E.isNormalVariety₂ hK₂' hK₂
  have e₁ : MMP.Flips.logCanonicalDivisor K₁' C₁ = MMP.Flips.logCanonicalDivisor K₁ C₁ +
      Divisor.toRDivisor (MMP.Mori.principalDivisor φ₁) := by
    rw [MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, ← hφ₁, map_sub]; abel
  have e₂ : MMP.Flips.logCanonicalDivisor K₂' C₂ = MMP.Flips.logCanonicalDivisor K₂ C₂ +
      Divisor.toRDivisor (MMP.Mori.principalDivisor φ₂) := by
    rw [MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, ← hφ₂, map_sub]; abel
  obtain ⟨W, i1, i2, i3, sW, i4, p₁, p₂, h, hW, hWs, hp₁s, hp₂s, hp₁, hp₂, hb₁, hb₂, hinv, hcomp,
    D₁, D₂, hD₁, hD₂, hcurve⟩ := E.exists_resolution
  haveI := hb₁.isDominant
  haveI := hb₂.isDominant
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨φ₁', hD₁'⟩ := exists_isRCartierPullback_add_principalDivisor p₁ hD₁ φ₁
  obtain ⟨φ₂', hD₂'⟩ := exists_isRCartierPullback_add_principalDivisor p₂ hD₂ φ₂
  refine ⟨E.isNormalVariety₁, E.isProjectiveVariety₁, E.comp_eq₁, ⟨m₁, hK₁'⟩, ?_,
    E.isNormalVariety₂, E.isProjectiveVariety₂, E.comp_eq₂, ⟨m₂, hK₂'⟩, ?_, E.isBirational,
    E.isOver, W, i1, i2, i3, sW, i4, p₁, p₂, h, hW, hWs, hp₁s, hp₂s, hp₁, hp₂, hb₁, hb₂, hinv,
    hcomp, D₁ + Divisor.toRDivisor (MMP.Mori.principalDivisor φ₁'),
    D₂ + Divisor.toRDivisor (MMP.Mori.principalDivisor φ₂'), by rw [e₁]; exact hD₁',
    by rw [e₂]; exact hD₂', fun Γ hΓ => ?_⟩
  · rw [e₁]; exact isRelativelyNef_add_principalDivisor π₁ E.isRelativelyNef₁ φ₁
  · rw [e₂]; exact isRelativelyNef_add_principalDivisor π₂ E.isRelativelyNef₂ φ₂
  · rw [forall_isRIntersectionNumber_eq_zero_add_iff (sX := sW) Γ D₁ φ₁',
      forall_isRIntersectionNumber_eq_zero_add_iff (sX := sW) Γ D₂ φ₂']
    exact hcurve Γ hΓ

/-! ### The induction -/

section Induction

variable {S : Scheme.{0}} (sS : S ⟶ Spec (.of ℂ))

/-- **Two models of the same boundary are equivalent** (`lem_fourfold_two_weak_models_crepant`). -/
private theorem modelRel_of_eq {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {πY : Y ⟶ S} {KY : Divisor Y} {C : ℕ → RDivisor Y}
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)} [∀ i, QuasiCompact (sZ i)]
    {πZ : ∀ i, Z i ⟶ S} {φ : ∀ i, Y.RationalMap (Z i)}
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hφ : ∀ i, IsNefWeakModel sY (sZ i) sS πY (πZ i) KY (C i) (φ i)) {i j : ℕ}
    (hij : C i = C j) : ModelRel sS KY C sZ πZ φ i j := by
  haveI : IsSeparated sS :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sS).toIsProper.toIsSeparated
  obtain ⟨eᵢ, heᵢ⟩ := (hφ i).isBirational
  obtain ⟨eⱼ, heⱼ⟩ := (hφ j).isBirational
  haveI := isDominant_of_isBirational (hφ i).isBirational
  haveI := isDominant_toRationalMap eᵢ
  haveI := isDominant_toRationalMap eᵢ.symm
  have h₂ : IsNefWeakModel sY (sZ j) sS πY (πZ j) KY (C i) (φ j) := hij ▸ hφ j
  have hcomp : (φ i).comp (eᵢ.symm.trans eⱼ).toRationalMap = φ j := by
    rw [comp_eq_comp_of_eq heᵢ.symm, toRationalMap_trans]
    calc eᵢ.toRationalMap.comp (eᵢ.symm.toRationalMap.comp eⱼ.toRationalMap)
        = (eᵢ.toRationalMap.comp eᵢ.symm.toRationalMap).comp eⱼ.toRationalMap :=
          (Scheme.RationalMap.comp_assoc _ _ _).symm
      _ = (Scheme.RationalMap.id Y).comp eⱼ.toRationalMap :=
          comp_eq_comp_of_eq (comp_eq_id_of_isInverse ⟨eᵢ, rfl, rfl⟩) _
      _ = φ j := by rw [Scheme.RationalMap.id_comp, heⱼ]
  refine ⟨eᵢ, eⱼ, heᵢ, heⱼ, ?_⟩
  rw [← hij]
  exact (IsNefWeakModel.eq_of_isRCartierPullback_and_isNefModelEquivalent (hφ i) h₂).2 _ hcomp

/-- **The nef case, with all boundaries distinct from the limit.** -/
private theorem exists_ne_modelRel_of_forall_ne (d : ℕ)
    (IH : ∀ d' < d, HasEquivalentPair sS d')
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (πY : Y ⟶ S) (KY : Divisor Y)
    (F : Finset (MMP.Mori.PrimeDivisor Y)) (C : ℕ → RDivisor Y) (B : RDivisor Y)
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, Y.RationalMap (Z i))
    [QuasiCompact sY] (hD : IsComparisonData sS sY πY KY F C B sZ πZ φ)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY πY (MMP.Flips.logCanonicalDivisor KY B))
    (hne : ∀ i, C i ≠ B)
    (hd : Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => C i - B)) ≤ d) :
    ∃ i j, i ≠ j ∧ ModelRel sS KY C sZ πZ φ i j := by
  classical
  have hS := hD.hS
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsSeparated sS :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sS).toIsProper.toIsSeparated
  /- The canonical divisor of the threefold `Y`. -/
  have hK3 : KY.IsCanonicalDivisor sY 3 := by
    obtain ⟨m, hm⟩ := (hD.hφ 0).isCanonicalDivisor
    have h := hm.topologicalKrullDim_eq
    rw [hD.hdim] at h
    obtain rfl : m = 3 := by exact_mod_cast h.symm
    exact hm
  have hB0 : ∀ P, 0 ≤ B.coeff P := coeff_nonneg_of_isRealTerminalPair hD.hB
  /- Rational null-decomposition data for `B` and the radial constant `ε`. -/
  obtain ⟨ν⟩ := nonempty_rationalNullData hD.hY hD.hYQ hK3 hB0
    (isRealKltPair_of_isRealTerminalPair hD.hB)
  obtain ⟨τ, hτ, hrad⟩ := exists_pos_forall_isNefWeakModel_of_isNefWeakModel
  set ε := τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) with hε
  have hτ0 := hτ ν.s ν.weight ν.m
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by rw [hε, div_lt_one (by positivity)]; linarith
  /- Coefficient vectors on `F`. -/
  set b : F → ℝ := fun P => B.coeff P with hb
  set c : ℕ → F → ℝ := fun i P => (C i).coeff P with hc
  have hCι : ∀ i, ofCoeffs F (c i) = C i := fun i =>
    ofCoeffs_coeff F fun P hP => hD.coeff_eq_zero i hP
  have hBι : ofCoeffs F b = B := ofCoeffs_coeff F fun P hP => hD.coeff_limit_eq_zero hP
  have hb0 : ∀ P, 0 ≤ b P := fun P => hB0 P
  have hc0 : ∀ i P, 0 ≤ c i P := fun i P => coeff_nonneg_of_isRealTerminalPair (hD.hC i) P
  have hcpos : ∀ i (P : F), 0 < c i P := fun i P => (hD.hF i P).mp P.2
  have hclim : Tendsto c atTop (𝓝 b) := tendsto_pi_nhds.mpr fun P => hD.hlim P
  have hcne : ∀ i, c i ≠ b := fun i h => hne i (by rw [← hCι, ← hBι, h])
  /- The radius `ρ`: terminality within `ρ₀`, and `ρ` below every positive coefficient. -/
  obtain ⟨ρ₀, hρ₀, hterm⟩ :=
    exists_pos_forall_isRealTerminalPair hD.hY hD.hYQ F b (hBι ▸ hD.hB)
  obtain ⟨δ, hδ, hδb⟩ := exists_pos_forall_lt_of_pos
    (fun P : F => if 0 < b P then b P else 1) fun P => by split_ifs with h <;> simp [h]
  set ρ := min (ρ₀ / 2) δ with hρdef
  have hρ : 0 < ρ := lt_min (half_pos hρ₀) hδ
  have hρρ₀ : ρ < ρ₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ₀)
  have hρb : ∀ P, 0 < b P → ρ < b P := fun P hP => by
    have := hδb P
    rw [if_pos hP] at this
    exact lt_of_le_of_lt (min_le_right _ _) this
  /- Directions, radii and the boundaries `A_i` on the sphere of radius `ρ`. -/
  set nrm : ℕ → ℝ := fun i => ‖c i - b‖ with hnrmdef
  have hnrm : ∀ i, 0 < nrm i := fun i => norm_pos_iff.mpr (sub_ne_zero.mpr (hcne i))
  set u : ℕ → F → ℝ := fun i => (nrm i)⁻¹ • (c i - b) with hudef
  set t : ℕ → ℝ := fun i => nrm i / ρ with htdef
  set A : ℕ → F → ℝ := fun i => b + ρ • u i with hAdef
  have hu1 : ∀ i, ‖u i‖ = 1 := fun i => by
    rw [hudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hnrm i).ne']
  have hdec : ∀ i, c i = (1 - t i) • b + t i • A i := fun i => by
    have : t i * ρ * (nrm i)⁻¹ = 1 := by
      rw [htdef, div_mul_cancel₀ _ hρ.ne', mul_inv_cancel₀ (hnrm i).ne']
    funext P
    simp only [hAdef, hudef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    linear_combination (-(c i P - b P)) * this
  have hA0 : ∀ i P, 0 ≤ A i P := fun i P => by
    simp only [hAdef, hudef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    rcases (hb0 P).lt_or_eq with hpos | hzero
    · have h1 : |(nrm i)⁻¹ * (c i P - b P)| ≤ 1 := by
        have := norm_le_pi_norm (u i) P
        rw [hu1 i, Real.norm_eq_abs] at this
        simpa only [hudef, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] using this
      have h2 := neg_abs_le ((nrm i)⁻¹ * (c i P - b P))
      have := hρb P hpos
      nlinarith
    · rw [← hzero, sub_zero]
      have := hc0 i P
      have := inv_pos.mpr (hnrm i)
      positivity
  have hAdist : ∀ i, dist (A i) b < ρ₀ := fun i => by
    rw [dist_eq_norm, hAdef, add_sub_cancel_left, norm_smul, hu1 i, mul_one, Real.norm_eq_abs,
      abs_of_pos hρ]
    exact hρρ₀
  have hAterm : ∀ i, IsRealTerminalPair sY (ofCoeffs F (A i)) := fun i =>
    hterm _ (fun P => hA0 i P) (hAdist i)
  have ht0 : ∀ i, 0 < t i := fun i => div_pos (hnrm i) hρ
  have htlim : Tendsto t atTop (𝓝 0) := by
    have h1 : Tendsto nrm atTop (𝓝 0) := by
      simpa [hnrmdef] using (hclim.sub_const b).norm
    simpa using h1.div_const ρ
  obtain ⟨L, hL⟩ := eventually_atTop.mp (htlim.eventually (gt_mem_nhds hε0))
  /- The radial interval lemma along the late indices. -/
  have hCdec : ∀ i, C i = (1 - t i) • B + t i • ofCoeffs F (A i) := fun i => by
    rw [← hCι, hdec, map_add, map_smul, map_smul, hBι]
  have hrad_i : ∀ i, L ≤ i →
      (∀ s : ℝ, 0 < s → s < ε →
        IsNefWeakModel sY (sZ i) sS πY (πZ i) KY ((1 - s) • B + s • ofCoeffs F (A i)) (φ i) ∧
        HasComparison sY (sZ i) KY ((1 - s) • B + s • ofCoeffs F (A i)) (φ i)
          (fun P => 0 < ((1 - s) • B + s • ofCoeffs F (A i)).coeff P)) ∧
      (∀ s s' : ℝ, 0 < s → s < ε → 0 < s' → s' < ε →
        IsNefModelEquivalent (sZ i) (sZ i) sS (πZ i) (πZ i)
          (MMP.Mori.RationalMap.transformDivisor (φ i) KY)
          (MMP.Mori.RationalMap.transformDivisor (φ i) ((1 - s) • B + s • ofCoeffs F (A i)))
          (MMP.Mori.RationalMap.transformDivisor (φ i) KY)
          (MMP.Mori.RationalMap.transformDivisor (φ i) ((1 - s') • B + s' • ofCoeffs F (A i)))
          (𝟙 (Z i) : Z i ⟶ Z i).toRationalMap) := fun i hi => by
    have hφi := hD.hφ i
    have hci := hD.hcomp i
    rw [hCdec i] at hφi hci
    exact hrad sY sS (sZ i) πY (πZ i) hD.hY hD.hYQ hD.hS hD.hπY hK3 hD.hB (hAterm i) hnef ν
      (t i) (ht0 i) (hL i hi) (φ i) hφi (hD.hZQ i)
      (hci.mono fun P hP => (hD.hF i P).mpr (by rwa [hCdec i]))
  /- Compactness of the sphere and a transverse hyperplane. -/
  set V := Submodule.span ℝ (Set.range fun i => c i - b) with hVdef
  have huV : ∀ i, u i ∈ V := fun i => V.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨σ', hσ', l, v, hl, hv, hlv, hdim'⟩ := exists_strictMono_hyperplane V
    (fun n => u (n + L)) (fun n => hu1 _) (fun n => huV _) (mul_pos hε0 hρ)
  set σ : ℕ → ℕ := fun n => σ' n + L with hσdef
  have hσ : StrictMono σ := fun a b hab => Nat.add_lt_add_right (hσ' hab) L
  have hσL : ∀ n, L ≤ σ n := fun n => Nat.le_add_left L _
  set sv : ℕ → ℝ := fun n => l n / ρ with hsvdef
  have hs0 : ∀ n, 0 < sv n := fun n => div_pos (hl n).1 hρ
  have hsε : ∀ n, sv n < ε := fun n => by
    rw [hsvdef, div_lt_iff₀ hρ]; exact (hl n).2
  /- The new boundaries `C_n^* = B + λ_n u_{σ n}` and their limit `B^*`. -/
  set cs : ℕ → F → ℝ := fun n => b + l n • u (σ n) with hcsdef
  set bs : F → ℝ := b + v with hbsdef
  have hcs_dec : ∀ n, cs n = (1 - sv n) • b + sv n • A (σ n) := fun n => by
    have : sv n * ρ = l n := by rw [hsvdef, div_mul_cancel₀ _ hρ.ne']
    funext P
    simp only [hcsdef, hAdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(u (σ n) P)) * this
  have hcs0 : ∀ n P, 0 ≤ cs n P := fun n P => by
    rw [hcs_dec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hs0 n
    have := hsε n
    have := hb0 P
    have := hA0 (σ n) P
    nlinarith
  have hlr : ∀ n, l n < ρ := fun n => lt_trans (hl n).2 (by nlinarith)
  have hcs_dist : ∀ n, dist (cs n) b < ρ₀ := fun n => by
    rw [dist_eq_norm, hcsdef, add_sub_cancel_left, norm_smul, hu1, mul_one, Real.norm_eq_abs,
      abs_of_pos (hl n).1]
    exact lt_trans (hlr n) hρρ₀
  have hcs_lim : Tendsto cs atTop (𝓝 bs) := tendsto_const_nhds.add hlv
  have hbs0 : ∀ P, 0 ≤ bs P := fun P =>
    ge_of_tendsto' ((continuous_apply P).tendsto bs |>.comp hcs_lim) fun n => hcs0 n P
  have hbs_dist : dist bs b < ρ₀ := by
    rw [dist_eq_norm, hbsdef, add_sub_cancel_left]
    exact lt_trans hv (lt_trans (by nlinarith) hρρ₀)
  have hcspos : ∀ n (P : F), 0 < cs n P := fun n P => by
    have hcP := hcpos (σ n) P
    rw [hdec] at hcP
    rw [hcs_dec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcP ⊢
    have := hs0 n
    have := hsε n
    have := hb0 P
    have := hA0 (σ n) P
    have := ht0 (σ n)
    have := hL (σ n) (hσL n)
    rcases (hb0 P).lt_or_eq with hbP | hbP
    · nlinarith
    · rw [← hbP] at hcP ⊢
      have : 0 < A (σ n) P := by nlinarith
      nlinarith
  obtain ⟨Cs, hCsdef⟩ : ∃ Cs : ℕ → RDivisor Y, ∀ n, Cs n = ofCoeffs F (cs n) := ⟨_, fun _ => rfl⟩
  obtain ⟨Bs, hBsdef⟩ : ∃ Bs : RDivisor Y, Bs = ofCoeffs F bs := ⟨_, rfl⟩
  have hCs_dec : ∀ n, Cs n = (1 - sv n) • B + sv n • ofCoeffs F (A (σ n)) := fun n => by
    rw [hCsdef, hcs_dec, map_add, map_smul, map_smul, hBι]
  have hFs : ∀ n P, P ∈ F ↔ 0 < (Cs n).coeff P := fun n P => by
    constructor
    · intro hP
      rw [hCsdef, coeff_ofCoeffs, dif_pos hP]
      exact hcspos n ⟨P, hP⟩
    · intro h
      by_contra hP
      rw [hCsdef, coeff_ofCoeffs_of_notMem F _ hP] at h
      exact lt_irrefl _ h
  have hDs : IsComparisonData sS sY πY KY F Cs Bs (Z := fun n => Z (σ n))
      (fun n => sZ (σ n)) (fun n => πZ (σ n)) (fun n => φ (σ n)) := by
    refine ⟨hD.hY, hD.hYQ, hD.hdim, hD.hS, hD.hπY, fun n => ?_, ?_, hFs, fun P => ?_,
      fun n => ?_, fun n => hD.hZQ (σ n), fun n => ?_⟩
    · rw [hCsdef]
      exact hterm _ (fun P => hcs0 n P) (hcs_dist n)
    · rw [hBsdef]
      exact hterm _ hbs0 hbs_dist
    · by_cases hP : P ∈ F
      · simp only [hCsdef, hBsdef, coeff_ofCoeffs, dif_pos hP]
        exact (tendsto_pi_nhds.mp hcs_lim) ⟨P, hP⟩
      · simp only [hCsdef, hBsdef, coeff_ofCoeffs_of_notMem F _ hP]
        exact tendsto_const_nhds
    · rw [hCs_dec n]
      exact ((hrad_i (σ n) (hσL n)).1 (sv n) (hs0 n) (hsε n)).1
    · have h := ((hrad_i (σ n) (hσL n)).1 (sv n) (hs0 n) (hsε n)).2
      rw [← hCs_dec n] at h
      exact h.mono fun P hP => (hFs n P).mp hP
  /- The dimension drops. -/
  have hspan_eq : ∀ (x : ℕ → F → ℝ) (y : F → ℝ),
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun n => ofCoeffs F (x n) - ofCoeffs F y)) =
        Module.finrank ℝ (Submodule.span ℝ (Set.range fun n => x n - y)) := by
    intro x y
    have : (Set.range fun n => ofCoeffs F (x n) - ofCoeffs F y) =
        ofCoeffs F '' Set.range fun n => x n - y := by
      rw [← Set.range_comp]
      simp only [Function.comp_def, map_sub]
    rw [this, Submodule.span_image]
    exact (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective _ (ofCoeffs_injective F) _)).symm
  have hdV : Module.finrank ℝ V ≤ d := by
    rw [hVdef, ← hspan_eq]
    have : (fun n => ofCoeffs F (c n) - ofCoeffs F b) = fun i => C i - B := by
      funext i; rw [hCι, hBι]
    rwa [this]
  have hds : Module.finrank ℝ (Submodule.span ℝ (Set.range fun n => Cs n - Bs)) < d := by
    have hCsfun : (fun n => Cs n - Bs) = fun n => ofCoeffs F (cs n) - ofCoeffs F bs := by
      funext n; rw [hCsdef, hBsdef]
    rw [hCsfun, hspan_eq]
    have : (fun n => cs n - bs) = fun n => l n • u (σ' n + L) - v := by
      funext n
      simp only [hcsdef, hbsdef, hσdef]
      abel
    rw [this]
    exact lt_of_lt_of_le hdim' hdV
  /- Induction, and transitivity through the radial equivalences. -/
  obtain ⟨n, m, hnm, eᵢ, eⱼ, heᵢ, heⱼ, hE⟩ := IH _ hds sY πY KY F Cs Bs _ _ _ hDs le_rfl
  refine ⟨σ n, σ m, hσ.injective.ne hnm, eᵢ, eⱼ, heᵢ, heⱼ, ?_⟩
  have hE1 := (hrad_i (σ n) (hσL n)).2 (t (σ n)) (sv n) (ht0 _) (hL _ (hσL n)) (hs0 n) (hsε n)
  have hE3 := (hrad_i (σ m) (hσL m)).2 (sv m) (t (σ m)) (hs0 m) (hsε m) (ht0 _) (hL _ (hσL m))
  rw [← hCdec, ← hCs_dec] at hE1 hE3
  haveI := isDominant_toRationalMap (eᵢ.symm.trans eⱼ)
  haveI : ((𝟙 (Z (σ n)) : Z (σ n) ⟶ Z (σ n)).toRationalMap).IsDominant :=
    isDominant_of_isBirational MMP.Mori.RationalMap.isBirational_id
  have h12 := ((isNefModelEquivalent_equivalence_and_refinement (k := ℂ)).2.2.1
    inferInstance).2 _ _ _ sS _ _ _ _ _ _ _ _ _ _ _ hE1 hE
  have h123 := ((isNefModelEquivalent_equivalence_and_refinement (k := ℂ)).2.2.1
    inferInstance).2 _ _ _ sS _ _ _ _ _ _ _ _ _ _ _ h12 hE3
  have heq : (((𝟙 (Z (σ n)) : Z (σ n) ⟶ Z (σ n)).toRationalMap).comp
      (eᵢ.symm.trans eⱼ).toRationalMap).comp (𝟙 (Z (σ m)) : Z (σ m) ⟶ Z (σ m)).toRationalMap =
      (eᵢ.symm.trans eⱼ).toRationalMap :=
    (Scheme.RationalMap.comp_id _).trans (Scheme.RationalMap.id_comp _)
  rwa [heq] at h123

/-- **The nef case.** If `K_Y + B` is nef over `S` and the statement holds in every smaller
dimension, a sequence of dimension at most `d` has two equivalent models. -/
private theorem exists_ne_modelRel_of_isRelativelyNef (d : ℕ)
    (IH : ∀ d' < d, HasEquivalentPair sS d')
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (πY : Y ⟶ S) (KY : Divisor Y)
    (F : Finset (MMP.Mori.PrimeDivisor Y)) (C : ℕ → RDivisor Y) (B : RDivisor Y)
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, Y.RationalMap (Z i))
    [QuasiCompact sY] (hD : IsComparisonData sS sY πY KY F C B sZ πZ φ)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sY πY (MMP.Flips.logCanonicalDivisor KY B))
    (hd : Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => C i - B)) ≤ d) :
    ∃ i j, i ≠ j ∧ ModelRel sS KY C sZ πZ φ i j := by
  by_cases hrep : ∃ i j, i ≠ j ∧ C i = C j
  · obtain ⟨i, j, hij, hC⟩ := hrep
    exact ⟨i, j, hij, modelRel_of_eq sS hD.hS hD.hφ hC⟩
  push Not at hrep
  /- At most one boundary equals `B`; pass to the indices after it. -/
  obtain ⟨M, hM⟩ : ∃ M, ∀ i, M ≤ i → C i ≠ B := by
    by_cases h : ∃ i, C i = B
    · obtain ⟨i₀, hi₀⟩ := h
      refine ⟨i₀ + 1, fun i hi hCi => hrep i i₀ (by omega) (hCi.trans hi₀.symm)⟩
    · push Not at h
      exact ⟨0, fun i _ => h i⟩
  have hσ : StrictMono fun n => n + M := fun a b hab => Nat.add_lt_add_right hab M
  obtain ⟨i, j, hij, hR⟩ := exists_ne_modelRel_of_forall_ne sS d IH sY πY KY F _ B _ _ _
    (hD.comp_strictMono hσ) hnef (fun n => hM _ (Nat.le_add_left M n))
    ((hD.finrank_comp_le _).trans hd)
  exact ⟨i + M, j + M, fun h => hij (by omega), hR⟩

/-- A scheme separated over `Spec ℂ` is separated over the terminal scheme. -/
private theorem isSeparated_terminal_of_isSeparated {X : Scheme.{0}} (s : X ⟶ Spec (.of ℂ))
    [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- **Reduction to the nef case.** The program making `K_Y + B` nef keeps the hypotheses and
the models, so the nef case gives two equivalent models in general. -/
private theorem hasEquivalentPair_of_forall_lt (d : ℕ) (IH : ∀ d' < d, HasEquivalentPair sS d') :
    HasEquivalentPair sS d := by
  unfold HasEquivalentPair
  intro Y _ _ _ sY πY KY F C B Z _ _ _ sZ _ πZ φ hD hd
  classical
  have hS := hD.hS
  have hY := hD.hY
  haveI : IsSeparated sS :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sS).toIsProper.toIsSeparated
  haveI : IsProper sY := (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  /- The program making `K_Y + B` nef. -/
  obtain ⟨n, Yi, sYi, hYi1, hYi2, hYi3, hYi4, πYi, KYi, BYi, R, Zi, sZi, f, g, fp, hmodels, hsteps,
    hnef, hdimn, hBn, CY, ψ, hψd, Φ, N, F', hCY, hψ, hΦ0, hΦs, hexc, hCterm, hF', hlim', hZn⟩ :=
    MMP.Fourfold.IsRealTerminalPair.exists_isRelativelyNef_of_tendsto_of_isNefWeakModel hY hS
      hD.hπY hD.hYQ hD.hdim (hD.hφ 0).isCanonicalDivisor hD.hC (fun i P => (hD.hF i P).symm)
      hD.hB hD.hlim hD.hφ hD.hZQ (fun i => by
        obtain ⟨W, i1, i2, i3, sW, p, q, h, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, GY, GZ, hGY,
          hGZ, hP⟩ := hD.hcomp i
        refine ⟨W, i1, i2, i3, sW, p, q, h, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, GY, GZ, hGY,
          hGZ, fun P hPF P' hP' => ?_⟩
        obtain ⟨P'', h1', h2'⟩ := hP P hPF
        rw [h1'] at hP'
        obtain rfl := Option.some.inj hP'
        exact h2')
  haveI := hYi1
  haveI := hYi2
  haveI := hYi3
  haveI := hYi4
  /- The data of each step. -/
  have hstep : ∀ j < n, IsProper (f j) ∧ IsBirationalMorphism (f j) ∧ IsProper (fp j) ∧
      IsBirationalMorphism (fp j) ∧ IsNormalVariety ℂ (sZi j) ∧
      f j ≫ g j = modelMap πY πYi j ∧ fp j ≫ g j = πYi j ∧
      divisorSeq B BYi (j + 1) = flipTransform (f j) (fp j) (divisorSeq B BYi j) := by
    intro j hj
    obtain ⟨-, -, hface, hnegc, hfpg, hcase⟩ := hsteps j hj
    have hfP : IsProper (f j) := hnegc.isContraction.isProper
    rcases hcase with ⟨⟨hfb, -⟩, hiso, -, hBY⟩ | hfl
    · exact ⟨hfP, hfb, inferInstance, MMP.Mori.isBirationalMorphism_of_isIso (fp j),
        hnegc.isNormalVariety_target, hface.comp_eq, hfpg, hBY⟩
    · exact ⟨hfP, hfl.isBirationalMorphism,
        isProper_of_isProjectiveMorphism (fp j) hfl.isProjectiveMorphism_flip,
        hfl.isBirationalMorphism_flip, hnegc.isNormalVariety_target, hface.comp_eq, hfpg,
        hfl.eq_flipTransform⟩
  /- The maps back to `Y` along the program. -/
  have hΨ : ∀ j ≤ n, ∃ (Ψ : (modelSeq Y Yi j).RationalMap Y) (_ : Ψ.IsDominant),
      Ψ.compHom πY = (modelMap πY πYi j).toRationalMap ∧ ∀ i, Φ i j = Ψ.comp (φ i) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨(𝟙 Y : Y ⟶ Y).toRationalMap,
        isDominant_of_isBirational MMP.Mori.RationalMap.isBirational_id,
        Scheme.RationalMap.id_compHom πY,
        fun i => (hΦ0 i).trans (Scheme.RationalMap.id_comp _).symm⟩
    | succ j ih =>
      intro hj
      obtain ⟨Ψ, hΨd, hΨS, hΦΨ⟩ := ih (by omega)
      obtain ⟨-, -, -, -, -, hfg, hfpg, -⟩ := hstep j (by omega)
      haveI := hψd j
      refine ⟨(ψ j).comp Ψ, (inferInstance : ((ψ j).comp Ψ : (Yi j).RationalMap Y).IsDominant),
        ?_, fun i => ?_⟩
      · show ((ψ j).comp Ψ : (Yi j).RationalMap Y).compHom πY = (πYi j).toRationalMap
        rw [comp_compHom, hΨS, Scheme.RationalMap.comp_toRationalMap, ← hfg, ← compHom_compHom,
          hψ j (by omega), ← hfpg]
        rfl
      · rw [hΦs i j (by omega), hΦΨ i]
        exact (Scheme.RationalMap.comp_assoc _ _ _).symm
  /- Separatedness and properness over the base. -/
  have hsepZ : ∀ i, IsSeparated (Z i ↘ ⊤_ Scheme) := fun i => by
    haveI : IsSeparated (sZ i) := (hD.hφ i).isNormalVariety_target.1.toIsSeparated
    exact isSeparated_terminal_of_isSeparated (sZ i)
  have hpropZ : ∀ i, IsProper (πZ i) := fun i => by
    haveI := (hD.hφ i).isProjectiveVariety_target
    haveI : IsProper (sZ i) := (instIsProperVarietyOfIsProjectiveVariety ℂ (sZ i)).toIsProper
    haveI : IsProper (πZ i ≫ sS) := by rw [(hD.hφ i).comp_eq_target]; infer_instance
    exact IsProper.of_comp (f := πZ i) (g := sS)
  /- Transforms of the boundaries along the program. -/
  have hT1 : ∀ i, N ≤ i → ∀ j ≤ n, MMP.Mori.RationalMap.transformDivisor (Φ i j)
      (divisorSeq (C i) (CY i) j) = MMP.Mori.RationalMap.transformDivisor (φ i) (C i) := by
    intro i hi j
    induction j with
    | zero => intro _; rw [hΦ0 i]; rfl
    | succ j ih =>
      intro hj
      obtain ⟨hfP, hfb, hfpP, hfpb, hV, -, -, -⟩ := hstep j (by omega)
      obtain ⟨Ψ, hΨd, hΨS, hΦΨ⟩ := hΨ j (by omega)
      haveI := hψd j
      haveI := hsepZ i
      haveI := hpropZ i
      haveI : IsIntegral (Zi j) := hV.1.toIsIntegral
      haveI : IsNormal (Zi j) := hV.2
      haveI : LocallyOfFiniteType (sZi j) := hV.1.toLocallyOfFiniteType
      haveI : IsLocallyNoetherian (Zi j) := LocallyOfFiniteType.isLocallyNoetherian (sZi j)
      haveI : IsSeparated (sZi j) := hV.1.toIsSeparated
      haveI : IsSeparated (Zi j ↘ ⊤_ Scheme) :=
        isSeparated_terminal_of_isSeparated (sZi j)
      haveI := isDominant_of_isBirational (hD.hφ i).isBirational
      have hov : (φ i).compHom (πZ i) = πY.toRationalMap := (hD.hφ i).isOver
      have hΦdom : ∀ x : modelSeq Y Yi j, Order.coheight x ≤ 1 → x ∈ (Φ i j).domain :=
        fun x hx => MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (modelMap πY πYi j)
          (πZ i) (Φ i j) (by rw [hΦΨ i, comp_compHom, hov, Scheme.RationalMap.comp_toRationalMap,
            hΨS]) hx
      have hDexc : ∀ E : MMP.Mori.PrimeDivisor (modelSeq Y Yi j),
          divisorSeq (C i) (CY i) j E ≠ 0 → f j E.genericPoint ∈ biregularLocus (f j) := by
        intro E hE
        by_contra hnot
        apply hE
        have h1 := hexc i hi j (by omega) E (by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact closure_minimal (Set.singleton_subset_iff.mpr hnot)
            (MMP.Mori.exceptionalSet (f j)).isClosed)
        rwa [DivisorWithCoeffs.coeff_apply] at h1
      rw [hΦs i j (by omega), ← ih (by omega)]
      show MMP.Mori.RationalMap.transformDivisor ((ψ j).comp (Φ i j)) (CY i j) = _
      rw [hCY i j (by omega)]
      exact transformDivisor_comp_flipTransform (f j) (fp j) hfb hfpb (ψ j) (hψ j (by omega))
        (Φ i j) hΦdom _ hDexc
  /- The boundaries along the program are linear images of the original ones. -/
  have hL : ∀ j ≤ n, ∃ L : RDivisor Y →ₗ[ℝ] RDivisor (modelSeq Y Yi j),
      divisorSeq B BYi j = L B ∧ ∀ i, divisorSeq (C i) (CY i) j = L (C i) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨LinearMap.id, rfl, fun i => rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨L, hLB, hLC⟩ := ih (by omega)
      obtain ⟨-, -, -, -, -, -, -, hBY⟩ := hstep j (by omega)
      refine ⟨((MMP.Mori.inverseTransformDivisorₗ ℝ (fp j)).comp
        (MMP.Mori.RationalMap.transformDivisorₗ ℝ (f j).toRationalMap)).comp L, ?_, fun i => ?_⟩
      · rw [hBY, hLB]; rfl
      · show CY i j = _
        rw [hCY i j (by omega), hLC i]
        rfl
  obtain ⟨Ψ, hΨd, -, hΦΨ⟩ := hΨ n le_rfl
  obtain ⟨L, hLB, hLC⟩ := hL n le_rfl
  obtain ⟨hYn, hYnQ, hπn⟩ := hmodels n le_rfl
  haveI : IsProper (modelStr sY sYi n) :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ (modelStr sY sYi n)).toIsProper
  haveI : IsSeparated (modelSeq Y Yi n ↘ ⊤_ Scheme) :=
    isSeparated_terminal_of_isSeparated (modelStr sY sYi n)
  /- The hypotheses on the last model, for the indices after `N`. -/
  have hD' : IsComparisonData sS (modelStr sY sYi n) (modelMap πY πYi n) (divisorSeq KY KYi n) F'
      (fun i => divisorSeq (C (i + N)) (CY (i + N)) n) (divisorSeq B BYi n)
      (Z := fun i => Z (i + N)) (fun i => sZ (i + N)) (fun i => πZ (i + N))
      (fun i => Φ (i + N) n) := {
    hY := hYn
    hYQ := hYnQ
    hdim := hdimn
    hS := hS
    hπY := hπn
    hC i := hCterm _ (by omega)
    hB := hBn
    hF i P := (hF' _ (by omega) P).symm
    hlim P := (hlim' P).comp (tendsto_add_atTop_nat N)
    hφ i := (hZn _ (by omega)).1
    hZQ i := hD.hZQ _
    hcomp i := by
      obtain ⟨W, i1, i2, i3, sW, p, q, h, hW, hWs, hps, hqs, hp, hq, hpb, hqb, hinv, hhq, GY, GZ,
        hGY, hGZ, hP⟩ := (hZn (i + N) (by omega)).2
      haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
      haveI : IsSeparated sW := hW.toIsSeparated
      haveI : IsSeparated (W ↘ ⊤_ Scheme) :=
        isSeparated_terminal_of_isSeparated sW
      refine ⟨W, i1, i2, i3, sW, p, q, h, hW, hWs, hps, hqs, hp, hq, hpb, hqb, hinv, hhq, GY, GZ,
        hGY, hGZ, fun P hPF => ?_⟩
      obtain ⟨P', hP'⟩ := exists_transformPrimeDivisor_eq_some_of_isInverse p hpb hinv P
      exact ⟨P', hP', hP P hPF P' hP'⟩ }
  /- The dimension does not increase. -/
  have hd' : Module.finrank ℝ (Submodule.span ℝ (Set.range fun i =>
      divisorSeq (C (i + N)) (CY (i + N)) n - divisorSeq B BYi n)) ≤ d := by
    have hrange : (Set.range fun i =>
        divisorSeq (C (i + N)) (CY (i + N)) n - divisorSeq B BYi n) =
        L '' Set.range (fun i => C (i + N) - B) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp only [Function.comp_apply, map_sub, hLB, hLC]
    rw [hrange, Submodule.span_image]
    haveI := finiteDimensional_supported F
    haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range fun i => C (i + N) - B)) :=
      Submodule.finiteDimensional_of_le
        (hD.comp_strictMono (σ := fun i => i + N)
          (fun a b h => Nat.add_lt_add_right h N)).span_le_supported
    exact (Submodule.finrank_map_le _ _).trans ((hD.finrank_comp_le (fun i => i + N)).trans hd)
  /- The nef case on the last model. -/
  obtain ⟨i, j, hij, eᵢ, eⱼ, heᵢ, heⱼ, hE⟩ := exists_ne_modelRel_of_isRelativelyNef sS d IH
    (modelStr sY sYi n) (modelMap πY πYi n) (divisorSeq KY KYi n) F' _ (divisorSeq B BYi n)
    (Z := fun i => Z (i + N)) _ _ _ hD' hnef hd'
  dsimp only at heᵢ heⱼ hE
  rw [hT1 (i + N) (by omega) n le_rfl, hT1 (j + N) (by omega) n le_rfl] at hE
  /- Back to `Y`: canonical divisors, and partial isomorphisms. -/
  obtain ⟨eᵢ', eᵢ'', -, -, hEi⟩ := modelRel_self hS hD.hφ (i + N)
  obtain ⟨eⱼ', eⱼ'', -, -, hEj⟩ := modelRel_self hS hD.hφ (j + N)
  have hE2 := IsNefModelEquivalent.of_isCanonicalDivisor hE hEi.isCanonicalDivisor₁
    hEj.isCanonicalDivisor₁
  haveI := isDominant_of_isBirational (hD.hφ (i + N)).isBirational
  have hΨb : ∃ eh : (modelSeq Y Yi n).PartialIso Y, eh.toRationalMap = Ψ := by
    obtain ⟨g₀, hg₀⟩ := (hD.hφ (i + N)).isBirational
    haveI := isDominant_toRationalMap eᵢ
    haveI := isDominant_toRationalMap g₀
    refine ⟨eᵢ.trans g₀.symm, ?_⟩
    calc (eᵢ.trans g₀.symm).toRationalMap = eᵢ.toRationalMap.comp g₀.symm.toRationalMap :=
          toRationalMap_trans _ _
      _ = (Ψ.comp (φ (i + N))).comp g₀.symm.toRationalMap :=
          comp_eq_comp_of_eq (heᵢ.trans (hΦΨ _)) _
      _ = Ψ.comp ((φ (i + N)).comp g₀.symm.toRationalMap) := Scheme.RationalMap.comp_assoc _ _ _
      _ = Ψ.comp (g₀.toRationalMap.comp g₀.symm.toRationalMap) :=
          congrArg (fun t => Ψ.comp t) (comp_eq_comp_of_eq hg₀.symm _)
      _ = Ψ.comp (Scheme.RationalMap.id Y) :=
          congrArg (fun t => Ψ.comp t) (comp_eq_id_of_isInverse ⟨g₀, rfl, rfl⟩)
      _ = Ψ := Scheme.RationalMap.comp_id _
  obtain ⟨fᵢ, fⱼ, hfᵢ, hfⱼ, hff⟩ := exists_partialIso_trans_eq Ψ hΨb (φ (i + N)) (φ (j + N)) eᵢ eⱼ
    (heᵢ.trans (hΦΨ _)) (heⱼ.trans (hΦΨ _))
  exact ⟨i + N, j + N, fun h => hij (by omega), fᵢ, fⱼ, hfᵢ, hfⱼ, by rw [hff]; exact hE2⟩

private theorem hasEquivalentPair (d : ℕ) : HasEquivalentPair sS d := by
  induction d using Nat.strong_induction_on with
  | _ d IH => exact hasEquivalentPair_of_forall_lt sS d IH

end Induction

/-! ### Assembly -/

/-- The theorem. -/
private theorem solution
    {Y S : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {πY : Y ⟶ S}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hπY : πY ≫ sS = sY) (KY : Divisor Y)
    (F : Finset (MMP.Mori.PrimeDivisor Y)) (C : ℕ → RDivisor Y) (B : RDivisor Y)
    (hC : ∀ i, IsRealTerminalPair sY (C i)) (hB : IsRealTerminalPair sY B)
    (hF : ∀ i P, P ∈ F ↔ 0 < (C i).coeff P)
    (hlim : ∀ P, Tendsto (fun i => (C i).coeff P) atTop (𝓝 (B.coeff P)))
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, Y.RationalMap (Z i))
    (hφ : ∀ i, IsNefWeakModel sY (sZ i) sS πY (πZ i) KY (C i) (φ i))
    (hZQ : ∀ i, IsQFactorial (sZ i))
    (hcomp : ∀ i, ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z i)
      (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ i = sW ∧
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
        IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
        h.compHom q = φ i ∧
        ∃ GY GZ : RDivisor W,
          MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KY (C i)) GY ∧
          MMP.Flips.IsRCartierPullback q
            (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (φ i) KY)
              (MMP.Mori.RationalMap.transformDivisor (φ i) (C i))) GZ ∧
          ∀ P ∈ F, ∃ P' : MMP.Mori.PrimeDivisor W,
            MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧ (GY - GZ).coeff P' = 0) :
    ∃ J : Finset ℕ, ∀ i, ∃ j ∈ J, ∃ (eᵢ : Y.PartialIso (Z i)) (eⱼ : Y.PartialIso (Z j)),
      eᵢ.toRationalMap = φ i ∧ eⱼ.toRationalMap = φ j ∧
      IsNefModelEquivalent (sZ i) (sZ j) sS (πZ i) (πZ j)
        (MMP.Mori.RationalMap.transformDivisor (φ i) KY)
        (MMP.Mori.RationalMap.transformDivisor (φ i) (C i))
        (MMP.Mori.RationalMap.transformDivisor (φ j) KY)
        (MMP.Mori.RationalMap.transformDivisor (φ j) (C j))
        (eᵢ.symm.trans eⱼ).toRationalMap := by
  have hD : IsComparisonData sS sY πY KY F C B sZ πZ φ :=
    ⟨hY, hYQ, hdim, hS, hπY, hC, hB, hF, hlim, hφ, hZQ, hcomp⟩
  exact exists_finset_of_forall_exists_ne (R := ModelRel sS KY C sZ πZ φ)
    (modelRel_self hS hφ) (fun i j h => h.symm hS) fun σ hσ =>
      hasEquivalentPair sS _ sY πY KY F _ B _ _ _ (hD.comp_strictMono hσ) (hD.finrank_comp_le σ)

end Proof_thm_fourfold_terminal_comparison_models_finite

end

open CategoryTheory AlgebraicGeometry Filter Topology

namespace MMP.Fourfold

open MMP.Mori

/-- **Finiteness for a convergent terminal comparison sequence.** Let `Y` be a projective
`ℚ`-factorial complex threefold over a projective complex variety `S` (by `π_Y`), with canonical
divisor `K_Y`. Let `C_i` be real terminal boundaries on `Y` with positive support a fixed finite
set `F` of prime divisors, converging coefficientwise to a real terminal boundary `B`. Suppose that
each `(Y, C_i)` has a `ℚ`-factorial nef weak model `φ_i : Y ⤏ Z_i` over `S`
(`MMP.Fourfold.IsNefWeakModel`) and that on a common projective resolution `p : W ⟶ Y`,
`q : W ⟶ Z_i` the comparison `p^*(K_Y + C_i) - q^*(K_{Z_i} + φ_{i*} C_i)` has coefficient zero at
the strict transform of every prime in `F`. Then there is a finite set `J` of indices such that
every model `(Z_i, φ_{i*} C_i)` is equivalent (`MMP.Fourfold.IsNefModelEquivalent`), through
`φ_j ∘ φ_i⁻¹`, to the model `(Z_j, φ_{j*} C_j)` of some `j ∈ J`. -/
@[mmp "thm_fourfold_terminal_comparison_models_finite"]
public theorem finite_isNefModelEquivalent_of_tendsto_isRealTerminalPair
    {Y S : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {πY : Y ⟶ S}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hπY : πY ≫ sS = sY) (KY : Divisor Y)
    (F : Finset (MMP.Mori.PrimeDivisor Y)) (C : ℕ → RDivisor Y) (B : RDivisor Y)
    (hC : ∀ i, IsRealTerminalPair sY (C i)) (hB : IsRealTerminalPair sY B)
    (hF : ∀ i P, P ∈ F ↔ 0 < (C i).coeff P)
    (hlim : ∀ P, Tendsto (fun i => (C i).coeff P) atTop (𝓝 (B.coeff P)))
    {Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, Y.RationalMap (Z i))
    (hφ : ∀ i, IsNefWeakModel sY (sZ i) sS πY (πZ i) KY (C i) (φ i))
    (hZQ : ∀ i, IsQFactorial (sZ i))
    (hcomp : ∀ i, ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z i)
      (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ i = sW ∧
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
        IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
        h.compHom q = φ i ∧
        ∃ GY GZ : RDivisor W,
          MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KY (C i)) GY ∧
          MMP.Flips.IsRCartierPullback q
            (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (φ i) KY)
              (MMP.Mori.RationalMap.transformDivisor (φ i) (C i))) GZ ∧
          ∀ P ∈ F, ∃ P' : MMP.Mori.PrimeDivisor W,
            MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧ (GY - GZ).coeff P' = 0) :
    ∃ J : Finset ℕ, ∀ i, ∃ j ∈ J, ∃ (eᵢ : Y.PartialIso (Z i)) (eⱼ : Y.PartialIso (Z j)),
      eᵢ.toRationalMap = φ i ∧ eⱼ.toRationalMap = φ j ∧
      IsNefModelEquivalent (sZ i) (sZ j) sS (πZ i) (πZ j)
        (MMP.Mori.RationalMap.transformDivisor (φ i) KY)
        (MMP.Mori.RationalMap.transformDivisor (φ i) (C i))
        (MMP.Mori.RationalMap.transformDivisor (φ j) KY)
        (MMP.Mori.RationalMap.transformDivisor (φ j) (C j))
        (eᵢ.symm.trans eⱼ).toRationalMap :=
  Proof_thm_fourfold_terminal_comparison_models_finite.solution hY hYQ hdim hS hπY KY F C B hC hB
    hF hlim sZ πZ φ hφ hZQ hcomp

end MMP.Fourfold
