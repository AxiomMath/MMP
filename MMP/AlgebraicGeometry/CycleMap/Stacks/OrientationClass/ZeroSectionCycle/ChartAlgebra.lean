module

public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
public import MMP.AlgebraicTopology.CapProduct.SupportRetraction
public import MMP.AlgebraicTopology.CapProduct.Restriction
public import MMP.AlgebraicTopology.FundamentalClass.Restriction
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProduct
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.GenericCovering
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartManifold

/-!
# Chart bookkeeping for the zero section cycle (Fulton 19.2(d))

The bundle-free pieces of the proof of Fulton's Lemma 19.2(d): Borel-Moore push-forward and
change-of-degree bookkeeping, the local orientation class of a point, the homeomorphism between
the sources of two embeddings with the same range, and open subsets `O ⊆ X_reg(ℂ)` read as open
subsets of the complex manifold `X_reg(ℂ)` together with their charts.

## Main definitions

* `MMP.homeomorphOfRangeEq`: the homeomorphism `A ≅ B` between the sources of two
  embeddings `A → C`, `B → C` with the same range.
* `MMP.UnderlyingSpace.regularOpensInterHomeomorph`: `O ∩ X_reg(ℂ) ≅ O` for `O ⊆ X_reg(ℂ)`.

## Main results

* `MMP.exists_isLocalOrientationClass_of_eq_zero`: the local orientation class of a point.
* `MMP.pushforward_chain_eq`: two chains of push-forwards with the same composite agree.
* `MMP.pushforward_setCongr_capProductSupport_relMap`: the cap product with a pulled back class,
  read on the preimage of the support.
* `MMP.UnderlyingSpace.restrict_eq_pushforward_regularOpensInterHom`: restriction to an open
  subset of the regular part, through the regular part.
* `MMP.UnderlyingSpace.exists_isAlgebraicChart_of_mem_atlas_regularOpensInter`: the charts of an
  open subset of `V_reg(ℂ)` are restrictions of algebraic charts.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Lemma 19.2(d).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology TopologicalSpace
open MMP.UnderlyingSpace

namespace MMP

open MMP

section ZeroDim

open borelMooreHomology BorelMooreCross FundamentalClass ThomClass SingularChain SingularCochain

variable {T : TopCat.{0}} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [ChartedSpace H T] (R : Type) [CommRing R]

/-- **The local orientation class of a point.** On a one-point space (a manifold of dimension
`0`), the cocycle `1` of degree `0` is the local orientation class at the point. -/
theorem exists_isLocalOrientationClass_of_eq_zero [Subsingleton T] {n : ℕ} (hn : n = 0)
    (b : Module.Basis (Fin n) ℝ H) (y : T) : ∃ u, IsLocalOrientationClass R b y u := by
  subst hn
  let α : Simplex T 0 → R := fun _ ↦ 1
  have hα : α ∈ relCocycles R ({y}ᶜ : Set T) 0 := by
    refine ⟨fun σ hσ ↦ ?_, ?_⟩
    · obtain ⟨t⟩ : Nonempty (stdSimplex ℝ (Fin 1)) := inferInstance
      exact absurd (Subsingleton.elim (σ t) y) (hσ ⟨t, rfl⟩)
    · funext σ
      simp [coboundary_apply, Fin.sum_univ_two, α]
  refine ⟨(relativeSingularCohomologyEquiv R ({y}ᶜ : Set T) 0).symm
    (Submodule.Quotient.mk ⟨α, hα⟩), α, hα, ⟨hα, fun e _ _ v _ hvt ↦ ?_⟩, by simp⟩
  simp [α]

end ZeroDim

section PushforwardBookkeeping

open borelMooreHomology BorelMooreCross

/-- For natural numbers `m` and `r`, `2(m + r) - 2r = 2m` in `ℤ`. -/
lemma two_mul_add_sub_two_mul (m r : ℕ) :
    ((2 * (m + r) : ℕ) : ℤ) - ((2 * r : ℕ) : ℤ) = ((2 * m : ℕ) : ℤ) := by
  omega

variable (R : Type) [CommRing R]

/-- Restriction to an open set `W` commutes with the change of degree along `j = j'`. -/
lemma congrDegree_restrict_hom {Y : TopCat.{0}} [T2Space Y] (W : Opens Y) {j j' : ℤ}
    (h : j = j') (x : borelMooreHomology R (ModuleCat.of R R) Y j) :
    (restrict R (ModuleCat.of R R) W j').hom (congrDegree R _ h x) =
      congrDegree R _ h ((restrict R (ModuleCat.of R R) W j).hom x) := by
  subst h
  rfl

/-- The push-forwards along `f`, `g` and `f ≫ g` commute with the change of degree. -/
lemma pushforward_congrDegree_pushforward {A B C : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (hfg : f ≫ g = k) (hf : IsProperMap f) (hg : IsProperMap g) (hk : IsProperMap k)
    {i i' : ℤ} (h : i = i') (x : borelMooreHomology R (ModuleCat.of R R) A i) :
    borelMooreHomology.pushforward R (ModuleCat.of R R) g hg i'
        (BorelMooreCross.congrDegree R B h
          (borelMooreHomology.pushforward R (ModuleCat.of R R) f hf i x)) =
      BorelMooreCross.congrDegree R C h
        (borelMooreHomology.pushforward R (ModuleCat.of R R) k hk i x) := by
  subst h hfg
  exact borelMooreHomology.pushforward_comp_apply R f g hf hg hk _ x

/-- Push-forward along a composite, with the properness of the composite deduced. -/
lemma pushforward_comp_hom_apply {A B C : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : IsProperMap f) (hg : IsProperMap g) (k : ℤ)
    (x : borelMooreHomology R (ModuleCat.of R R) A k) :
    (pushforward R (ModuleCat.of R R) g hg k).hom
        ((pushforward R (ModuleCat.of R R) f hf k).hom x) =
      (pushforward R (ModuleCat.of R R) (f ≫ g) (hg.comp hf) k).hom x :=
  pushforward_comp_apply R f g hf hg _ k x

/-- Two chains of push-forwards along maps with the same composite agree. -/
lemma pushforward_chain_eq {A₀ A₁ A₂ A₃ A₄ A₅ B₁ : TopCat.{0}} (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂)
    (f₃ : A₂ ⟶ A₃) (f₄ : A₃ ⟶ A₄) (f₅ : A₄ ⟶ A₅) (g₁ : A₀ ⟶ B₁) (g₂ : B₁ ⟶ A₅)
    (hf₁ : IsProperMap f₁) (hf₂ : IsProperMap f₂) (hf₃ : IsProperMap f₃) (hf₄ : IsProperMap f₄)
    (hf₅ : IsProperMap f₅) (hg₁ : IsProperMap g₁) (hg₂ : IsProperMap g₂)
    (h : ∀ a, f₅ (f₄ (f₃ (f₂ (f₁ a)))) = g₂ (g₁ a)) (k : ℤ)
    (x : borelMooreHomology R (ModuleCat.of R R) A₀ k) :
    (pushforward R (ModuleCat.of R R) f₅ hf₅ k).hom
      ((pushforward R (ModuleCat.of R R) f₄ hf₄ k).hom
        ((pushforward R (ModuleCat.of R R) f₃ hf₃ k).hom
          ((pushforward R (ModuleCat.of R R) f₂ hf₂ k).hom
            ((pushforward R (ModuleCat.of R R) f₁ hf₁ k).hom x)))) =
      (pushforward R (ModuleCat.of R R) g₂ hg₂ k).hom
        ((pushforward R (ModuleCat.of R R) g₁ hg₁ k).hom x) := by
  simp only [pushforward_comp_hom_apply]
  exact pushforward_apply_congr R (ConcreteCategory.hom_ext _ _ h) _ _ _ _

end PushforwardBookkeeping

/-- The homeomorphism between the sources of two embeddings with the same range. -/
def homeomorphOfRangeEq {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] {f : A → C} {g : B → C} (hf : IsEmbedding f) (hg : IsEmbedding g)
    (h : range f = range g) : A ≃ₜ B :=
  hf.toHomeomorph.trans ((Homeomorph.setCongr h).trans hg.toHomeomorph.symm)

/-- `g (homeomorphOfRangeEq hf hg h a) = f a`. -/
lemma apply_homeomorphOfRangeEq {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] {f : A → C} {g : B → C} (hf : IsEmbedding f) (hg : IsEmbedding g)
    (h : range f = range g) (a : A) : g (homeomorphOfRangeEq hf hg h a) = f a :=
  congrArg Subtype.val <|
    hg.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr h) (hf.toHomeomorph a))

section RegularOpens

open borelMooreHomology BorelMooreCross

section Topology

variable (R : Type) [CommRing R]

/-- The cap product `T ∩` with a class `g^* u ∈ H^j(Y, Y - T)` pulled back along `g : Y → F`,
read on `g⁻¹(S) = T`, is the cap product `g^* u ∩` of `capProductSupportPullback`. -/
lemma pushforward_setCongr_capProductSupport_relMap {Y F : TopCat.{0}} (g : Y ⟶ F) {S : Set F}
    (hS : IsClosed S) {T : Set Y} (hT : T = g ⁻¹' S) (hTc : IsClosed T)
    (hTd : HasProperNeighbourhoodDeformations T) (hg : Tᶜ ⊆ g ⁻¹' Sᶜ)
    (hYd : HasProperNeighbourhoodDeformations (g ⁻¹' S)) (j k : ℤ)
    (u : cohomologyWithSupports R (ModuleCat.of R R) F S j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (Homeomorph.setCongr hT : C(T, g ⁻¹' S)))
        (Homeomorph.setCongr hT).isProperMap (k - j)).hom
      (capProductSupport R Y hTc hTd j k
        ((relativeSingularCohomology.map R (ModuleCat.of R R) g hg j).hom u) a) =
      capProductSupportPullback R g hS hYd j k u a := by
  subst hT
  rw [capProductSupportPullback_apply]
  exact pushforward_id_apply' R _ _ rfl _ _

end Topology

namespace borelMooreHomology

open MMP.borelMooreHomology

variable (R : Type) [CommRing R]

/-- Restriction to two equal open sets. -/
lemma restrict_eq_pushforward_setCongr {Y : TopCat.{0}} [T2Space Y] {O O' : Opens Y}
    (h : (O' : Set Y) = O) (j : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) Y j) :
    (restrict R (ModuleCat.of R R) O j).hom a =
      (pushforward R (ModuleCat.of R R) (TopCat.ofHom (Homeomorph.setCongr h : C(O', O)))
        (Homeomorph.setCongr h).isProperMap j).hom
        ((restrict R (ModuleCat.of R R) O' j).hom a) := by
  obtain rfl : O' = O := SetLike.coe_injective h
  exact (pushforward_id_apply' R _ _ rfl _ _).symm

end borelMooreHomology

namespace UnderlyingSpace

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

section Algebraic

variable [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

/-- An open subset `O ⊆ X_reg(ℂ)`, read as the open subset `O ∩ X_reg(ℂ)` of `X_reg(ℂ)`: the
homeomorphism `O ∩ X_reg(ℂ) ≅ O`. -/
def regularOpensInterHomeomorph (O : Opens (UnderlyingSpace ℂ X))
    (hO : (O : Set (UnderlyingSpace ℂ X)) ⊆ regularPart ℂ X) :
    regularOpensInter (𝕜 := ℂ) O ≃ₜ O where
  toFun z := ⟨z.1.1, z.2⟩
  invFun x := ⟨⟨x.1, hO x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- `regularOpensInterHomeomorph O hO` sends `z` to the point `z` of `X(ℂ)`. -/
@[simp]
lemma coe_regularOpensInterHomeomorph_apply (O : Opens (UnderlyingSpace ℂ X))
    (hO : (O : Set (UnderlyingSpace ℂ X)) ⊆ regularPart ℂ X) (z : regularOpensInter (𝕜 := ℂ) O) :
    (regularOpensInterHomeomorph O hO z : UnderlyingSpace ℂ X) = z.1.1 :=
  rfl

/-- `regularOpensInterHomeomorph`, as a morphism of spaces. -/
def regularOpensInterHom (O : Opens (UnderlyingSpace ℂ X))
    (hO : (O : Set (UnderlyingSpace ℂ X)) ⊆ regularPart ℂ X) :
    TopCat.of (regularOpensInter (𝕜 := ℂ) O) ⟶ TopCat.of O :=
  TopCat.ofHom (regularOpensInterHomeomorph O hO : C(regularOpensInter (𝕜 := ℂ) O, O))

/-- `regularOpensInterHom O hO` is a proper map. -/
lemma isProperMap_regularOpensInterHom (O : Opens (UnderlyingSpace ℂ X))
    (hO : (O : Set (UnderlyingSpace ℂ X)) ⊆ regularPart ℂ X) :
    IsProperMap (regularOpensInterHom O hO) :=
  (regularOpensInterHomeomorph O hO).isProperMap

variable (R : Type) [CommRing R] in
/-- For an open set `O ⊆ X_reg(ℂ)`, restricting to `O` is restricting to `X_reg(ℂ)` and then to
`O ∩ X_reg(ℂ)`, read in `O`. -/
lemma restrict_eq_pushforward_regularOpensInterHom [T2Space (UnderlyingSpace ℂ X)]
    (O : Opens (UnderlyingSpace ℂ X)) (hO : (O : Set (UnderlyingSpace ℂ X)) ⊆ regularPart ℂ X)
    (j : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) j) :
    (restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X)) O j).hom a =
      (pushforward R (ModuleCat.of R R) (regularOpensInterHom O hO)
        (isProperMap_regularOpensInterHom O hO) j).hom
        ((restrict R (ModuleCat.of R R) (Y := TopCat.of (regularOpens ℂ X))
          (regularOpensInter (𝕜 := ℂ) O) j).hom
          ((restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ X))
            (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X))) j).hom a)) :=
  FundamentalClass.restrict_eq_pushforward_subOpensInv (R := R)
    (show O ≤ (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X))) from hO) j a

end Algebraic

variable [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [QuasiCompact (X ↘ Spec (.of ℂ))]

/-- **The charts of an open subset of `X_reg(ℂ)`.** A chart of the open subset
`O ∩ X_reg(ℂ)` of the complex manifold `X_reg(ℂ)` is the restriction of an algebraic chart `a` of
`X(ℂ)`: it agrees with `a`, has the points of `a`'s source as source, and its inverse is `a⁻¹`. -/
theorem exists_isAlgebraicChart_of_mem_atlas_regularOpensInter {n : ℕ}
    (hn : (n : WithBot ℕ∞) = MMP.Intersection.Scheme.dimension X) (O : Opens (UnderlyingSpace ℂ X))
    {c : OpenPartialHomeomorph (regularOpensInter (𝕜 := ℂ) O) (EuclideanSpace ℂ (Fin n))}
    (hc : letI := regularChartedSpace (𝕜 := ℂ) hn
      c ∈ atlas (EuclideanSpace ℂ (Fin n)) (regularOpensInter (𝕜 := ℂ) O)) :
    ∃ a : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n)),
      IsAlgebraicChart a ∧ (∀ z : regularOpensInter (𝕜 := ℂ) O, c z = a z.1.1) ∧
        (∀ z : regularOpensInter (𝕜 := ℂ) O, z ∈ c.source ↔ z.1.1 ∈ a.source) ∧
          ∀ y ∈ c.target, ((c.symm y).1.1 : UnderlyingSpace ℂ X) = a.symm y := by
  letI := regularChartedSpace (𝕜 := ℂ) hn
  obtain ⟨_, ⟨x₀, rfl⟩, hc⟩ := hc
  rw [mem_singleton_iff] at hc
  subst hc
  set a := (exists_isAlgebraicChart_of_dimension_eq hn x₀.1.1
    (mem_regularOpens.1 x₀.1.2)).choose
  set c := (chartAt (EuclideanSpace ℂ (Fin n)) x₀.1).subtypeRestr ⟨x₀⟩
  have hsrc : ∀ z, z ∈ c.source ↔ z.1.1 ∈ a.source := fun z ↦ by
    rw [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
    change z.1 ∈ (a.subtypeRestr ⟨x₀.1⟩).source ↔ _
    rw [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
  have hcoe : ∀ z, c z = a z.1.1 := fun z ↦ rfl
  refine ⟨a, (exists_isAlgebraicChart_of_dimension_eq hn x₀.1.1
    (mem_regularOpens.1 x₀.1.2)).choose_spec.2, hcoe, hsrc, fun y hy ↦ ?_⟩
  exact (a.left_inv ((hsrc _).1 (c.map_target hy))).symm.trans
    (congrArg a.symm ((hcoe _).symm.trans (c.right_inv hy)))

end UnderlyingSpace

end RegularOpens

end MMP
