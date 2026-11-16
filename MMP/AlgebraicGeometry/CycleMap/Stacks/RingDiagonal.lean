module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationProof
public import MMP.AlgebraicGeometry.CycleMap.Stacks.ExteriorProduct
public import MMP.AlgebraicGeometry.CycleMap.Stacks.Pushforward
public import MMP.AlgebraicGeometry.RegularImmersion.OfSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.SelfIntersectionProduct
public import MMP.AlgebraicGeometry.CycleMap.DiagonalPoints

/-!
# The cycle class of a Stacks intersection product, through the diagonal

Let `X` be a complex scheme, smooth of relative dimension `n` over `ℂ`, with diagonal
`δ : X ⟶ X ×_ℂ X`, a regular closed immersion of codimension `n`
(`MMP.Chow.isRegularClosedImmersionOfCodim_diagonal`), and orientation class
`u = u_δ ∈ H^{2n}(X × X, X × X - Δ)` (`MMP.Modules.IsRegularImbeddingOrientationClass`). The
intersection product of Stacks' Chow groups is `x · y = δ^!(x × y)`
(`Stacks.Chow.selfIntersectionProduct`, Stacks 0FC0), with `δ^! = c(δ, 𝒩)` the class of the normal
sheaf of `δ` (`Stacks.Chow.regularNormalGysinClass`, Stacks 0FBK). Fulton's Theorem 19.2 for the
fibre square of `δ` along `1_{X × X}` therefore gives

  `cl_X(x · y) = u ∩ cl_{X × X}(x × y)` in `H_{2m}(Δ(ℂ))`, `m = k + l - n`,

for `x ∈ A_k X`, `y ∈ A_l X`, the left side read through `X(ℂ) ≅ Δ(ℂ)`
(`MMP.Chow.pushforward_chowCycleClass_selfIntersectionProduct`), from Theorem 19.2 on Stacks'
Chow groups (`MMP.Chow.chowCycleMapRefinedGysinFormulaAt`).

## Main results

* `MMP.Chow.isRegularClosedImmersionOfCodim_diagonal`: the diagonal of a scheme smooth of relative
  dimension `n` over `ℂ` is a regular closed immersion of codimension `n`.
* `MMP.Chow.properChowPushforward_fst_regularNormalGysinClass_cap`: `δ^!(x × y)`, computed on the
  fibre square of `δ` along `1_{X × X}` and pushed to `X`, is the Stacks product `x · y`.
* `MMP.Chow.pushforward_chowCycleClass_selfIntersectionProduct`:
  `cl_X(x · y) = u ∩ cl_{X × X}(x × y)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Theorem 19.2 and Corollary 19.2.
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf TensorProduct

namespace MMP.Chow

attribute [local instance low] fibreProductOver
attribute [local instance] isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct

/-! ### Transport lemmas -/

/-- The identity is proper. -/
theorem isProper_id (Y : Scheme.{0}) : IsProper (𝟙 Y) :=
  inferInstance

/-- The identity is locally of finite type. -/
theorem locallyOfFiniteType_id (Y : Scheme.{0}) : LocallyOfFiniteType (𝟙 Y) :=
  inferInstance

section Transport

variable {C : ChowSituation.{0}}

/-- `chowGroupCongrDegree` along `rfl` is the identity. -/
theorem chowGroupCongrDegree_rfl {Z : Scheme.{0}} (s : Z ⟶ C.S) [LocallyOfFiniteType s] {j : ℤ}
    (a : chowGroup C s j) : chowGroupCongrDegree C s (rfl : j = j) a = a :=
  rfl

/-- Proper pushforward along equal morphisms. -/
theorem properChowPushforward_congr_hom {A B : Scheme.{0}} {sA : A ⟶ C.S} {sB : B ⟶ C.S}
    [LocallyOfFiniteType sA] [LocallyOfFiniteType sB] {p p' : A ⟶ B} [IsProper p] [IsProper p']
    (h : p = p') (hp : p ≫ sB = sA) (hp' : p' ≫ sB = sA) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB p hp k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA sB p' hp' k)
    (a : chowGroup C sA k) :
    properChowPushforward C sA sB p hp k hfac a = properChowPushforward C sA sB p' hp' k hfac' a := by
  subst h
  rfl

/-- Pushforward along an isomorphism after a proper pushforward is the proper pushforward along
the composite. -/
theorem chowPushforwardOfIso_properChowPushforward {A B D : Scheme.{0}} {sA : A ⟶ C.S}
    {sB : B ⟶ C.S} {sD : D ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sB]
    [LocallyOfFiniteType sD] (p : A ⟶ B) [IsProper p] (q : B ⟶ D) [IsIso q] (hp : p ≫ sB = sA)
    (hq : q ≫ sD = sB) (k : ℤ) (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB p hp k)
    (a : chowGroup C sA k) :
    chowPushforwardOfIso C sB sD q hq k (properChowPushforward C sA sB p hp k hfac a) =
      properChowPushforward C sA sD (p ≫ q) (by rw [Category.assoc, hq, hp]) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _) a :=
  DFunLike.congr_fun (properChowPushforward_comp C sA sB sD p q hp hq k hfac
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sB sD q hq k)) a

/-- `chowGroupCongr` changes a class only up to heterogeneous equality. -/
theorem chowGroupCongr_heq' {Z : Scheme.{0}} {q q' : Z ⟶ C.S} [LocallyOfFiniteType q]
    [LocallyOfFiniteType q'] (h : q = q') (k : ℤ) (a : chowGroup C q k) :
    chowGroupCongr C h k a ≍ a := by
  subst h
  rfl

/-- Stacks' exterior product commutes with the transport along an equality of structure
morphisms, up to heterogeneous equality. -/
theorem chowExteriorProduct_chowGroupCongr_heq [Subsingleton C.S] [IsIntegral C.S]
    [JacobsonSpace C.S] (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {Y : Scheme.{0}} {s s' : Y ⟶ C.S} [LocallyOfFiniteType s] [LocallyOfFiniteType s']
    (h : s = s') (k l : ℤ) (a : chowGroup C s k) (b : chowGroup C s l) :
    chowExteriorProduct C hδ s' s' k l (chowGroupCongr C h k a ⊗ₜ chowGroupCongr C h l b) ≍
      chowExteriorProduct C hδ s s k l (a ⊗ₜ b) := by
  subst h
  rfl

variable {G : GysinSystem C} {X P : Scheme.{0}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- The cap product of a bivariant class at a test morphism `g : P' ⟶ P` equal to the identity,
pushed forward to the source, is the one at the identity, on heterogeneously equal classes. -/
theorem properChowPushforward_fst_cap_of_heq_id {sP : P ⟶ C.S} {_ : LocallyOfFiniteType sP}
    {f : X ⟶ P} {_ : LocallyOfFiniteType f} {hf : f ≫ sP = sX} {p : ℤ}
    (c : BivariantClass C G sX sP f hf p) {P' : Scheme.{0}} (hP : P' = P) (g : P' ⟶ P)
    {_ : LocallyOfFiniteType g} (hgP : IsProper g) (hP1 : IsProper (𝟙 P)) (hg : g ≍ 𝟙 P) (k : ℤ)
    (a : chowGroup C (g ≫ sP) k) (b : chowGroup C (𝟙 P ≫ sP) k) (hab : a ≍ b) :
    properChowPushforward C (pullback.fst f g ≫ sX) sX (pullback.fst f g) rfl (k - p)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ rfl _)
        (c.cap g k a) =
      properChowPushforward C (pullback.fst f (𝟙 P) ≫ sX) sX (pullback.fst f (𝟙 P)) rfl (k - p)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ rfl _)
        (c.cap (𝟙 P) k b) := by
  subst hP
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hab
  rfl

/-- The normal sheaf class of a regular closed immersion does not depend on how the structure
morphism of the target is written. -/
theorem regularNormalGysinClass_cap_congr {f : X ⟶ P} [IsClosedImmersion f] {d : ℕ}
    (hreg : IsRegularClosedImmersionOfCodim f d) {sP sP' : P ⟶ C.S} [LocallyOfFiniteType sP]
    [LocallyOfFiniteType sP'] (h : sP = sP') (hf : f ≫ sP = sX) (hf' : f ≫ sP' = sX)
    {T : Scheme.{0}} (g : T ⟶ P) [LocallyOfFiniteType g] (k : ℤ) (a : chowGroup C (g ≫ sP) k) :
    (regularNormalGysinClass C sX sP f hf hreg).cap g k a =
      (regularNormalGysinClass C sX sP' f hf' hreg).cap g k (chowGroupCongr C (by rw [h]) k a) := by
  subst h
  rfl

end Transport

/-! ### The diagonal -/

section Diagonal

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]

/-- The diagonal of a complex scheme is a closed immersion. -/
theorem isClosedImmersion_pullbackDiagonal [IsComplexScheme X] :
    IsClosedImmersion (pullback.diagonal (X ↘ Spec (.of ℂ))) :=
  haveI := isSeparated_of_isComplexScheme X
  inferInstance

/-- **The diagonal of a smooth scheme is a regular closed immersion** (Stacks 0FBR, 067U): for
`X` smooth of relative dimension `n` over `ℂ`, `δ : X ⟶ X ×_ℂ X` is a regular closed immersion of
codimension `n`. -/
theorem isRegularClosedImmersionOfCodim_diagonal [IsComplexScheme X] (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))] :
    IsRegularClosedImmersionOfCodim (pullback.diagonal (X ↘ Spec (.of ℂ))) n := by
  haveI := isClosedImmersion_pullbackDiagonal X
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  haveI : SmoothOfRelativeDimension n (pullback.fst (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @SmoothOfRelativeDimension n)
      (IsPullback.of_hasPullback _ _).flip ‹_›
  haveI : SmoothOfRelativeDimension n (pullback.diagonal (X ↘ Spec (.of ℂ)) ≫
      pullback.fst (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ)) := by
    rw [pullback.diagonal_fst_assoc]
    infer_instance
  exact MMP.isRegularClosedImmersionOfCodim_of_smoothOfRelativeDimension
    (pullback.diagonal (X ↘ Spec (.of ℂ)))
    (pullback.fst (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ≫ X ↘ Spec (.of ℂ)) (n := n) (m := n)

end Diagonal

attribute [local instance] isOver_pullbackDiagonal isClosedImmersion_pullbackDiagonal

/-! ### `δ^!(x × y)` on the fibre square of `δ` along `1_{X × X}` -/

section Algebra

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] {n : ℕ}
  (hΔ : IsRegularClosedImmersionOfCodim (pullback.diagonal (X ↘ Spec (.of ℂ))) n)

/-- `X ×_ℂ X ⟶ X ×_ℂ X` from the self-product over `𝟙 X ≫ (X ↘ Spec ℂ)`, on which Stacks'
product caps, is the identity. -/
theorem exteriorToSelfProduct_id_id_eq :
    (exteriorToSelfProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (𝟙 X) (𝟙 X) :
      pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) = 𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) := by
  ext <;> simp [exteriorToSelfProduct, exteriorToSelfProductMap] <;> rfl

/-- The defining formula of `Stacks.Chow.selfIntersectionProduct` on `X`. -/
theorem selfIntersectionProduct_eq (a b : ℤ)
    (α : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) a)
    (β : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) b) :
    selfIntersectionProduct (fieldChowSituation ℂ)
        (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
        (X ↘ Spec (.of ℂ)) n
        (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          (selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))) (pullback.diagonal (X ↘ Spec (.of ℂ)))
          (diagonal_comp_selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))) hΔ) a b α β =
      chowPushforwardOfIso (fieldChowSituation ℂ)
        (pullback.fst (𝟙 X) (𝟙 X) ≫ (𝟙 X ≫ X ↘ Spec (.of ℂ))) (X ↘ Spec (.of ℂ))
        (pullback.fst (𝟙 X) (𝟙 X)) (by rw [Category.id_comp]) (a + b - n)
        (intersectionProduct (fieldChowSituation ℂ)
          (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
          (X ↘ Spec (.of ℂ)) (𝟙 X) (𝟙 X) n
          (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
            (selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))) (pullback.diagonal (X ↘ Spec (.of ℂ)))
            (diagonal_comp_selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))) hΔ) a b
          (TensorProduct.tmul ℤ
            (chowGroupCongr (fieldChowSituation ℂ) (Category.id_comp (X ↘ Spec (.of ℂ))).symm a α)
            (chowGroupCongr (fieldChowSituation ℂ) (Category.id_comp (X ↘ Spec (.of ℂ))).symm b β))) :=
  rfl

include hΔ in
/-- **`δ^!(x × y)`, pushed to `X`, is the Stacks intersection product `x · y`** (Stacks 0FC0).
On the fibre square of `δ` along `1_{X × X}`, `c(δ, 𝒩) ∩ (x × y)` (the left side of Fulton's
Theorem 19.2, `MMP.Chow.ChowCycleMapRefinedGysinFormulaAt`), pushed forward along
`X ×_{X × X} (X × X) ≅ X`, is `x · y = Stacks.Chow.selfIntersectionProduct x y`. -/
theorem properChowPushforward_fst_regularNormalGysinClass_cap {k l : ℕ} (N M : ℤ)
    (hN : ((k + l : ℕ) : ℤ) = N) (hM : N - n = M)
    (x : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (y : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) l) :
    properChowPushforward (fieldChowSituation ℂ)
        (pullback.fst (pullback.diagonal (X ↘ Spec (.of ℂ))) (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))) ≫
          X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))
        (pullback.fst (pullback.diagonal (X ↘ Spec (.of ℂ))) (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))))) rfl M
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ rfl _)
        (chowGroupCongrDegree (fieldChowSituation ℂ)
          (pullback.fst (pullback.diagonal (X ↘ Spec (.of ℂ))) (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))) ≫
            X ↘ Spec (.of ℂ)) hM
          ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
              (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ)) (pullback.diagonal (X ↘ Spec (.of ℂ)))
              (comp_over _ _) hΔ).cap (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))) N
            (chowGroupCongr (fieldChowSituation ℂ) (q := pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))
              (q' := 𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) ≫ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))
              (comp_over (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))) _).symm N
              (chowGroupCongrDegree (fieldChowSituation ℂ) (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ)) hN
                (chowGroupCongr (fieldChowSituation ℂ) (pullback_fst_comp_over X X)
                  ((k + l : ℕ) : ℤ)
                  (chowExteriorProduct (fieldChowSituation ℂ)
                    (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (X ↘ Spec (.of ℂ))
                    (X ↘ Spec (.of ℂ)) k l (x ⊗ₜ y))))))) =
      chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
        (by rw [← hM, ← hN]; push_cast; ring)
        (selfIntersectionProduct (fieldChowSituation ℂ)
          (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
          (X ↘ Spec (.of ℂ)) n
          (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
            (selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))) (pullback.diagonal (X ↘ Spec (.of ℂ)))
            (diagonal_comp_selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))) hΔ) k l x y) := by
  subst hN hM
  haveI hP1 := isProper_id (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))
  rw [chowGroupCongrDegree_rfl, chowGroupCongrDegree_rfl, chowGroupCongrDegree_rfl,
    regularNormalGysinClass_cap_congr (C := fieldChowSituation ℂ) (sX := X ↘ Spec (.of ℂ))
      (f := pullback.diagonal (X ↘ Spec (.of ℂ))) hΔ (sP := pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))
      (sP' := selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))) (pullback_fst_comp_over X X).symm
      (comp_over (pullback.diagonal (X ↘ Spec (.of ℂ))) (Spec (.of ℂ)))
      (diagonal_comp_selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))),
    selfIntersectionProduct_eq, intersectionProduct_apply, chowPushforwardOfIso_properChowPushforward]
  haveI : @IsProper (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))
      (exteriorToSelfProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (𝟙 X) (𝟙 X)) := by
    rw [exteriorToSelfProduct_id_id_eq]
    exact isProper_id _
  haveI : @LocallyOfFiniteType (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))
      (exteriorToSelfProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (𝟙 X) (𝟙 X)) := by
    rw [exteriorToSelfProduct_id_id_eq]
    exact locallyOfFiniteType_id _
  haveI : LocallyOfFiniteType (exteriorToSelfProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
      (𝟙 X) (𝟙 X)) := ‹@LocallyOfFiniteType (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) _›
  haveI hE : IsProper (exteriorToSelfProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (𝟙 X)
      (𝟙 X)) := ‹@IsProper (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) _›
  haveI : IsProper (pullback.fst (pullback.diagonal (X ↘ Spec (.of ℂ)))
      (exteriorToSelfProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (𝟙 X) (𝟙 X))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper.{0})
      (IsPullback.of_hasPullback _ _).flip hE
  have hfst : (pullbackDiagonalMapIdIso (𝟙 X) (𝟙 X) (X ↘ Spec (.of ℂ))).hom ≫
      pullback.fst (𝟙 X) (𝟙 X) = pullback.fst (pullback.diagonal (X ↘ Spec (.of ℂ)))
        (exteriorToSelfProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (𝟙 X) (𝟙 X)) := by
    have h := congrArg (· ≫ pullback.fst (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))
      (pullback.condition (f := pullback.diagonal (X ↘ Spec (.of ℂ)))
        (g := exteriorToSelfProduct (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (𝟙 X) (𝟙 X)))
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, exteriorToSelfProduct,
      exteriorToSelfProductMap, pullback.lift_fst] at h
    rw [pullbackDiagonalMapIdIso_hom_fst]
    exact h.symm
  rw [properChowPushforward_congr_hom hfst _ rfl _ _
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ rfl _)]
  rw [chowGroupCongr_chowGroupCongr, chowGroupCongr_chowGroupCongr]
  have h1 := chowExteriorProduct_chowGroupCongr_heq (C := fieldChowSituation ℂ)
    (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s)
    (Category.id_comp (X ↘ Spec (.of ℂ))).symm (k : ℤ) (l : ℤ) x y
  refine Eq.symm (properChowPushforward_fst_cap_of_heq_id _ rfl _ hE hP1
    (heq_of_eq exteriorToSelfProduct_id_id_eq) _ _ _ ?_)
  refine HEq.trans (chowGroupCongr_heq' _ _ _) (HEq.trans h1 ?_)
  exact (chowGroupCongr_heq' _ _ _).symm

end Algebra

/-! ### The cycle class of `x · y` -/

section CycleClass

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] {n : ℕ}
  (hΔ : IsRegularClosedImmersionOfCodim (pullback.diagonal (X ↘ Spec (.of ℂ))) n)
  (R : Type) [CommRing R]

/-- Push-forward along equal maps. -/
theorem pushforward_apply_congr_hom {A B : TopCat.{0}} {f g : A ⟶ B} (h : f = g)
    (hf : IsProperMap f) (hg : IsProperMap g) (i : ℤ)
    (z : borelMooreHomology R (ModuleCat.of R R) A i) :
    (borelMooreHomology.pushforward R (ModuleCat.of R R) f hf i).hom z =
      (borelMooreHomology.pushforward R (ModuleCat.of R R) g hg i).hom z := by
  subst h
  rfl

/-- `X(ℂ) → Δ(ℂ)` through `X ×_{X × X} (X × X)`: the map of points of the fibre square of `δ`
along `1_{X × X}` is that of `δ` after the first projection. -/
theorem map_fst_comp_fibreSquarePointsHom_id_vert :
    TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
        (pullback.fst (pullback.diagonal (X ↘ Spec (.of ℂ))) (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))))) ≫
      fibreSquarePointsHom (IsPullback.id_vert (pullback.diagonal (X ↘ Spec (.of ℂ)) :
        X ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))) =
    fibreSquarePointsHom (IsPullback.of_hasPullback (pullback.diagonal (X ↘ Spec (.of ℂ)) :
        X ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))))).flip := by
  refine ConcreteCategory.hom_ext _ _ fun p ↦ Subtype.ext (UnderlyingSpace.ext ?_)
  change toHom (UnderlyingSpace.map (K := ℂ) (pullback.diagonal (X ↘ Spec (.of ℂ)))
      (UnderlyingSpace.map (K := ℂ)
        (pullback.fst (pullback.diagonal (X ↘ Spec (.of ℂ))) (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))))) p)) =
    toHom (UnderlyingSpace.map (K := ℂ)
      (pullback.snd (pullback.diagonal (X ↘ Spec (.of ℂ))) (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))))) p)
  rw [toHom_map, toHom_map, toHom_map, Category.assoc, pullback.condition, Category.comp_id]

include hΔ in
/-- **The cycle class of a Stacks intersection product** (Fulton, Theorem 19.2 for the
diagonal). Let `X` be a complex scheme whose diagonal `δ` is a regular closed immersion of
codimension `n`, `u = u_δ ∈ H^{2n}(X × X, X × X - Δ)` an orientation class of `δ`, and
`x ∈ A_k X`, `y ∈ A_l X` with `k + l = m + n`. Then `cl_X(x · y) = u ∩ cl_{X × X}(x × y)` in
`H_{2m}(Δ(ℂ))`, where `x · y` is Stacks' intersection product
`Stacks.Chow.selfIntersectionProduct` formed with `δ^! = c(δ, 𝒩)` and the left side is read
through `X(ℂ) ≅ Δ(ℂ)`. -/
theorem pushforward_chowCycleClass_selfIntersectionProduct {k l m : ℕ} (hklm : k + l = m + n)
    {u : cohomologyWithSupports R (ModuleCat.of R R)
      (TopCat.of (UnderlyingSpace ℂ (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))))
      (range (UnderlyingSpace.map (K := ℂ) (pullback.diagonal (X ↘ Spec (.of ℂ)) :
        X ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))))) (2 * n : ℕ)}
    (hu : MMP.Modules.IsRegularImbeddingOrientationClass R
      (pullback.diagonal (X ↘ Spec (.of ℂ)) : X ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) n u)
    (x : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (y : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) l) :
    borelMooreHomology.pushforward R (ModuleCat.of R R)
        (fibreSquarePointsHom (IsPullback.id_vert (pullback.diagonal (X ↘ Spec (.of ℂ)) :
          X ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))))
        (isProperMap_fibreSquarePointsHom (IsPullback.id_vert _)) (2 * m : ℕ)
        (chowCycleClass R m
          (chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
            (by omega : (k : ℤ) + l - n = m)
            (selfIntersectionProduct (fieldChowSituation ℂ)
              (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
              (X ↘ Spec (.of ℂ)) n
              (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
                (selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
                (pullback.diagonal (X ↘ Spec (.of ℂ)))
                (diagonal_comp_selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
                hΔ) k l x y))) =
      BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul_eq m n)
        (borelMooreHomology.capProductSupportPullback R
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))))))
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
            (pullback.diagonal (X ↘ Spec (.of ℂ)) : X ⟶ pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))).isClosed_range
          (hasProperNeighbourhoodDeformations_preimage_range_map _ (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))))
          ((2 * n : ℕ) : ℤ) ((2 * (m + n) : ℕ) : ℤ) u
          (chowCycleClass R (m + n)
            (chowGroupCongrDegree (fieldChowSituation ℂ) (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))
              (by omega : ((k + l : ℕ) : ℤ) = ((m + n : ℕ) : ℤ))
              (chowGroupCongr (fieldChowSituation ℂ) (pullback_fst_comp_over X X)
                ((k + l : ℕ) : ℤ)
                (chowExteriorProduct (fieldChowSituation ℂ)
                  (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (X ↘ Spec (.of ℂ))
                  (X ↘ Spec (.of ℂ)) k l (x ⊗ₜ y)))))) := by
  have h19 := chowCycleMapRefinedGysinFormulaAt (Y := pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))) _ (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)))) R hΔ
    hu m (chowGroupCongrDegree (fieldChowSituation ℂ) (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))
      (by omega : ((k + l : ℕ) : ℤ) = ((m + n : ℕ) : ℤ))
      (chowGroupCongr (fieldChowSituation ℂ) (pullback_fst_comp_over X X) ((k + l : ℕ) : ℤ)
        (chowExteriorProduct (fieldChowSituation ℂ)
          (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (X ↘ Spec (.of ℂ))
          (X ↘ Spec (.of ℂ)) k l (x ⊗ₜ y))))
  unfold ChowCycleMapRefinedGysinFormulaAt at h19
  refine Eq.trans ?_ h19
  rw [← properChowPushforward_fst_regularNormalGysinClass_cap hΔ _ _
      (by omega : ((k + l : ℕ) : ℤ) = ((m + n : ℕ) : ℤ)) (natCast_add_sub_natCast m n) x y]
  erw [chowCycleClass_properChowPushforward_of_isProper
    (X := pullback (pullback.diagonal (X ↘ Spec (.of ℂ))) (𝟙 (pullback (X ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ))))) R
    (pullback.fst _ _)]
  rw [← borelMooreHomology.pushforward_comp_apply']
  exact pushforward_apply_congr_hom R map_fst_comp_fibreSquarePointsHom_id_vert _ _ _ _

end CycleClass

end MMP.Chow
