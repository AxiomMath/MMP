module

public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.IsoOfInverse

/-!
# Comparing `MMP.Intersection.ProjSpace` with the Stacks models of projective space

* `MMP.Intersection.isIso_twistMap_integralGradedHom`: the canonical comparison
  `r^* 𝒪_{Proj ℤ[T]}(d) ⟶ 𝒪_{Proj S[T]}(d)` along the coefficient change `ℤ → S` is an
  isomorphism, for every `d : ℤ`.
* `MMP.Intersection.ProjSpace.isoPolyGrading`: `ℙ^{ULift (Fin (n + 1))}_S ≅ Proj S[T₀, …, Tₙ]`,
  induced by renaming the variables, and `ProjSpace.twistingSheafIsoPullback`: under it
  `𝒪(d)` corresponds to `𝒪(d)`.
* `MMP.Intersection.ProjSpace.isoProjectiveSpaceOver`: `ℙ^{ULift (Fin (n + 1))}_k` is
  isomorphic to the Stacks base-change model `projectiveSpaceOver n (Spec k)` over `Spec k`, and
  `ProjSpace.twistOneIsoPullback`: under it the Stacks hyperplane sheaf pulls back to
  `ProjSpace.twistOne`.
* `MMP.Intersection.ProjSpace.isProper_toSpec`: `ℙ^ι_k ⟶ Spec k` is proper for finite `ι`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj HomogeneousIdeal
open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MMP.Intersection

/-! ### The twist comparison along the integral coefficient change -/

/-- **The twist comparison along `ℤ → S` is an isomorphism.** For the coefficient change
`Stacks.AlgebraicGeometry.ProjPolyChart.integralGradedHom S n` from `ℤ[T₀, …, Tₙ]` to
`S[T₀, …, Tₙ]`, the canonical comparison `r^* 𝒪(d) ⟶ 𝒪(d)` is an isomorphism, for any proof of
the containment of irrelevant ideals. -/
theorem isIso_twistMap_integralGradedHom (S : Type u) [CommRing S] (n : ℕ)
    (h : (polyGrading S n)₊ ≤ (polyGrading (ULift.{u} ℤ) n)₊.map (integralGradedHom S n))
    (d : ℤ) : IsIso (Stacks.ProjTwistComparison.twistMap (integralGradedHom S n) h d) := by
  refine Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison _ _ _ h d ?_
  refine (irrelevant_le_span_X S n).trans (Ideal.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨MvPolynomial.X i, X_mem_one _ n i, MvPolynomial.map_X _ i⟩

/-- The containment of irrelevant ideals for the coefficient change `ℤ → S`. -/
theorem irrelevant_le_map_integralGradedHom (S : Type u) [CommRing S] (n : ℕ) :
    (polyGrading S n)₊ ≤ (polyGrading (ULift.{u} ℤ) n)₊.map (integralGradedHom S n) :=
  irrelevant_le_map_coeffGradedHom _ n _

/-- The twist comparison along `ℤ → S`, as an isomorphism, for the canonical proof
`MMP.Intersection.irrelevant_le_map_integralGradedHom`. -/
def twistMapIntegralGradedHomIso (S : Type u) [CommRing S] (n : ℕ) (d : ℤ) :
    (Scheme.Modules.pullback (Proj.map (integralGradedHom S n)
        (irrelevant_le_map_integralGradedHom S n))).obj
        (twistingSheaf (polyGrading (ULift.{u} ℤ) n) d) ≅ twistingSheaf (polyGrading S n) d :=
  haveI := isIso_twistMap_integralGradedHom S n
    (irrelevant_le_map_integralGradedHom S n) d
  asIso (Stacks.ProjTwistComparison.twistMap (integralGradedHom S n) _ d)

/-- `AlgebraicGeometry.Proj.map` depends on its homomorphism only, not on the proof of the
containment of irrelevant ideals. -/
theorem projMap_congr {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (g₁ g₂ : 𝒜 →+*ᵍ ℬ) (h₁ : ℬ₊ ≤ 𝒜₊.map g₁) (h₂ : ℬ₊ ≤ 𝒜₊.map g₂) (h : g₁ = g₂) :
    Proj.map g₁ h₁ = Proj.map g₂ h₂ := by
  subst h
  rfl

/-! ### Renaming the variables -/

section Rename

variable (R : Type u) [CommRing R]

/-- Renaming the variables along `f : σ → τ`, as a homomorphism of total-degree gradings. -/
def renameGradedHom {σ τ : Type*} (f : σ → τ) :
    MvPolynomial.homogeneousSubmodule σ R →+*ᵍ MvPolynomial.homogeneousSubmodule τ R where
  toRingHom := (MvPolynomial.rename f).toRingHom
  map_mem hx := (MvPolynomial.mem_homogeneousSubmodule _ _).2
    ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hx).rename_isHomogeneous

/-- `renameGradedHom R f` acts on a polynomial as `MvPolynomial.rename f`. -/
@[simp] theorem renameGradedHom_apply {σ τ : Type*} (f : σ → τ) (p : MvPolynomial σ R) :
    renameGradedHom R f p = MvPolynomial.rename f p :=
  rfl

/-- Renaming along `f` and then along `g` is renaming along `g ∘ f`. -/
theorem renameGradedHom_comp {σ τ ρ : Type*} (f : σ → τ) (g : τ → ρ) :
    (renameGradedHom R g).comp (renameGradedHom R f) = renameGradedHom R (g ∘ f) :=
  GradedRingHom.ext (MvPolynomial.rename_rename f g)

/-- Renaming along the identity is the identity graded homomorphism. -/
theorem renameGradedHom_id {σ : Type*} :
    renameGradedHom R (id : σ → σ) = GradedRingHom.id _ :=
  GradedRingHom.ext MvPolynomial.rename_id_apply

variable (n : ℕ)

/-- Renaming along `ULift.up` followed by `ULift.down` is the identity. -/
theorem renameGradedHom_down_comp_up :
    (renameGradedHom R (ULift.down : ULift.{u} (Fin (n + 1)) → Fin (n + 1))).comp
      (renameGradedHom R ULift.up) = GradedRingHom.id (polyGrading R n) := by
  rw [renameGradedHom_comp]
  exact renameGradedHom_id R

/-- Renaming along `ULift.down` followed by `ULift.up` is the identity. -/
theorem renameGradedHom_up_comp_down :
    (renameGradedHom R (ULift.up : Fin (n + 1) → ULift.{u} (Fin (n + 1)))).comp
      (renameGradedHom R ULift.down) =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R) := by
  rw [renameGradedHom_comp]
  exact renameGradedHom_id R

/-- The irrelevant ideal of `R[T_i : i ∈ ULift (Fin (n + 1))]` is contained in the ideal generated
by the image of the irrelevant ideal of `R[T₀, …, Tₙ]` under renaming along `ULift.up`. -/
theorem irrelevant_le_map_renameGradedHom_up :
    (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R)₊ ≤
      (polyGrading R n)₊.map (renameGradedHom R ULift.up) :=
  Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse _ _
    (renameGradedHom_up_comp_down R n)

/-- The irrelevant ideal of `R[T₀, …, Tₙ]` is contained in the ideal generated by the image of
the irrelevant ideal of `R[T_i : i ∈ ULift (Fin (n + 1))]` under renaming along `ULift.down`. -/
theorem irrelevant_le_map_renameGradedHom_down :
    (polyGrading R n)₊ ≤
      (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R)₊.map
        (renameGradedHom R ULift.down) :=
  Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse _ _
    (renameGradedHom_down_comp_up R n)

/-- **`ℙ^{ULift (Fin (n + 1))}_R ≅ Proj R[T₀, …, Tₙ]`**, induced by renaming the variables. -/
def ProjSpace.isoPolyGrading :
    ProjSpace R (ULift.{u} (Fin (n + 1))) ≅ Proj (polyGrading R n) where
  hom := Proj.map (renameGradedHom R ULift.up) (irrelevant_le_map_renameGradedHom_up R n)
  inv := Proj.map (renameGradedHom R ULift.down) (irrelevant_le_map_renameGradedHom_down R n)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact (projMap_congr _ _ _ _
      (renameGradedHom_up_comp_down R n)).trans Proj.map_id
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact (projMap_congr _ _ _ _
      (renameGradedHom_down_comp_up R n)).trans Proj.map_id

/-- The forward map of `ProjSpace.isoPolyGrading` is `Proj.map` of renaming along `ULift.up`. -/
theorem ProjSpace.isoPolyGrading_hom :
    (ProjSpace.isoPolyGrading R n).hom =
      Proj.map (renameGradedHom R ULift.up) (irrelevant_le_map_renameGradedHom_up R n) :=
  rfl

/-- **`𝒪(d)` corresponds to `𝒪(d)` under the renaming isomorphism**: the twist comparison
along it is invertible. -/
theorem ProjSpace.isIso_twistMap_isoPolyGrading (d : ℤ) :
    IsIso (Stacks.ProjTwistComparison.twistMap (renameGradedHom R ULift.up)
      (irrelevant_le_map_renameGradedHom_up R n) d) :=
  Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id _ _ d _
    (renameGradedHom_up_comp_down R n) (renameGradedHom_down_comp_up R n)

/-- The twisting sheaf `𝒪(d)` on `ℙ^{ULift (Fin (n + 1))}_R` is the inverse image of `𝒪(d)` on
`Proj R[T₀, …, Tₙ]` along `ProjSpace.isoPolyGrading`; the isomorphism is the twist comparison. -/
def ProjSpace.twistingSheafIsoPullback (d : ℤ) :
    (Scheme.Modules.pullback (ProjSpace.isoPolyGrading R n).hom).obj
        (twistingSheaf (polyGrading R n) d) ≅
      twistingSheaf (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R) d :=
  @asIso _ _ _ _ _ (ProjSpace.isIso_twistMap_isoPolyGrading R n d)

end Rename

/-! ### Comparison with the base-change model `projectiveSpaceOver n (Spec k)` -/

section OverField

variable (k : Type u) [Field k] (n : ℕ)

/-- **`ℙ^{ULift (Fin (n + 1))}_k` is the Stacks base-change model of projective `n`-space over
`Spec k`**: the renaming isomorphism `ProjSpace.isoPolyGrading` followed by the inverse of the
coordinate-pinned comparison `Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`. -/
def ProjSpace.isoProjectiveSpaceOver :
    ProjSpace k (ULift.{u} (Fin (n + 1))) ≅ projectiveSpaceOver n (Spec (.of k)) :=
  ProjSpace.isoPolyGrading k n ≪≫
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).iso.symm

/-- The isomorphism `ProjSpace.isoProjectiveSpaceOver` lies over `Spec k`. -/
@[reassoc]
theorem ProjSpace.isoProjectiveSpaceOver_hom_fst :
    (ProjSpace.isoProjectiveSpaceOver k n).hom ≫ pullback.fst _ _ =
      ProjSpace.toSpec k (ULift.{u} (Fin (n + 1))) := by
  have hinv : (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).iso.inv ≫
      pullback.fst _ _ = Proj.toSpecZero (polyGrading k n) ≫
        Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' (polyGrading k n)).comp
          (algebraMap k (MvPolynomial (Fin (n + 1)) k)))) := by
    rw [← (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n).toBase,
      Iso.inv_hom_id_assoc]
  rw [ProjSpace.isoProjectiveSpaceOver, Iso.trans_hom, Iso.symm_hom, Category.assoc, hinv,
    ProjSpace.isoPolyGrading_hom, Proj.map_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ProjSpace.toSpec]
  congr 3
  refine RingHom.ext fun a => Subtype.ext ?_
  have hC : MvPolynomial.C a ∈ polyGrading k n 0 := MvPolynomial.isHomogeneous_C _ a
  have h0 := GradedRing.projZeroRingHom'_apply_coe (polyGrading k n) ⟨_, hC⟩
  change MvPolynomial.rename ULift.up
      ((GradedRing.projZeroRingHom' (polyGrading k n) (MvPolynomial.C a) : polyGrading k n 0) :
        MvPolynomial (Fin (n + 1)) k) = MvPolynomial.C a
  rw [h0, MvPolynomial.rename_C]

/-- `ProjSpace.isoProjectiveSpaceOver` lies over `Spec k`, with the structure morphism of the
base-change model spelled through its `CanonicallyOver` instance. -/
theorem ProjSpace.isoProjectiveSpaceOver_hom_over :
    (ProjSpace.isoProjectiveSpaceOver k n).hom ≫
        (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) =
      ProjSpace.toSpec k (ULift.{u} (Fin (n + 1))) :=
  ProjSpace.isoProjectiveSpaceOver_hom_fst k n

/-- Under `ProjSpace.isoProjectiveSpaceOver`, the projection of the base-change model to the
integral model is the coefficient change `ℤ → k` after renaming the variables. -/
theorem ProjSpace.isoProjectiveSpaceOver_hom_toIntegralAtUniverse :
    (ProjSpace.isoProjectiveSpaceOver k n).hom ≫
        projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)) =
      (ProjSpace.isoPolyGrading k n).hom ≫
        Proj.map (integralGradedHom k n) (irrelevant_le_map_integralGradedHom k n) := by
  rw [ProjSpace.isoProjectiveSpaceOver, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  exact congrArg ((ProjSpace.isoPolyGrading k n).hom ≫ ·) <| (projCompare_snd k n).trans
    (Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map _ _ _ _
      (mapDomain_integralGradedHom_eq_top k n))

/-- **The integral twisting sheaves pull back to the twisting sheaves of
`ℙ^{ULift (Fin (n + 1))}_k`** along `ProjSpace.isoProjectiveSpaceOver` followed by the projection
to the integral model, in every degree `d : ℤ`. The isomorphism is assembled from the twist
comparisons along the coefficient change `ℤ → k` and along the renaming of the variables. -/
def ProjSpace.pullbackTwistingSheafIso (d : ℤ) :
    (Scheme.Modules.pullback (ProjSpace.isoProjectiveSpaceOver k n).hom).obj
        ((Scheme.Modules.pullback
            (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
          (twistingSheaf (polyGrading (ULift.{u} ℤ) n) d)) ≅
      twistingSheaf (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k) d :=
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (ProjSpace.isoProjectiveSpaceOver_hom_toIntegralAtUniverse k n)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback (ProjSpace.isoPolyGrading k n).hom).mapIso
      (twistMapIntegralGradedHomIso k n d) ≪≫
    ProjSpace.twistingSheafIsoPullback k n d

/-- **The Stacks hyperplane sheaf pulls back to `ProjSpace.twistOne`** along
`ProjSpace.isoProjectiveSpaceOver`. -/
def ProjSpace.twistOneIsoPullback :
    (Scheme.Modules.pullback (ProjSpace.isoProjectiveSpaceOver k n).hom).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))) ≅
      ProjSpace.twistOne k (ULift.{u} (Fin (n + 1))) :=
  ProjSpace.pullbackTwistingSheafIso k n 1

/-! ### Properness -/

/-- The degree-zero part of `k[xᵢ : i ∈ ι]` is `k`. -/
theorem bijective_algebraMap_homogeneousSubmodule_zero (ι : Type u) :
    Function.Bijective (algebraMap k (MvPolynomial.homogeneousSubmodule ι k 0)) := by
  refine ⟨fun a b h => MvPolynomial.C_injective _ _ (congrArg Subtype.val h), ?_⟩
  rintro ⟨x, hx⟩
  rw [MvPolynomial.mem_homogeneousSubmodule] at hx
  by_cases h0 : x = 0
  · exact ⟨0, Subtype.ext (by simp [h0])⟩
  · have h := hx.totalDegree h0
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h
    exact ⟨x.coeff 0, Subtype.ext (by simpa using h.symm)⟩

/-- **Projective space over a field is proper**: `ℙ^ι_k ⟶ Spec k` is proper for finite `ι`. -/
instance ProjSpace.isProper_toSpec (ι : Type u) [Finite ι] :
    IsProper (ProjSpace.toSpec k ι) := by
  have : IsIso (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule ι k 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_algebraMap_homogeneousSubmodule_zero k ι)
  unfold ProjSpace.toSpec
  infer_instance

end OverField

end MMP.Intersection

end
