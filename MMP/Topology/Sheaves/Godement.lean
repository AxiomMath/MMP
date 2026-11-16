module

public import MMP.Attr
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The Godement resolution and hypercohomology

Let `T` be a topological space. For a sheaf of abelian groups `F` on `T`, the *Godement sheaf*
`G(F)` is the sheaf of discontinuous sections, `G(F)(U) = ∏_{x ∈ U} F_x`, and `s ↦ (s_x)_x` is an
injection `F ⟶ G(F)`. The *Godement resolution* is `G^0(F) = G(F)` and
`G^{n+1}(F) = G(coker(G^{n-1}(F) ⟶ G^n(F)))`, with `G^{-1}(F) = F`, the differential
`G^n(F) ⟶ G^{n+1}(F)` being the projection to the cokernel followed by the injection into `G`.

For a complex `K^•` of sheaves of abelian groups, `G^•(K^•)` is a double complex and the
*hypercohomology* of `K^•` is `ℍ^n(T, K^•) = H^n(Tot Γ(T, G^•(K^•)))`; the cohomology of a sheaf
is the hypercohomology of the complex concentrated in degree `0`.

For a continuous map `f : T' ⟶ T`, the maps
`Γ(U, G(F)) = ∏_{x ∈ U} F_x ⟶ ∏_{y ∈ f⁻¹ U} F_{f y}`, `(s_x) ↦ (s_{f y})`, composed with
`∏_{y ∈ f⁻¹ U} F_{f y} ⟶ ∏_{y ∈ f⁻¹ U} (f⁻¹ F)_y = Γ(f⁻¹ U, G(f⁻¹ F))` and induced inductively on
all `G^n`, give the pullback `f^* : ℍ^n(T, K^•) ⟶ ℍ^n(T', f⁻¹ K^•)`.

## Main definitions

* `MMP.Analytic.CokernelCoresolution.complexFunctor`: for an endofunctor `G` of a category
  with zero morphisms and cokernels and a natural transformation `η : 𝟭 ⟶ G`, the complex
  `G(F) ⟶ G(coker η_F) ⟶ ⋯` built from cokernels, functorial in `F`.
* `MMP.Analytic.CokernelCoresolution.complexHom`: the map of such complexes `G^•(F) ⟶ P G'^•(B)`
  induced by a map `F ⟶ P B` and a compatible way (`CokernelCoresolution.Lift`) of lifting maps
  `A ⟶ P B` to `G A ⟶ P (G' B)`.
* `MMP.Analytic.godementFunctor`, `MMP.Analytic.godementUnit`: the Godement sheaf `G(F)` and the
  injection `F ⟶ G(F)`.
* `MMP.Analytic.godementResolution`, `MMP.Analytic.godementAugmentation`: the Godement resolution
  as a functor to cochain complexes, and its augmentation `F[0] ⟶ G^•(F)`.
* `MMP.Analytic.godementDoubleComplex`: the double complex `G^•(K^•)` of a complex of sheaves.
* `MMP.Analytic.hypercohomology`: `ℍ^n(T, -)`, a functor on cochain complexes of sheaves.
* `MMP.Analytic.sheafCohomology`: `H^n(T, F) = ℍ^n(T, F[0])`, a functor on sheaves.
* `MMP.Analytic.godementResolutionPullback`: the comparison `G^•(F) ⟶ f_* G^•(f⁻¹ F)`.
* `MMP.Analytic.hypercohomologyPullback`: the pullback `f^* : ℍ^n(T, K) ⟶ ℍ^n(T', f⁻¹ K)`.
* `MMP.Analytic.sheafCohomologyPullback`: the pullback `f^* : H^n(T, F) ⟶ H^n(T', f⁻¹ F)`.

## Main results

* `MMP.Analytic.godementUnit_app_hom_app_injective`: `F ⟶ G(F)` is injective on sections.
* `MMP.Analytic.godementResolution_map_comp_godementResolutionPullback`: the comparison of
  Godement resolutions along `f` is natural in the sheaf.
* `MMP.Analytic.hypercohomology_map_comp_hypercohomologyPullback`: the pullback on
  hypercohomology is natural in the complex.

## Implementation notes

* The Godement sheaf is the presheaf of dependent functions `x ↦ s_x ∈ F_x`; its sheaf condition
  is that of the sheaf of discontinuous sections of a family of types.
* The construction of the resolution from cokernels, of its maps and of their naturality, is
  carried out for an arbitrary augmented endofunctor of a preadditive category with cokernels,
  and specialised to `G`.
* In the pullback, the identification `F_{f y} ⟶ (f⁻¹ F)_y` is the stalk at `f y` of the unit
  `F ⟶ f_* f⁻¹ F` of the inverse image adjunction, followed by `(f_* f⁻¹ F)_{f y} ⟶ (f⁻¹ F)_y`.
  In higher degrees the map `G^{n+1}(F) ⟶ f_* G^{n+1}(f⁻¹ F)` is the lift of the map of
  cokernels induced by the maps in degrees `n - 1` and `n`.
* The complex `K^•` is any `ℤ`-indexed cochain complex, not only one bounded in degrees
  `[0, m]`. The Godement degree is extended by zero from `ℕ` to `ℤ`; the term of bidegree `(q, p)`
  of the double complex is `G^p(K^q)`, and the total complex is formed with direct sums.
* Global sections are taken before the total complex: `ℍ^n(T, K) = H^n(Tot Γ(T, G^•(K^•)))`.
  For a bounded complex `K^•`, as in the source, every antidiagonal is finite and `Γ(T, -)`
  commutes with the finite direct sums of the total complex, so this is `H^n(Γ(T, Tot G^•(K^•)))`.
* The pullback on sheaf cohomology lands in `H^n(T', f⁻¹ F)` through the identification
  `f⁻¹ (F[0]) ≅ (f⁻¹ F)[0]`.

## References

* [R. Godement, *Topologie algébrique et théorie des faisceaux*]
* [Serre, *Géométrie algébrique et géométrie analytique*]
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe v u v' u'

namespace MMP.Analytic

namespace CokernelCoresolution

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]
  (G : C ⥤ C) (η : 𝟭 C ⟶ G)

/-- The `n`-th stage `(G^{n-1}(F), G^n(F), d^{n-1})` of the coresolution of `F` built from `η`
and cokernels, with `G^{-1}(F) = F`. -/
def stage (F : C) : ℕ → Σ (X : C), Σ (Y : C), (X ⟶ Y)
  | 0 => ⟨F, G.obj F, η.app F⟩
  | n + 1 => ⟨(stage F n).2.1, G.obj (cokernel (stage F n).2.2),
      cokernel.π (stage F n).2.2 ≫ η.app (cokernel (stage F n).2.2)⟩

/-- The term `G^n(F)` of the coresolution. -/
abbrev X (F : C) (n : ℕ) : C := (stage G η F n).2.1

/-- The differential `G^n(F) ⟶ G^{n+1}(F)`. -/
abbrev d (F : C) (n : ℕ) : X G η F n ⟶ X G η F (n + 1) := (stage G η F (n + 1)).2.2

/-- The differential `G^0(F) ⟶ G^1(F)` is the projection to `coker η_F` followed by `η`. -/
lemma d_zero (F : C) : d G η F 0 = cokernel.π (η.app F) ≫ η.app (cokernel (η.app F)) := rfl

/-- The differential `G^{n+1}(F) ⟶ G^{n+2}(F)` is the projection to the cokernel of
`G^n(F) ⟶ G^{n+1}(F)` followed by `η`. -/
lemma d_succ (F : C) (n : ℕ) :
    d G η F (n + 1) = cokernel.π (d G η F n) ≫ η.app (cokernel (d G η F n)) :=
  rfl

/-- The composite `F ⟶ G^0(F) ⟶ G^1(F)` is zero. -/
@[reassoc (attr := simp)]
lemma app_comp_d_zero (F : C) : η.app F ≫ d G η F 0 = 0 :=
  (cokernel.condition_assoc (η.app F) (η.app (cokernel (η.app F)))).trans zero_comp

/-- Two consecutive differentials of the coresolution compose to zero. -/
@[reassoc (attr := simp)]
lemma d_comp_d (F : C) (n : ℕ) : d G η F n ≫ d G η F (n + 1) = 0 :=
  (cokernel.condition_assoc (d G η F n) (η.app (cokernel (d G η F n)))).trans zero_comp

/-- The coresolution `G^0(F) ⟶ G^1(F) ⟶ ⋯` as a cochain complex. -/
def complex (F : C) : CochainComplex C ℕ :=
  CochainComplex.of (X G η F) (d G η F) (d_comp_d G η F)

/-- The `n`-th term of `complex G η F` is `G^n(F)`. -/
@[simp]
lemma complex_X (F : C) (n : ℕ) : (complex G η F).X n = X G η F n := rfl

/-- The differential of `complex G η F` in degree `n` is `d G η F n`. -/
@[simp]
lemma complex_d (F : C) (n : ℕ) : (complex G η F).d n (n + 1) = d G η F n := by
  simp [complex]

variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasCokernels D]
  (G' : D ⥤ D) (η' : 𝟭 D ⟶ G') (P : D ⥤ C)

/-- A way of lifting maps `A ⟶ P B` to maps `G A ⟶ P (G' B)`, compatible with the
augmentations and natural in `A` and `B`. -/
structure Lift where
  /-- The lifted map. -/
  lift {A : C} {B : D} : (A ⟶ P.obj B) → (G.obj A ⟶ P.obj (G'.obj B))
  app_comp_lift {A : C} {B : D} (φ : A ⟶ P.obj B) : η.app A ≫ lift φ = φ ≫ P.map (η'.app B)
  lift_precomp {A A' : C} {B : D} (a : A ⟶ A') (φ : A' ⟶ P.obj B) :
    lift (a ≫ φ) = G.map a ≫ lift φ
  lift_postcomp {A : C} {B B' : D} (φ : A ⟶ P.obj B) (b : B ⟶ B') :
    lift (φ ≫ P.map b) = lift φ ≫ P.map (G'.map b)

variable {G η G' η' P}
variable [P.PreservesZeroMorphisms]

/-- A map of stages in degree `n`: maps `a`, `b` of the two terms commuting with the maps of
the stages. -/
abbrev StageHom (F : C) (B : D) (n : ℕ) : Type _ :=
  Σ' (a : (stage G η F n).1 ⟶ P.obj (stage G' η' B n).1)
      (b : (stage G η F n).2.1 ⟶ P.obj (stage G' η' B n).2.1),
        (stage G η F n).2.2 ≫ b = a ≫ P.map (stage G' η' B n).2.2

/-- The map of cokernels induced by a map of stages. -/
def cokerDesc {F : C} {B : D} {n : ℕ} (p : StageHom (G := G) (η := η) (G' := G') (η' := η')
    (P := P) F B n) :
    cokernel (stage G η F n).2.2 ⟶ P.obj (cokernel (stage G' η' B n).2.2) :=
  cokernel.desc _ (p.2.1 ≫ P.map (cokernel.π _)) (by
    rw [← Category.assoc, p.2.2, Category.assoc, ← P.map_comp, cokernel.condition,
      Functor.map_zero, comp_zero])

/-- The map of cokernels induced by a map of stages commutes with the projections. -/
@[reassoc (attr := simp)]
lemma π_cokerDesc {F : C} {B : D} {n : ℕ} (p : StageHom (G := G) (η := η) (G' := G') (η' := η')
    (P := P) F B n) :
    cokernel.π _ ≫ cokerDesc p = p.2.1 ≫ P.map (cokernel.π _) :=
  cokernel.π_desc _ _ _

/-- The maps of stages induced by a lift and a map `F ⟶ P B`. -/
def stageHom (Λ : Lift G η G' η' P) {F : C} {B : D} (φ : F ⟶ P.obj B) :
    ∀ n : ℕ, StageHom (G := G) (η := η) (G' := G') (η' := η') (P := P) F B n
  | 0 => ⟨φ, Λ.lift φ, Λ.app_comp_lift φ⟩
  | n + 1 =>
    ⟨(stageHom Λ φ n).2.1, Λ.lift (cokerDesc (stageHom Λ φ n)), by
        dsimp only [stage]
        rw [Category.assoc, Λ.app_comp_lift, π_cokerDesc_assoc, P.map_comp]⟩

variable (Λ : Lift G η G' η' P) {F : C} {B : D} (φ : F ⟶ P.obj B)

/-- The component `G^n(F) ⟶ P (G'^n(B))` of the map of coresolutions induced by `φ`. -/
abbrev homX (n : ℕ) : X G η F n ⟶ P.obj (X G' η' B n) := (stageHom Λ φ n).2.1

/-- In degree `0`, the map of coresolutions is the lift of `φ`. -/
lemma homX_zero : homX Λ φ 0 = Λ.lift φ := rfl

/-- In degree `n + 1`, the map of coresolutions is the lift of the induced map of cokernels. -/
lemma homX_succ (n : ℕ) : homX Λ φ (n + 1) = Λ.lift (cokerDesc (stageHom Λ φ n)) :=
  rfl

/-- The map of coresolutions in degree `0` is compatible with the augmentations. -/
@[reassoc]
lemma app_comp_homX_zero : η.app F ≫ homX Λ φ 0 = φ ≫ P.map (η'.app B) :=
  Λ.app_comp_lift φ

/-- The components of the map of coresolutions commute with the differentials. -/
@[reassoc]
lemma d_comp_homX (n : ℕ) :
    d G η F n ≫ homX Λ φ (n + 1) = homX Λ φ n ≫ P.map (d G' η' B n) :=
  (stageHom Λ φ (n + 1)).2.2

/-- The map of coresolutions `G^•(F) ⟶ P (G'^•(B))` induced by `φ : F ⟶ P B`. -/
def complexHom : complex G η F ⟶ (P.mapHomologicalComplex _).obj (complex G' η' B) where
  f n := homX Λ φ n
  comm' i j h := by
    obtain rfl : i + 1 = j := h
    simpa using (d_comp_homX Λ φ i).symm

/-- The `n`-th component of `complexHom Λ φ` is `homX Λ φ n`. -/
@[simp]
lemma complexHom_f (n : ℕ) : (complexHom Λ φ).f n = homX Λ φ n := rfl

variable (G η) in
/-- The lift of maps given by the functor `G` itself. -/
@[simps]
def idLift : Lift G η G η (𝟭 C) where
  lift φ := G.map φ
  app_comp_lift φ := (η.naturality φ).symm
  lift_precomp a φ := G.map_comp a φ
  lift_postcomp φ b := G.map_comp φ b

/-- The maps of coresolutions are natural: a commutative square `a ≫ φ' = φ ≫ P b` induces
a commutative square of coresolutions in every degree. -/
lemma homX_comp_homX {F F' : C} {B B' : D} (a : F ⟶ F') (b : B ⟶ B') (φ : F ⟶ P.obj B)
    (φ' : F' ⟶ P.obj B') (h : a ≫ φ' = φ ≫ P.map b) (n : ℕ) :
    homX (idLift G η) a n ≫ homX Λ φ' n = homX Λ φ n ≫ P.map (homX (idLift G' η') b n) := by
  suffices H : ∀ n, (stageHom (idLift G η) a n).1 ≫ (stageHom Λ φ' n).1 =
      (stageHom Λ φ n).1 ≫ P.map (stageHom (idLift G' η') b n).1 ∧
      homX (idLift G η) a n ≫ homX Λ φ' n = homX Λ φ n ≫ P.map (homX (idLift G' η') b n) from
    (H n).2
  intro n
  induction n with
  | zero =>
    refine ⟨h, ?_⟩
    change G.map a ≫ Λ.lift φ' = Λ.lift φ ≫ P.map (G'.map b)
    rw [← Λ.lift_precomp, h, Λ.lift_postcomp]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    change G.map (cokerDesc (stageHom (idLift G η) a n)) ≫ Λ.lift (cokerDesc (stageHom Λ φ' n)) =
      Λ.lift (cokerDesc (stageHom Λ φ n)) ≫
        P.map (G'.map (cokerDesc (stageHom (idLift G' η') b n)))
    rw [← Λ.lift_precomp, ← Λ.lift_postcomp]
    congr 1
    refine coequalizer.hom_ext ?_
    change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
    rw [π_cokerDesc_assoc, π_cokerDesc_assoc, ← P.map_comp, π_cokerDesc]
    change homX (idLift G η) a n ≫ cokernel.π _ ≫ _ = _
    rw [π_cokerDesc, reassoc_of% ih.2, P.map_comp]
    rfl

/-- The map of coresolutions induced by the identity is the identity. -/
lemma homX_id (F : C) (n : ℕ) : homX (idLift G η) (𝟙 F) n = 𝟙 _ := by
  suffices H : ∀ n, (stageHom (idLift G η) (𝟙 F) n).1 = 𝟙 _ ∧
      homX (idLift G η) (𝟙 F) n = 𝟙 _ from (H n).2
  intro n
  induction n with
  | zero => exact ⟨rfl, G.map_id F⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : cokerDesc (stageHom (idLift G η) (𝟙 F) n) = 𝟙 (cokernel (stage G η F n).2.2) := by
      refine coequalizer.hom_ext ?_
      change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
      rw [π_cokerDesc, Category.comp_id]
      change homX (idLift G η) (𝟙 F) n ≫ cokernel.π _ = _
      rw [ih.2, Category.id_comp]
    change G.map (cokerDesc (stageHom (idLift G η) (𝟙 F) n)) = _
    rw [e, G.map_id]
    rfl

/-- The map of coresolutions induced by a composite is the composite of the induced maps. -/
lemma homX_comp {F F' F'' : C} (a : F ⟶ F') (b : F' ⟶ F'') (n : ℕ) :
    homX (idLift G η) (a ≫ b) n = homX (idLift G η) a n ≫ homX (idLift G η) b n := by
  simpa [homX_id] using (homX_comp_homX (idLift G η) a (𝟙 F'') (a ≫ b) b (by simp) n).symm

/-- The map of coresolutions induced by the zero map is zero. -/
lemma homX_zero_hom [G.PreservesZeroMorphisms] (F F' : C) (n : ℕ) :
    homX (idLift G η) (0 : F ⟶ F') n = 0 := by
  suffices H : ∀ n, (stageHom (idLift G η) (0 : F ⟶ F') n).1 = 0 ∧
      homX (idLift G η) (0 : F ⟶ F') n = 0 from (H n).2
  intro n
  induction n with
  | zero => exact ⟨rfl, G.map_zero F F'⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : cokerDesc (stageHom (idLift G η) (0 : F ⟶ F') n) =
        (0 : cokernel (stage G η F n).2.2 ⟶ cokernel (stage G η F' n).2.2) := by
      refine coequalizer.hom_ext ?_
      change cokernel.π _ ≫ _ = cokernel.π _ ≫ _
      rw [π_cokerDesc, comp_zero]
      change homX (idLift G η) (0 : F ⟶ F') n ≫ cokernel.π _ = _
      rw [ih.2, zero_comp]
    change G.map (cokerDesc (stageHom (idLift G η) (0 : F ⟶ F') n)) = _
    rw [e, G.map_zero]
    rfl

variable (G η) in
/-- The coresolution `F ↦ G^•(F)` as a functor to cochain complexes. -/
def complexFunctor : C ⥤ CochainComplex C ℕ where
  obj F := complex G η F
  map a := complexHom (idLift G η) a
  map_id F := by ext n; exact homX_id F n
  map_comp a b := by ext n; exact homX_comp a b n

/-- The `n`-th component of `(complexFunctor G η).map a` is `homX (idLift G η) a n`. -/
@[simp]
lemma complexFunctor_map_f {F F' : C} (a : F ⟶ F') (n : ℕ) :
    ((complexFunctor G η).map a).f n = homX (idLift G η) a n := rfl

/-- The functor `complexFunctor G η` preserves zero morphisms when `G` does. -/
instance [G.PreservesZeroMorphisms] : (complexFunctor G η).PreservesZeroMorphisms where
  map_zero F F' := by ext n; exact homX_zero_hom F F' n

/-- The naturality of `complexHom` with respect to commutative squares. -/
@[reassoc]
lemma complexFunctor_map_comp_complexHom {F F' : C} {B B' : D} (a : F ⟶ F') (b : B ⟶ B')
    (φ : F ⟶ P.obj B) (φ' : F' ⟶ P.obj B') (h : a ≫ φ' = φ ≫ P.map b) :
    (complexFunctor G η).map a ≫ complexHom Λ φ' =
      complexHom Λ φ ≫ (P.mapHomologicalComplex _).map ((complexFunctor G' η').map b) := by
  ext n
  exact homX_comp_homX Λ a b φ φ' h n

variable [HasZeroObject C]

variable (G η) in
/-- The augmentation `F[0] ⟶ G^•(F)`, given by `η` in degree `0`. -/
def augmentation (F : C) : (CochainComplex.single₀ C).obj F ⟶ complex G η F :=
  HomologicalComplex.mkHomFromSingle (η.app F) (fun k (hk : 0 + 1 = k) => by
    subst hk; rw [complex_d]; exact app_comp_d_zero G η F)

/-- In degree `0`, the augmentation `F[0] ⟶ G^•(F)` is `η_F`, through `F[0]^0 ≅ F`. -/
lemma augmentation_f_zero (F : C) :
    (augmentation G η F).f 0 = (HomologicalComplex.singleObjXSelf _ 0 F).hom ≫ η.app F :=
  HomologicalComplex.mkHomFromSingle_f _ _

end CokernelCoresolution

section Sheaves

open TopCat TopCat.Presheaf

variable {T : TopCat.{u}}

/-- Two maps of sheaves of abelian groups agreeing on all sections are equal. -/
lemma sheafHom_ext {F F' : TopCat.Sheaf AddCommGrpCat.{u} T} {a b : F ⟶ F'}
    (h : ∀ (U : (Opens T)ᵒᵖ) (s : F.presheaf.obj U), a.hom.app U s = b.hom.app U s) : a = b :=
  InducedCategory.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.ext (h U)))

/-- The presheaf of discontinuous sections of a presheaf `F` of abelian groups:
`U ↦ ∏_{x ∈ U} F_x`, with restriction given by restricting families of germs. -/
def discontinuousSections (F : TopCat.Presheaf AddCommGrpCat.{u} T) :
    TopCat.Presheaf AddCommGrpCat.{u} T where
  obj U := AddCommGrpCat.of ((x : U.unop) → F.stalk x)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s x => s (i.unop x)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Restriction of discontinuous sections restricts the family of germs. -/
@[simp]
lemma discontinuousSections_map_apply (F : TopCat.Presheaf AddCommGrpCat.{u} T)
    {U V : (Opens T)ᵒᵖ} (i : U ⟶ V) (s : (x : U.unop) → F.stalk x) (x : V.unop) :
    (discontinuousSections F).map i s x = s (i.unop x) := rfl

/-- The presheaf of discontinuous sections is a sheaf. -/
lemma isSheaf_discontinuousSections (F : TopCat.Presheaf AddCommGrpCat.{u} T) :
    (discontinuousSections F).IsSheaf := by
  rw [isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  exact TopCat.Presheaf.toTypes_isSheaf T (fun x => F.stalk x)

/-- The map of discontinuous sections induced by a map of presheaves, acting by the stalk maps. -/
def discontinuousSectionsMap {F F' : TopCat.Presheaf AddCommGrpCat.{u} T} (a : F ⟶ F') :
    discontinuousSections F ⟶ discontinuousSections F' where
  app _ := AddCommGrpCat.ofHom (AddMonoidHom.pi fun x =>
    ((stalkFunctor AddCommGrpCat x.1).map a).hom.comp (Pi.evalAddMonoidHom _ x))
  naturality _ _ _ := rfl

/-- The map of discontinuous sections induced by `a` acts on each germ by the stalk map of `a`. -/
@[simp]
lemma discontinuousSectionsMap_app_apply {F F' : TopCat.Presheaf AddCommGrpCat.{u} T}
    (a : F ⟶ F') (U : (Opens T)ᵒᵖ) (s : (x : U.unop) → F.stalk x) (x : U.unop) :
    (discontinuousSectionsMap a).app U s x = (stalkFunctor AddCommGrpCat x.1).map a (s x) := rfl

variable (T) in
/-- The Godement sheaf `G(F)` of a sheaf of abelian groups `F`: the sheaf of discontinuous
sections `G(F)(U) = ∏_{x ∈ U} F_x`, as a functor of `F`. -/
@[mmp "def_mmp_gaga_godement"]
def godementFunctor : TopCat.Sheaf AddCommGrpCat.{u} T ⥤ TopCat.Sheaf AddCommGrpCat.{u} T where
  obj F := ⟨discontinuousSections F.presheaf, isSheaf_discontinuousSections _⟩
  map a := ObjectProperty.homMk (discontinuousSectionsMap a.hom)
  map_id F := sheafHom_ext fun U s => funext fun x => by
    change (stalkFunctor AddCommGrpCat x.1).map (𝟙 F.presheaf) (s x) = s x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp a b := sheafHom_ext fun U s => funext fun x => by
    change (stalkFunctor AddCommGrpCat x.1).map (a.hom ≫ b.hom) (s x) =
      (stalkFunctor AddCommGrpCat x.1).map b.hom ((stalkFunctor AddCommGrpCat x.1).map a.hom (s x))
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- The underlying presheaf of `G(F)` is the presheaf of discontinuous sections of `F`. -/
@[simp]
lemma godementFunctor_obj_obj (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    ((godementFunctor T).obj F).obj = discontinuousSections F.presheaf := rfl

/-- The map `G(F) ⟶ G(F')` induced by `a` is the map of discontinuous sections of `a`. -/
@[simp]
lemma godementFunctor_map_hom {F F' : TopCat.Sheaf AddCommGrpCat.{u} T} (a : F ⟶ F') :
    ((godementFunctor T).map a).hom = discontinuousSectionsMap a.hom := rfl

/-- The Godement functor preserves zero morphisms. -/
instance : (godementFunctor T).PreservesZeroMorphisms where
  map_zero F F' := sheafHom_ext fun U s => funext fun x => by
    change (stalkFunctor AddCommGrpCat x.1).map (0 : F.presheaf ⟶ F'.presheaf) (s x) = 0
    rw [CategoryTheory.Functor.map_zero]
    rfl

variable (T) in
/-- The injection `F ⟶ G(F)`, `s ↦ (s_x)_x`. -/
@[mmp "def_mmp_gaga_godement"]
def godementUnit : 𝟭 (TopCat.Sheaf AddCommGrpCat.{u} T) ⟶ godementFunctor T where
  app F := ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.pi fun x => (F.presheaf.germ U.unop x.1 x.2).hom)
      naturality _ _ i := AddCommGrpCat.ext fun s => funext fun x =>
        germ_res_apply' F.presheaf i x.1 x.2 s }
  naturality _ _ a := sheafHom_ext fun U s => funext fun x =>
    (stalkFunctor_map_germ_apply U.unop x.1 x.2 a.hom s).symm

/-- The injection `F ⟶ G(F)` sends a section `s` over `U` to its family of germs
`(s_x)_{x ∈ U}`. -/
@[simp]
lemma godementUnit_app_hom_app_apply (F : TopCat.Sheaf AddCommGrpCat.{u} T) (U : (Opens T)ᵒᵖ)
    (s : F.presheaf.obj U) (x : U.unop) :
    ((godementUnit T).app F).hom.app U s x = F.presheaf.germ U.unop x.1 x.2 s := rfl

/-- The map `F ⟶ G(F)`, `s ↦ (s_x)_x`, is injective on sections. -/
lemma godementUnit_app_hom_app_injective (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (U : (Opens T)ᵒᵖ) : Function.Injective (((godementUnit T).app F).hom.app U) :=
  fun s t h => section_ext F U.unop s t fun x hx => congrFun h ⟨x, hx⟩

section Pullback

variable {T' : TopCat.{u}} (f : T' ⟶ T)

/-- The stalk maps `(f_* B)_{f y} ⟶ B_y` are natural in `B`. -/
@[reassoc, elementwise]
lemma stalkFunctor_map_pushforward_comp_stalkPushforward
    {B B' : TopCat.Presheaf AddCommGrpCat.{u} T'} (b : B ⟶ B') (y : T') :
    (stalkFunctor AddCommGrpCat (f y)).map ((Presheaf.pushforward AddCommGrpCat f).map b) ≫
        B'.stalkPushforward AddCommGrpCat f y =
      B.stalkPushforward AddCommGrpCat f y ≫ (stalkFunctor AddCommGrpCat y).map b := by
  refine stalk_hom_ext _ fun U hU => ?_
  erw [stalkFunctor_map_germ_assoc, stalkPushforward_germ, stalkPushforward_germ_assoc,
    stalkFunctor_map_germ]
  rfl

/-- For `φ : A ⟶ f_* B`, the map `G(A) ⟶ f_* G(B)` sending `(s_x)_{x ∈ U}` to
`(φ_{f y}(s_{f y}))_{y ∈ f⁻¹ U}`, the stalk maps read through `(f_* B)_{f y} ⟶ B_y`. -/
def godementLiftHom {A : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B) :
    (godementFunctor T).obj A ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat f).obj ((godementFunctor T').obj B) :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.pi fun (y : (Opens.map f).obj U.unop) =>
        ((B.presheaf.stalkPushforward AddCommGrpCat f y).hom.comp
          ((stalkFunctor AddCommGrpCat (f y)).map φ.hom).hom).comp
          (Pi.evalAddMonoidHom (fun x : U.unop => A.presheaf.stalk x) ⟨f y, y.2⟩))
      naturality _ _ _ := rfl }

/-- The map `G(A) ⟶ f_* G(B)` sends `(s_x)_{x ∈ U}` to `(φ_{f y}(s_{f y}))_{y ∈ f⁻¹ U}`, read
through `(f_* B)_{f y} ⟶ B_y`. -/
@[simp]
lemma godementLiftHom_hom_app_apply {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj B) (U : (Opens T)ᵒᵖ)
    (s : (x : U.unop) → A.presheaf.stalk x) (y : (Opens.map f).obj U.unop) :
    (godementLiftHom f φ).hom.app U s y =
      B.presheaf.stalkPushforward AddCommGrpCat f y
        ((stalkFunctor AddCommGrpCat (f y)).map φ.hom (s ⟨f y, y.2⟩)) := rfl

/-- The lifts `G(A) ⟶ f_* G(B)` of maps `A ⟶ f_* B` along a continuous map `f : T' ⟶ T`. -/
def godementPullbackLift :
    CokernelCoresolution.Lift (godementFunctor T) (godementUnit T) (godementFunctor T')
      (godementUnit T') (TopCat.Sheaf.pushforward AddCommGrpCat f) where
  lift φ := godementLiftHom f φ
  app_comp_lift {A B} φ := sheafHom_ext fun U s => funext fun y =>
    (congrArg (B.presheaf.stalkPushforward AddCommGrpCat f y)
      (stalkFunctor_map_germ_apply U.unop (f y) y.2 φ.hom s)).trans
      (stalkPushforward_germ_apply _ _ _ _ _ _ _)
  lift_precomp {A A' B} a φ := sheafHom_ext fun U s => funext fun y => by
    change B.presheaf.stalkPushforward AddCommGrpCat f y
        ((stalkFunctor AddCommGrpCat (f y)).map (a.hom ≫ φ.hom) (s ⟨f y, y.2⟩)) =
      B.presheaf.stalkPushforward AddCommGrpCat f y
        ((stalkFunctor AddCommGrpCat (f y)).map φ.hom
          ((stalkFunctor AddCommGrpCat (f y)).map a.hom (s ⟨f y, y.2⟩)))
    rw [CategoryTheory.Functor.map_comp]
    rfl
  lift_postcomp {A B B'} φ b := sheafHom_ext fun U s => funext fun y => by
    change B'.presheaf.stalkPushforward AddCommGrpCat.{u} f y
        ((stalkFunctor AddCommGrpCat.{u} (f y)).map
          (φ.hom ≫ (Presheaf.pushforward AddCommGrpCat.{u} f).map b.hom) (s ⟨f y, y.2⟩)) =
      (stalkFunctor AddCommGrpCat.{u} y).map b.hom
        (B.presheaf.stalkPushforward AddCommGrpCat.{u} f y
        ((stalkFunctor AddCommGrpCat.{u} (f y)).map φ.hom (s ⟨f y, y.2⟩)))
    have h1 := ConcreteCategory.congr_hom
      ((stalkFunctor AddCommGrpCat.{u} (f y)).map_comp φ.hom
        ((Presheaf.pushforward AddCommGrpCat.{u} f).map b.hom)) (s ⟨f y, y.2⟩)
    exact (congrArg (B'.presheaf.stalkPushforward AddCommGrpCat.{u} f y) h1).trans
      (stalkFunctor_map_pushforward_comp_stalkPushforward_apply f b.hom y _)

end Pullback

end Sheaves

section Hypercohomology

variable (T : TopCat.{u})

/-- The **Godement resolution** `F ↦ G^•(F)` of sheaves of abelian groups:
`G^0(F) = G(F)` and `G^{n+1}(F) = G(coker(G^{n-1}(F) ⟶ G^n(F)))`, with `G^{-1}(F) = F`. -/
@[mmp "def_mmp_gaga_godement"]
def godementResolution :
    TopCat.Sheaf AddCommGrpCat.{u} T ⥤ CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℕ :=
  CokernelCoresolution.complexFunctor (godementFunctor T) (godementUnit T)

/-- The Godement resolution preserves zero morphisms. -/
instance : (godementResolution T).PreservesZeroMorphisms :=
  inferInstanceAs (CokernelCoresolution.complexFunctor _ _).PreservesZeroMorphisms

/-- The term `G^0(F)` of the Godement resolution is `G(F)`. -/
lemma godementResolution_X_zero (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    ((godementResolution T).obj F).X 0 = (godementFunctor T).obj F := rfl

/-- The term `G^1(F)` of the Godement resolution is `G(coker(F ⟶ G(F)))`. -/
lemma godementResolution_X_one (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    ((godementResolution T).obj F).X 1 =
      (godementFunctor T).obj (cokernel ((godementUnit T).app F)) := rfl

/-- The term `G^{n+2}(F)` of the Godement resolution is `G(coker(G^n(F) ⟶ G^{n+1}(F)))`. -/
lemma godementResolution_X_add_two (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) :
    ((godementResolution T).obj F).X (n + 2) = (godementFunctor T).obj
      (cokernel (((godementResolution T).obj F).d n (n + 1))) := by
  simp only [godementResolution, CokernelCoresolution.complexFunctor,
    CokernelCoresolution.complex_d]
  rfl

/-- The augmentation `F[0] ⟶ G^•(F)`, given by the injection `F ⟶ G(F)` in degree `0`. -/
def godementAugmentation (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (CochainComplex.single₀ _).obj F ⟶ (godementResolution T).obj F :=
  CokernelCoresolution.augmentation (godementFunctor T) (godementUnit T) F

/-- The global sections functor `Γ(T, -)` on sheaves of abelian groups. -/
abbrev globalSections : TopCat.Sheaf AddCommGrpCat.{u} T ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{u}).obj (op ⊤)

/-- The global sections functor preserves zero morphisms. -/
instance : (globalSections T).PreservesZeroMorphisms :=
  inferInstanceAs ((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{u}).obj
    (op ⊤)).PreservesZeroMorphisms

/-- The complex `Γ(T, G^•(F))`, extended by zero to an `ℤ`-indexed cochain complex. -/
def godementSections : TopCat.Sheaf AddCommGrpCat.{u} T ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  godementResolution T ⋙ (globalSections T).mapHomologicalComplex _ ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}

/-- The functor `F ↦ Γ(T, G^•(F))` preserves zero morphisms. -/
instance : (godementSections T).PreservesZeroMorphisms := by
  dsimp only [godementSections]
  infer_instance

/-- The **Godement double complex** `G^•(K^•)` of a complex of sheaves `K`: the term of bidegree
`(q, p)` is `G^p(K^q)`. -/
@[mmp "def_mmp_gaga_godement"]
def godementDoubleComplex (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) :
    HomologicalComplex₂ (TopCat.Sheaf AddCommGrpCat.{u} T) (ComplexShape.up ℤ)
      (ComplexShape.up ℕ) :=
  ((godementResolution T).mapHomologicalComplex _).obj K

/-- The double complex `Γ(T, G^•(K^•))`, the Godement degree extended by zero to `ℤ`. -/
abbrev godementSectionsDoubleComplex (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((godementSections T).mapHomologicalComplex _).obj K

/-- The **hypercohomology** `ℍ^n(T, K^•) = H^n(Tot Γ(T, G^•(K^•)))` of a complex of sheaves of
abelian groups, as a functor of the complex. -/
@[mmp "def_mmp_gaga_godement"]
def hypercohomology (n : ℤ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ ⥤ AddCommGrpCat.{u} :=
  (godementSections T).mapHomologicalComplex _ ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (c₁₂ := ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor _ _ n

/-- `ℍ^n(T, K^•)` is the `n`-th cohomology of the total complex of `Γ(T, G^•(K^•))`. -/
lemma hypercohomology_obj (n : ℤ) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) :
    (hypercohomology T n).obj K =
      ((godementSectionsDoubleComplex T K).total (ComplexShape.up ℤ)).homology n := rfl

/-- The cohomology `H^n(T, F) = ℍ^n(T, F[0])` of a sheaf of abelian groups, as a functor. -/
def sheafCohomology (n : ℤ) : TopCat.Sheaf AddCommGrpCat.{u} T ⥤ AddCommGrpCat.{u} :=
  HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙ hypercohomology T n

end Hypercohomology

section HypercohomologyPullback

variable {T T' : TopCat.{u}} (f : T' ⟶ T)

/-- The inverse image `f⁻¹ K` of a complex of sheaves of abelian groups. -/
abbrev complexPullback :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ ⥤
      CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T') ℤ :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).mapHomologicalComplex _

/-- The comparison `G^•(F) ⟶ f_* G^•(f⁻¹ F)` of Godement resolutions along `f : T' ⟶ T`: in
degree `0` it is `(s_x)_{x ∈ U} ↦ (s_{f y})_{y ∈ f⁻¹ U}`, read through the stalk maps
`F_{f y} ⟶ (f⁻¹ F)_y`, and it is induced inductively on the cokernels in higher degrees. -/
def godementResolutionPullback (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (godementResolution T).obj F ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj
        ((godementResolution T').obj ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F)) :=
  CokernelCoresolution.complexHom (godementPullbackLift f)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F)

/-- In degree `0`, the comparison `G^•(F) ⟶ f_* G^•(f⁻¹ F)` is the lift of the unit
`F ⟶ f_* f⁻¹ F`. -/
lemma godementResolutionPullback_f_zero (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (godementResolutionPullback f F).f 0 =
      godementLiftHom f
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F) :=
  rfl

/-- The comparison of Godement resolutions is natural in the sheaf. -/
@[reassoc]
lemma godementResolution_map_comp_godementResolutionPullback
    {F F' : TopCat.Sheaf AddCommGrpCat.{u} T} (a : F ⟶ F') :
    (godementResolution T).map a ≫ godementResolutionPullback f F' =
      godementResolutionPullback f F ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).map
          ((godementResolution T').map ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map a)) :=
  CokernelCoresolution.complexFunctor_map_comp_complexHom _ _ _ _ _
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.naturality a)

/-- The pullback `Γ(T, G^•(F)) ⟶ Γ(T', G^•(f⁻¹ F))` on global sections of Godement
resolutions. -/
def godementSectionsPullback (F : TopCat.Sheaf AddCommGrpCat.{u} T) :
    (godementSections T).obj F ⟶ (godementSections T').obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F) :=
  (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).map
    (((globalSections T).mapHomologicalComplex _).map (godementResolutionPullback f F))

/-- The pullback on global sections of Godement resolutions is natural in the sheaf. -/
@[reassoc]
lemma godementSections_map_comp_godementSectionsPullback
    {F F' : TopCat.Sheaf AddCommGrpCat.{u} T} (a : F ⟶ F') :
    (godementSections T).map a ≫ godementSectionsPullback f F' =
      godementSectionsPullback f F ≫
        (godementSections T').map ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map a) := by
  have h := congrArg (fun g => (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).map
    (((globalSections T).mapHomologicalComplex _).map g))
    (godementResolution_map_comp_godementResolutionPullback f a)
  simp only [Functor.map_comp] at h
  exact h

/-- The map of double complexes `Γ(T, G^•(K^•)) ⟶ Γ(T', G^•(f⁻¹ K^•))`. -/
def godementSectionsDoubleComplexPullback
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) :
    godementSectionsDoubleComplex T K ⟶
      godementSectionsDoubleComplex T' ((complexPullback f).obj K) where
  f q := godementSectionsPullback f (K.X q)
  comm' q q' _ := (godementSections_map_comp_godementSectionsPullback f (K.d q q')).symm

/-- The **pullback** `f^* : ℍ^n(T, K^•) ⟶ ℍ^n(T', f⁻¹ K^•)` along a continuous map
`f : T' ⟶ T`. -/
@[mmp "def_mmp_gaga_godement"]
def hypercohomologyPullback (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ) (n : ℤ) :
    (hypercohomology T n).obj K ⟶ (hypercohomology T' n).obj ((complexPullback f).obj K) :=
  HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f K)
      (ComplexShape.up ℤ)) n

/-- The pullback on hypercohomology is natural in the complex. -/
@[reassoc]
lemma hypercohomology_map_comp_hypercohomologyPullback
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} T) ℤ} (φ : K ⟶ L) (n : ℤ) :
    (hypercohomology T n).map φ ≫ hypercohomologyPullback f L n =
      hypercohomologyPullback f K n ≫ (hypercohomology T' n).map ((complexPullback f).map φ) := by
  have h : ((godementSections T).mapHomologicalComplex _).map φ ≫
      godementSectionsDoubleComplexPullback f L =
      godementSectionsDoubleComplexPullback f K ≫
        ((godementSections T').mapHomologicalComplex _).map ((complexPullback f).map φ) := by
    ext q : 1
    exact godementSections_map_comp_godementSectionsPullback f (φ.f q)
  change HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (((godementSections T).mapHomologicalComplex _).map φ) (ComplexShape.up ℤ)) n ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (godementSectionsDoubleComplexPullback f L) (ComplexShape.up ℤ)) n =
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (godementSectionsDoubleComplexPullback f K) (ComplexShape.up ℤ)) n ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (((godementSections T').mapHomologicalComplex _).map ((complexPullback f).map φ))
          (ComplexShape.up ℤ)) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp, h]

/-- The pullback `f^* : H^n(T, F) ⟶ H^n(T', f⁻¹ F)` on sheaf cohomology: the pullback of
hypercohomology, followed by the identification `f⁻¹ (F[0]) ≅ (f⁻¹ F)[0]`. -/
def sheafCohomologyPullback (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℤ) :
    (sheafCohomology T n).obj F ⟶
      (sheafCohomology T' n).obj ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F) :=
  hypercohomologyPullback f _ n ≫
    (hypercohomology T' n).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) (ComplexShape.up ℤ) 0).hom.app F)

end HypercohomologyPullback

end MMP.Analytic
