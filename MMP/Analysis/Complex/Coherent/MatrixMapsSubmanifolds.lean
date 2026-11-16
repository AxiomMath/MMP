module

public import MMP.Analysis.Complex.Coherent.CoherenceCalculus
public import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
public import MMP.Topology.Sheaves.GodementOpenEmbedding
public import StacksFrontier.Topology.Sheaves.Stalk.PullbackUnit

/-!
# The coherent analytic toolkit: matrices, closed submanifolds

Maps between free modules given by matrices and the augmentation of a resolution, holomorphic
coordinates of atlas charts, the ideal of a closed complex submanifold and its generation by
flattening coordinates, Godement resolutions along a closed embedding, the structure sheaf of a
submanifold and its local model, and the direct image and restriction of modules along a closed
submanifold.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter MMP.Analytic

namespace MMP.Analytic.CoherentAnalytic

open scoped Manifold ContDiff
open MMP.Analytic.OkaCoherence (overSection epi_of_locally_surjective
  freeHomEquiv_symm_app_freeSection kernel_ι_app_injective exists_kernel_ι_app_eq
  kernel_condition_app freeElt free_map_freeElt holEval contMDiff_holEval holEval_ext)

section MatrixMaps

open Limits

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M]

local notation "𝒜" => holSheaf n M

variable {W : Opens (TopCat.of M)}

/-- The unique map from an object of the slice over `W` to its terminal object. -/
abbrev toTop (Z : Over W) : Z ⟶ Over.mk (𝟙 W) := Over.homMk Z.hom (by simp)

/-- A section of a sheaf on the slice over `W`, from its value on the terminal object. -/
noncomputable def topSec (P : SheafOfModules.{0} ((𝒜).over W))
    (t : P.val.obj (op (Over.mk (𝟙 W)))) : P.sections :=
  PresheafOfModules.sectionsMk (fun Z => P.val.map (toTop Z.unop).op t) fun {Z Z'} f => by
    have h : (toTop Z.unop).op ≫ f = (toTop Z'.unop).op :=
      Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))
    rw [← PresheafOfModules.map_comp_apply, h]

/-- The component of `topSec P t` at `Z` is the restriction of `t` along `Z ⟶ W`. -/
theorem topSec_apply (P : SheafOfModules.{0} ((𝒜).over W))
    (t : P.val.obj (op (Over.mk (𝟙 W)))) (Z : Over W) :
    (topSec P t).1 (op Z) = P.val.map (toTop Z).op t := rfl

/-- A section of `𝒜` over `Z.left`, as a section of `𝒜|_W` over `Z`. -/
def toOverRing (Z : Over W) (a : (𝒜).obj.obj (op Z.left)) :
    ((𝒜).over W).obj.obj (op Z) := a

/-- A section of `𝒜|_W` over `Z`, as a section of `𝒜` over `Z.left`. -/
def fromOverRing (Z : Over W) (a : ((𝒜).over W).obj.obj (op Z)) :
    (𝒜).obj.obj (op Z.left) := a

/-- `fromOverRing` carries a sum of products with sections from `toOverRing` to the corresponding
sum of products. -/
theorem fromOverRing_sum_mul (Z : Over W) {p : ℕ} (a : Fin p → ((𝒜).over W).obj.obj (op Z))
    (b : Fin p → (𝒜).obj.obj (op Z.left)) :
    fromOverRing Z (∑ l, a l * toOverRing Z (b l)) = ∑ l, fromOverRing Z (a l) * b l := rfl

/-- The morphism of free modules on the slice over `W` given by a matrix of sections over `W`. -/
noncomputable def matMap {p q : ℕ} (P : Fin p → Fin q → (𝒜).obj.obj (op W)) :
    SheafOfModules.free (R := (𝒜).over W) (Fin p) ⟶ SheafOfModules.free (Fin q) :=
  (SheafOfModules.free (Fin q)).freeHomEquiv.symm fun l => topSec _
    (∑ m, toOverRing (Over.mk (𝟙 W)) (P l m) •
      freeElt (R := (𝒜).over W) m (op (Over.mk (𝟙 W))))

/-- On the free module over `Z`, `matMap P` sends `∑ l, a l • e l` to
`∑ m, (∑ l, a l * P l m) • e m`, with `P` restricted to `Z`. -/
theorem matMap_app {p q : ℕ} (P : Fin p → Fin q → (𝒜).obj.obj (op W)) (Z : Over W)
    (a : Fin p → ((𝒜).over W).obj.obj (op Z)) :
    (matMap P).val.app (op Z) (∑ l, a l • freeElt (R := (𝒜).over W) l (op Z)) =
      ∑ m, (∑ l, a l * toOverRing Z (resA Z.hom.le (P l m))) •
        freeElt (R := (𝒜).over W) m (op Z) := by
  rw [matMap, freeHomEquiv_symm_app_sum]
  have e : ∀ l, (topSec (SheafOfModules.free (R := (𝒜).over W) (Fin q))
      (∑ m, toOverRing (Over.mk (𝟙 W)) (P l m) •
        freeElt (R := (𝒜).over W) m (op (Over.mk (𝟙 W))))).1 (op Z) =
      ∑ m, toOverRing Z (resA Z.hom.le (P l m)) • freeElt (R := (𝒜).over W) m (op Z) := fun l =>
    (topSec_apply _ _ Z).trans (free_map_sum_smul (R := (𝒜).over W) _ _)
  refine (Finset.sum_congr rfl fun l _ => congrArg
    (fun v : (SheafOfModules.free (R := (𝒜).over W) (Fin q)).val.obj (op Z) => a l • v)
    (e l)).trans ?_
  exact sum_smul_sum_smul _ _ _

/-- If the matrix product `P * N` vanishes, then `matMap P ≫ matMap N = 0`. -/
theorem matMap_comp_eq_zero {p q t : ℕ} (P : Fin p → Fin q → (𝒜).obj.obj (op W))
    (N : Fin q → Fin t → (𝒜).obj.obj (op W)) (h : ∀ l u, ∑ m, P l m * N m u = 0) :
    matMap P ≫ matMap N = 0 := by
  ext Z v
  obtain ⟨a, ha⟩ := exists_eq_sum_smul_freeSection' (R := (𝒜).over W) Z v
  change (matMap N).val.app Z ((matMap P).val.app Z v) = 0
  rw [ha, matMap_app, matMap_app]
  refine Finset.sum_eq_zero fun u _ => ?_
  have e : ∑ m, (∑ l, a l * toOverRing Z.unop (resA Z.unop.hom.le (P l m))) *
      toOverRing Z.unop (resA Z.unop.hom.le (N m u)) = 0 := by
    simp only [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← Finset.mul_sum]
    have e2 : ∑ m, toOverRing Z.unop (resA Z.unop.hom.le (P l m)) *
        toOverRing Z.unop (resA Z.unop.hom.le (N m u)) =
        toOverRing Z.unop (resA Z.unop.hom.le (∑ m, P l m * N m u)) := by
      rw [resA_sum (A := 𝒜)]
      simp only [resA_mul (A := 𝒜)]
      rfl
    rw [e2, h l u]
    have : toOverRing Z.unop (resA (A := 𝒜) Z.unop.hom.le 0) = 0 := map_zero _
    rw [this, mul_zero]
  rw [e, zero_smul]

/-- **Exactness from generating relations.** If the rows of `P` generate the relations among
elements `g` of `Q`, and the sections of the free module killed by `φ` are relations among the
`g`, then `free ⟶(P) free ⟶(φ) T` is exact. -/
theorem exact_matMap_of_relGen {p q : ℕ} (Q : SheafOfModules.{0} 𝒜)
    (g : Fin q → Q.val.obj (op W)) (P : Fin p → Fin q → (𝒜).obj.obj (op W))
    (hP : RelGen Q g P) {T : SheafOfModules.{0} ((𝒜).over W)}
    (φ : SheafOfModules.free (R := (𝒜).over W) (Fin q) ⟶ T)
    (hφ : ∀ (X : Over W) (β : Fin q → ((𝒜).over W).obj.obj (op X)),
      φ.val.app (op X) (∑ m, β m • freeElt (R := (𝒜).over W) m (op X)) = 0 →
        ∑ m, fromOverRing X (β m) • resM Q X.hom.le (g m) = 0)
    (hz : matMap P ≫ φ = 0) :
    (ShortComplex.mk (matMap P) φ hz).Exact := by
  refine shortComplex_exact_of_locally _ fun X b hb => ?_
  obtain ⟨β, hβ⟩ := exists_eq_sum_smul_freeSection' (R := (𝒜).over W) (I := Fin q) (op X) b
  rw [hβ] at hb
  choose U' hU' hyU' c hc using hP.2 X.left X.hom.le _ (hφ X β hb)
  let T' : Sieve X :=
    { arrows := fun Y _ => ∃ y : X.left, Y.left ≤ U' y.1 y.2
      downward_closed := fun {Y Y'} _ ⟨y, hy⟩ g => ⟨y, g.left.le.trans hy⟩ }
  refine ⟨T', ?_, ?_⟩
  · rw [GrothendieckTopology.mem_over_iff]
    refine (Opens.mem_grothendieckTopology _).2 fun y hy => ?_
    refine ⟨U' y hy, homOfLE (hU' y hy), ?_, hyU' y hy⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨⟨y, hy⟩, le_rfl⟩
  · rintro Y f ⟨⟨y, hy⟩, hle⟩
    refine ⟨∑ l, toOverRing Y (resA hle (c y hy l)) • freeElt (R := (𝒜).over W) l (op Y), ?_⟩
    change (matMap P).val.app (op Y) _ = _
    rw [matMap_app, hβ]
    refine Eq.trans ?_ (free_map_sum_smul (R := (𝒜).over W) f.op β).symm
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    have key := congrArg (resA (A := 𝒜) hle) (hc y hy m)
    rw [resA_resA (A := 𝒜), resA_sum (A := 𝒜)] at key
    simp only [resA_mul (A := 𝒜), resA_resA (A := 𝒜)] at key
    exact key.symm

/-- Coefficients of relations among rows of a matrix. -/
theorem coeff_eq_zero_of_rowsF {V : Opens (TopCat.of M)} {p q t : ℕ}
    (P : Fin p → Fin q → (𝒜).obj.obj (op V)) (N : Fin q → Fin t → (𝒜).obj.obj (op V))
    (h : ∀ l, ∑ m, P l m • rowsF N m = 0) : ∀ l u, ∑ m, P l m * N m u = 0 := by
  intro l u
  have e := h l
  rw [sum_smul_rowsF] at e
  exact congrFun (free_sum_smul_injective (b := fun _ => 0) (e.trans (by simp))) u

/-- Sections killed by the matrix map of `N` are relations among the rows of `N`. -/
theorem matMap_app_eq_zero {q t : ℕ} (N : Fin q → Fin t → (𝒜).obj.obj (op W))
    (X : Over W) (β : Fin q → ((𝒜).over W).obj.obj (op X))
    (h : (matMap N).val.app (op X) (∑ m, β m • freeElt (R := (𝒜).over W) m (op X)) = 0) :
    ∑ m, fromOverRing X (β m) •
      resM (SheafOfModules.free (R := 𝒜) (Fin t)) X.hom.le (rowsF N m) = 0 := by
  rw [matMap_app] at h
  have h0 := free_sum_smul_injective (b := fun _ => 0) (h.trans (by simp))
  have e : ∀ m, resM (SheafOfModules.free (R := 𝒜) (Fin t)) X.hom.le (rowsF N m) =
      rowsF (fun m u => resA X.hom.le (N m u)) m := fun m => resM_rowsF _ N m
  simp only [e]
  rw [sum_smul_rowsF]
  refine Finset.sum_eq_zero fun u _ => ?_
  have := congrArg (fromOverRing X) (congrFun h0 u)
  rw [fromOverRing_sum_mul] at this
  rw [this]
  exact zero_smul _ _

/-- The augmentation `𝒜ʳ|_W ⟶ S|_W` given by elements `s` of `S` over `W`. -/
noncomputable abbrev augMap (S : SheafOfModules.{0} 𝒜) {r : ℕ}
    (s : Fin r → S.val.obj (op W)) :
    SheafOfModules.free (R := (𝒜).over W) (Fin r) ⟶ S.over W :=
  (S.over W).freeHomEquiv.symm fun k => overSection S (s k)

/-- On the free module over `X`, `augMap S s` sends `∑ m, β m • e m` to `∑ m, β m • s m`, with `s`
restricted to `X`. -/
theorem augMap_app (S : SheafOfModules.{0} 𝒜) {r : ℕ} (s : Fin r → S.val.obj (op W))
    (X : Over W) (β : Fin r → ((𝒜).over W).obj.obj (op X)) :
    (augMap S s).val.app (op X) (∑ m, β m • freeElt (R := (𝒜).over W) m (op X)) =
      ∑ m, fromOverRing X (β m) • resM S X.hom.le (s m) :=
  freeHomEquiv_symm_app_sum _ _ _

/-- If the rows of `P` are relations among the sections `s`, then `matMap P ≫ augMap S s = 0`. -/
theorem matMap_comp_augMap_eq_zero (S : SheafOfModules.{0} 𝒜) {p r : ℕ}
    (s : Fin r → S.val.obj (op W)) (P : Fin p → Fin r → (𝒜).obj.obj (op W))
    (h : ∀ l, ∑ k, P l k • s k = 0) : matMap P ≫ augMap S s = 0 := by
  ext Z v
  obtain ⟨a, ha⟩ := exists_eq_sum_smul_freeSection' (R := (𝒜).over W) Z v
  change (augMap S s).val.app Z ((matMap P).val.app Z v) = 0
  rw [ha, matMap_app, augMap_app]
  calc _ = ∑ m, ∑ l, fromOverRing Z.unop (a l) •
          (resA Z.unop.hom.le (P l m) • resM S Z.unop.hom.le (s m)) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [fromOverRing_sum_mul, Finset.sum_smul]
        exact Finset.sum_congr rfl fun l _ => mul_smul _ _ _
    _ = ∑ l, fromOverRing Z.unop (a l) •
          ∑ m, resA Z.unop.hom.le (P l m) • resM S Z.unop.hom.le (s m) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.smul_sum ..).symm
    _ = 0 := by
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [← resM_sum_smul, h l, resM_zero, smul_zero]

/-- The free module of rank `0` is zero. -/
theorem isZero_free_of_eq {m : ℕ} (hm : m = 0) :
    IsZero (SheafOfModules.free (R := (𝒜).over W) (Fin m)) := by
  subst hm
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.free (R := (𝒜).over W) (Fin 0)).freeHomEquiv.injective
  funext i
  exact i.elim0

/-- A short complex is exact if it has the same maps as an exact short complex. -/
theorem shortComplex_exact_of_eq {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {S : ShortComplex C} {f' : S.X₁ ⟶ S.X₂} {g' : S.X₂ ⟶ S.X₃} (hf : S.f = f') (hg : S.g = g')
    (hz : f' ≫ g' = 0) (h : (ShortComplex.mk f' g' hz).Exact) : S.Exact := by
  cases S
  cases hf
  cases hg
  exact h

/-- The ranks `r, ρ 0, ρ 1, …` of a resolution. -/
def resRank (r : ℕ) (ρ : ℕ → ℕ) : ℕ → ℕ
  | 0 => r
  | i + 1 => ρ i

/-- The matrices `D0, D 0, D 1, …` of a resolution. -/
def resMat {r : ℕ} {ρ : ℕ → ℕ} (D0 : Fin (ρ 0) → Fin r → (𝒜).obj.obj (op W))
    (D : ∀ i, Fin (ρ (i + 1)) → Fin (ρ i) → (𝒜).obj.obj (op W)) :
    ∀ i, Fin (resRank r ρ (i + 1)) → Fin (resRank r ρ i) → (𝒜).obj.obj (op W)
  | 0 => D0
  | i + 1 => D i

/-- **The free resolution near a point**, assembled from generators and a resolution of their
relations. -/
theorem exists_complex_of_relResolution (S : SheafOfModules.{0} 𝒜) {r : ℕ}
    (s : Fin r → S.val.obj (op W)) (hs : LocallyGenerates S s) {k : ℕ} {ρ : ℕ → ℕ}
    {D0 : Fin (ρ 0) → Fin r → (𝒜).obj.obj (op W)}
    {D : ∀ i, Fin (ρ (i + 1)) → Fin (ρ i) → (𝒜).obj.obj (op W)}
    (hres : IsRelResolution S s k ρ D0 D) :
    ∃ (C : ChainComplex (SheafOfModules.{0} ((𝒜).over W)) ℕ) (ε : C.X 0 ⟶ S.over W),
      (∀ i, ∃ r : ℕ, Nonempty (C.X i ≅ SheafOfModules.free (Fin r))) ∧
      (∀ i, ρ i = 0 → IsZero (C.X (i + 1))) ∧ (∀ i, 0 < i → C.ExactAt i) ∧ Epi ε ∧
      ∃ h : C.d 1 0 ≫ ε = 0, (ShortComplex.mk _ _ h).Exact := by
  have hrel : ∀ i, RelGen (SheafOfModules.free (R := 𝒜) (Fin (resRank r ρ i)))
      (rowsF (resMat D0 D i)) (resMat D0 D (i + 1)) := fun i => by
    cases i with
    | zero => exact hres.2.1
    | succ i => exact hres.2.2.1 i
  have sq : ∀ i, matMap (resMat D0 D (i + 1)) ≫ matMap (resMat D0 D i) = 0 := fun i =>
    matMap_comp_eq_zero _ _ (coeff_eq_zero_of_rowsF _ _ (hrel i).1)
  let X : ℕ → SheafOfModules.{0} ((𝒜).over W) := fun i =>
    SheafOfModules.free (R := (𝒜).over W) (Fin (resRank r ρ i))
  let d : ∀ i, X (i + 1) ⟶ X i := fun i => matMap (resMat D0 D i)
  let C : ChainComplex (SheafOfModules.{0} ((𝒜).over W)) ℕ := ChainComplex.of X d sq
  have hz0 : matMap D0 ≫ augMap S s = 0 := matMap_comp_augMap_eq_zero S s D0 hres.1.1
  let ε : C.X 0 ⟶ S.over W := augMap S s
  refine ⟨C, ε, fun i => ⟨resRank r ρ i, ⟨Iso.refl _⟩⟩, fun i hi => ?_, fun i hi => ?_,
    epi_freeHomEquiv_symm_overSection S s hs, ?_, ?_⟩
  · exact isZero_free_of_eq hi
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [HomologicalComplex.exactAt_iff' C (j + 2) (j + 1) j (by simp) (by simp)]
    exact shortComplex_exact_of_eq (ChainComplex.of_d X d (j + 1)) (ChainComplex.of_d X d j)
      (sq j) (exact_matMap_of_relGen _ (rowsF (resMat D0 D j)) (resMat D0 D (j + 1)) (hrel j)
        (matMap (resMat D0 D j)) (matMap_app_eq_zero (resMat D0 D j)) (sq j))
  · have e : C.d 1 0 = d 0 := ChainComplex.of_d X d 0
    rw [e]
    exact hz0
  · exact shortComplex_exact_of_eq (ChainComplex.of_d X d 0) rfl hz0
      (exact_matMap_of_relGen S s D0 hres.1 (augMap S s)
        (fun X β h => (augMap_app S s X β).symm.trans h) hz0)

end MatrixMaps

section PartThree

open Limits Topology IsLocalRing

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M]

local notation "𝒜" => holSheaf n M
local notation "𝒪₀" => holGerms (0 : Fin n → ℂ)

attribute [local instance] instRegular

/-- Sections that locally generate `Q` still locally generate it after restriction to a smaller
open set. -/
theorem LocallyGenerates.restrict {Q : SheafOfModules.{0} 𝒜} {W W' : Opens (TopCat.of M)}
    (h : W' ≤ W) {m : ℕ} {g : Fin m → Q.val.obj (op W)} (hg : LocallyGenerates Q g) :
    LocallyGenerates Q (fun k => resM Q h (g k)) := by
  intro Z z t
  obtain ⟨S, hS, hc⟩ := hg Z (z ≫ homOfLE h) t
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨c, hc⟩ := hc V f hf
  refine ⟨c, hc.trans (Finset.sum_congr rfl fun k _ => ?_)⟩
  congr 1
  simp only [resM]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  rfl

/-- **Basis replacement.** If the germs at `x` of a module locally generated by `g` form a free
module, lifts of a basis are free generators near `x`. -/
theorem exists_free_generators (x : M) (Q : SheafOfModules.{0} 𝒜) (hQ : RelFin Q)
    {W : Opens (TopCat.of M)} (hxW : x ∈ W) {r : ℕ} (g : Fin r → Q.val.obj (op W))
    (hg : LocallyGenerates Q g)
    (hpd : HasProjectiveDimensionLE (ModuleCat.of 𝒪₀ ((Fin r → 𝒪₀) ⧸ krel Q hxW g)) 0) :
    ∃ (W' : Opens (TopCat.of M)) (_ : W' ≤ W) (_ : x ∈ W') (m : ℕ) (t : Fin m → Q.val.obj (op W')),
      LocallyGenerates Q t ∧
        RelGen Q t (fun l => Fin.elim0 l : Fin 0 → Fin m → (𝒜).obj.obj (op W')) := by
  classical
  set K := krel Q hxW g
  have hproj : Module.Projective 𝒪₀ ((Fin r → 𝒪₀) ⧸ K) :=
    (IsProjective.iff_projective _).2 ((projective_iff_hasProjectiveDimensionLE_zero _).2 hpd)
  have hfree : Module.Free 𝒪₀ ((Fin r → 𝒪₀) ⧸ K) := Module.free_of_flat_of_isLocalRing
  let nB := Module.finBasis 𝒪₀ ((Fin r → 𝒪₀) ⧸ K)
  set m := Module.finrank 𝒪₀ ((Fin r → 𝒪₀) ⧸ K)
  choose ub hub using fun j => Submodule.mkQ_surjective K (nB j)
  obtain ⟨U1, hx1, u, hu⟩ := exists_germHom_eq_fun (n := n) x (fun p : Fin m × Fin r => ub p.1 p.2)
  let W1 := U1 ⊓ W
  have hx1' : x ∈ W1 := ⟨hx1, hxW⟩
  let t1 : Fin m → Q.val.obj (op W1) := fun j =>
    ∑ k, resA (inf_le_left : W1 ≤ U1) (u (j, k)) • resM Q (inf_le_right : W1 ≤ W) (g k)
  let cc : Fin r × Fin m → 𝒪₀ := fun p => nB.repr (K.mkQ (Pi.single p.1 1)) p.2
  have hmemK : ∀ k, (Pi.single k 1 - ∑ j, cc (k, j) • ub j) ∈ K := by
    intro k
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hub]
    rw [sub_eq_zero]
    exact (nB.sum_repr _).symm
  choose U2 hU2 hx2 a ha hrel using hmemK
  obtain ⟨U3, hx3, c, hc⟩ := exists_germHom_eq_fun (n := n) x cc
  obtain ⟨U4', hx4', hU4'⟩ := exists_le_of_forall_mem U2 hx2
  let W4 := (U4' ⊓ U3) ⊓ W1
  have hx4 : x ∈ W4 := ⟨⟨hx4', hx3⟩, hx1'⟩
  have h4U2 : ∀ k, W4 ≤ U2 k := fun k => (inf_le_left.trans inf_le_left).trans (hU4' k)
  have h4U3 : W4 ≤ U3 := inf_le_left.trans inf_le_right
  have h41 : W4 ≤ W1 := inf_le_right
  let φ : Fin r × Fin r → (𝒜).obj.obj (op W4) := fun p =>
    resA (h4U2 p.1) (a p.1 p.2) - ((if p.1 = p.2 then 1 else 0) -
      ∑ j, resA h4U3 (c (p.1, j)) * resA (h41.trans inf_le_left) (u (j, p.2)))
  have hφ : ∀ p, germHom x hx4 (φ p) = 0 := by
    rintro ⟨k, k'⟩
    simp only [φ, map_sub, map_sum, map_mul]
    rw [germHom_resA x (h4U2 k) hx4 (a k k'), ha k k', sub_eq_zero]
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    · by_cases hkk : k = k'
      · subst hkk; simp
      · rw [Pi.single_eq_of_ne' hkk, if_neg hkk, map_zero]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [germHom_resA x h4U3 hx4 (c (k, j)),
        germHom_resA x (h41.trans inf_le_left) hx4 (u (j, k')), hc (k, j), hu (j, k')]
  obtain ⟨W5, h54, hx5, hφ0⟩ := exists_resA_eq_zero_fun (n := n) x hx4 φ hφ
  have h51 : W5 ≤ W1 := h54.trans h41
  have h5W : W5 ≤ W := h51.trans inf_le_right
  let G : Fin r → Q.val.obj (op W5) := fun k => resM Q h5W (g k)
  let Uu : Fin m → Fin r → (𝒜).obj.obj (op W5) := fun j k => resA (h51.trans inf_le_left) (u (j, k))
  let Cc : Fin r → Fin m → (𝒜).obj.obj (op W5) := fun k j => resA (h54.trans h4U3) (c (k, j))
  let t5 : Fin m → Q.val.obj (op W5) := fun j => resM Q h51 (t1 j)
  have ht5 : ∀ j, t5 j = ∑ k, Uu j k • G k := by
    intro j
    change resM Q h51 (∑ k, resA (inf_le_left : W1 ≤ U1) (u (j, k)) •
      resM Q (inf_le_right : W1 ≤ W) (g k)) = _
    rw [resM_sum_smul Q h51]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [resA_resA (A := 𝒜), resM_resM]
  have hkey : ∀ k, G k = ∑ j, Cc k j • t5 j := by
    intro k
    have e := congrArg (resM Q (h54.trans (h4U2 k))) (hrel k)
    rw [resM_sum_smul, resM_zero] at e
    simp only [resM_resM] at e
    have ea : ∀ k', resA (h54.trans (h4U2 k)) (a k k') =
        (if k = k' then 1 else 0) - ∑ j, Cc k j * Uu j k' := by
      intro k'
      have e2 := hφ0 (k, k')
      simp only [φ, resA_sub (A := 𝒜), resA_resA (A := 𝒜), sub_eq_zero] at e2
      rw [e2]
      simp only [resA_sub (A := 𝒜), resA_sum (A := 𝒜), resA_mul (A := 𝒜), resA_resA (A := 𝒜)]
      congr 1
      split_ifs <;> simp [resA]
    simp only [ea, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at e
    rw [sub_eq_zero] at e
    refine e.trans ?_
    simp only [ht5, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  obtain ⟨W6, h65, hx6, tt, F, hF⟩ := exists_relGen hQ hx5 t5
  have hFgerm : ∀ l j, germHom x hx6 (F l j) = 0 := by
    intro l
    let α : Fin r → (𝒜).obj.obj (op W6) := fun k => ∑ j, F l j * resA h65 (Uu j k)
    have hα : ∑ k, α k • resM Q (h65.trans h5W) (g k) = 0 := by
      have e := hF.1 l
      have e2 : ∀ j, resM Q h65 (t5 j) =
          ∑ k, resA h65 (Uu j k) • resM Q (h65.trans h5W) (g k) := fun j => by
        rw [ht5 j, resM_sum_smul Q h65]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [resM_resM]
      rw [← e]
      simp only [e2, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [α, Finset.sum_smul]
    have hmem : (fun k => germHom x hx6 (α k)) ∈ K :=
      ⟨W6, h65.trans h5W, hx6, α, fun k => rfl, hα⟩
    have h0 : K.mkQ (fun k => germHom x hx6 (α k)) = 0 :=
      (Submodule.Quotient.mk_eq_zero K).2 hmem
    have hsum : (fun k => germHom x hx6 (α k)) = ∑ j, germHom x hx6 (F l j) • ub j := by
      funext k
      simp only [α, map_sum, map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [germHom_resA x h65 hx6 (Uu j k), germHom_resA x (h51.trans inf_le_left) hx5 (u (j, k)),
        hu (j, k)]
    rw [hsum, map_sum] at h0
    simp only [map_smul, hub] at h0
    exact Fintype.linearIndependent_iff.1 nB.linearIndependent _ h0
  obtain ⟨W7, h76, hx7, hF0⟩ := exists_resA_eq_zero_fun (n := n) x hx6
    (fun p : Fin tt × Fin m => F p.1 p.2) fun p => hFgerm p.1 p.2
  have h75 : W7 ≤ W5 := h76.trans h65
  refine ⟨W7, h75.trans h5W, hx7, m, fun j => resM Q h75 (t5 j), ?_, fun l => Fin.elim0 l, ?_⟩
  · -- the new generators generate
    refine locallyGenerates_of_nhds _ fun U hU t y hy => ?_
    obtain ⟨U', hU', hy', d, hd⟩ := hg.exists_nhds (hU.trans (h75.trans h5W)) t hy
    refine ⟨U', hU', hy', fun j => ∑ k, d k * resA (hU'.trans (hU.trans h75)) (Cc k j), ?_⟩
    rw [hd]
    have e : ∀ k, resM Q (hU'.trans (hU.trans (h75.trans h5W))) (g k) =
        ∑ j, resA (hU'.trans (hU.trans h75)) (Cc k j) •
          resM Q (hU'.trans hU) (resM Q h75 (t5 j)) := by
      intro k
      have e1 := congrArg (resM Q (hU'.trans (hU.trans h75))) (hkey k)
      simp only [G, resM_resM] at e1
      rw [e1, resM_sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show t5 j = resM Q h51 (t1 j) from rfl, resM_resM, resM_resM, resM_resM]
    simp only [e, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  · -- the new generators are independent
    intro U hU a ha y hy
    have ha' : ∑ j, a j • resM Q (hU.trans h76) (resM Q h65 (t5 j)) = 0 := by
      simpa only [resM_resM] using ha
    obtain ⟨U', h', hy', d, hd⟩ := hF.2 U (hU.trans h76) a ha' y hy
    refine ⟨U', h', hy', Fin.elim0, fun j => ?_⟩
    rw [hd j]
    refine (Finset.sum_eq_zero fun l _ => ?_).trans (Fintype.sum_empty _).symm
    have e4 : resA (A := 𝒜) (h'.trans (hU.trans h76)) (F l j) =
        resA (A := 𝒜) (h'.trans hU) (resA h76 (F l j)) := by rw [resA_resA (A := 𝒜)]
    rw [e4]
    have e3 := hF0 (l, j)
    simp only at e3
    rw [e3]; simp [resA]

end PartThree

section AtlasCharts

open Topology

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M]

/-- A holomorphic function on `U ⊆ M`, read in a chart `φ` of the maximal atlas, is complex
differentiable on the image of `U ∩` the chart source. -/
theorem differentiableOn_comp_symm_of_mem_maximalAtlas
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℂ (Fin n))}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M) (U : Opens M)
    (g : U → ℂ) (hg : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ g) :
    DifferentiableOn ℂ (fun w => Function.extend (Subtype.val : U → M) g 0 (φ.symm w))
      (φ.target ∩ φ.symm ⁻¹' U) := by
  set g' : M → ℂ := Function.extend (Subtype.val : U → M) g 0
  have hg' : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ g' U := by
    intro m hm
    have : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (fun w : U => g' w) ⟨m, hm⟩ := by
      have h1 : (fun w : U => g' w) = g := funext fun w => Subtype.val_injective.extend_apply g 0 w
      rw [h1]; exact hg _
    exact (contMDiffAt_subtype_iff.1 this).contMDiffWithinAt
  have h2 : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (g' ∘ φ.symm)
      (φ.target ∩ φ.symm ⁻¹' U) :=
    hg'.comp ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono Set.inter_subset_left)
      (fun z hz => hz.2)
  exact (contMDiffOn_iff_contDiffOn.1 h2).differentiableOn (by simp)

/-- A complex differentiable function near the image of `U ⊆` the source of a chart `φ` of the
maximal atlas, composed with `φ`, is holomorphic on `U`. -/
theorem contMDiff_comp_of_mem_maximalAtlas
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℂ (Fin n))}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M) (U : Opens M)
    (hU : (U : Set M) ⊆ φ.source) {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsOpen S)
    (G : EuclideanSpace ℂ (Fin n) → ℂ) (hG : DifferentiableOn ℂ G S)
    (hmaps : ∀ w ∈ U, φ w ∈ S) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (fun w : U => G (φ w)) := by
  have hGa := analyticOnNhd_of_differentiableOn hS hG
  have hG' : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ G S :=
    contMDiffOn_iff_contDiffOn.2 (hGa.contDiffOn hS.uniqueDiffOn)
  have h2 : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (G ∘ φ) U :=
    hG'.comp ((contMDiffOn_of_mem_maximalAtlas hφ).mono hU) (fun m hm => hmaps m hm)
  intro w
  exact contMDiffAt_subtype_iff.2 (h2.contMDiffAt (U.isOpen.mem_nhds w.2))

/-- **Hadamard division along a flattened submanifold.** In a chart `φ` flattening `Z`, a
holomorphic function vanishing on `Z` is, near a point of `Z`, a holomorphic combination of the
coordinates `φᵢ`, `i ≥ k`. -/
theorem exists_eq_sum_coord_of_mem {Z : Set M}
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℂ (Fin n))}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M) {k : ℕ}
    (hflat : φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0})
    {U : Opens M} (hU : (U : Set M) ⊆ φ.source) (h : U → ℂ)
    (hh : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ h)
    (hvan : ∀ q : U, (q : M) ∈ Z → h q = 0) {y : M} (hy : y ∈ U)
    (hyL : ∀ i : Fin n, k ≤ (i : ℕ) → φ y i = 0) :
    ∃ (U' : Opens M) (hU' : U' ≤ U), y ∈ U' ∧ ∃ c : {i : Fin n // k ≤ (i : ℕ)} → U' → ℂ,
      (∀ i, ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (c i)) ∧
      ∀ q : U', h ⟨q, hU' q.2⟩ = ∑ i, c i q * φ q i := by
  classical
  set E := EuclideanSpace ℂ (Fin n)
  set eq := EuclideanSpace.equiv (Fin n) ℂ
  set b := φ y
  have hyS : y ∈ φ.source := hU hy
  have hbT : b ∈ φ.target := φ.map_source hyS
  let h' : E → ℂ := fun w => Function.extend (Subtype.val : U → M) h 0 (φ.symm w)
  have hS0 : IsOpen (φ.target ∩ φ.symm ⁻¹' U) := φ.isOpen_inter_preimage_symm U.isOpen
  have hbS0 : b ∈ φ.target ∩ φ.symm ⁻¹' U := ⟨hbT, by simp [b, φ.left_inv hyS, hy]⟩
  have hd := differentiableOn_comp_symm_of_mem_maximalAtlas hφ U h hh
  let G : E → Fin n → ℂ := fun w i => if k ≤ (i : ℕ) then 0 else w i
  let P : E → E := fun w => eq.symm (G w)
  have hGc : Continuous G := continuous_pi fun i => by
    by_cases hi : k ≤ (i : ℕ)
    · simp only [G, if_pos hi]; exact continuous_const
    · simp only [G, if_neg hi]; exact (EuclideanSpace.proj i).continuous
  have hPc : Continuous P := eq.symm.continuous.comp hGc
  have hPb : P b = b := by
    apply eq.injective
    simp only [P, ContinuousLinearEquiv.apply_symm_apply]
    funext i
    simp only [G]
    split_ifs with hi
    · exact (hyL i hi).symm
    · rfl
  have hPv : ∀ᶠ w in 𝓝 b, h' (P w) = 0 := by
    have hmem : ∀ᶠ w in 𝓝 b, P w ∈ φ.target ∩ φ.symm ⁻¹' U :=
      hPc.continuousAt.preimage_mem_nhds (by rw [hPb]; exact hS0.mem_nhds hbS0)
    filter_upwards [hmem] with w hw
    have hL : P w ∈ φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0} := by
      refine ⟨hw.1, fun i hi => ?_⟩
      change G w i = 0
      simp [G, hi]
    rw [← hflat] at hL
    obtain ⟨z, ⟨hzZ, hzS⟩, hz⟩ := hL
    have hz' : φ.symm (P w) = z := by rw [← hz, φ.left_inv hzS]
    simp only [h', hz']
    have hzU : z ∈ U := by rw [← hz']; exact hw.2
    rw [Subtype.val_injective.extend_apply h 0 ⟨z, hzU⟩]
    exact hvan ⟨z, hzU⟩ hzZ
  let hH : (Fin n → ℂ) → ℂ := fun v => h' (eq.symm v)
  have hHd : ∀ᶠ v in 𝓝 (eq b), DifferentiableAt ℂ hH v := by
    have : ∀ᶠ v in 𝓝 (eq b), eq.symm v ∈ φ.target ∩ φ.symm ⁻¹' U :=
      eq.symm.continuous.continuousAt.preimage_mem_nhds (by
        rw [ContinuousLinearEquiv.symm_apply_apply]; exact hS0.mem_nhds hbS0)
    filter_upwards [this] with v hv
    exact (hd.differentiableAt (hS0.mem_nhds hv)).comp v eq.symm.differentiableAt
  let F : E → Fin n → ℂ := fun w => eq w
  let gen : {i : Fin n // k ≤ (i : ℕ)} → holGerms b := fun i =>
    ⟨((fun w : E => w i.1 : E → ℂ) : Germ (𝓝 b) ℂ), coe_mem_holGerms
      (Eventually.of_forall fun w => (EuclideanSpace.proj (𝕜 := ℂ) i.1).differentiableAt)⟩
  let I : Ideal (holGerms b) := Ideal.span (Set.range gen)
  obtain ⟨-, hcomp⟩ := exists_sub_eq_sum_sub_mul_and_comp_sub_comp_mem (E := E) hHd
  have hFG : G b = eq b := by
    funext i
    simp only [G]
    split_ifs with hi
    · exact (hyL i hi).symm
    · rfl
  obtain ⟨g, hgI, hg⟩ := hcomp b F G (Eventually.of_forall fun w => eq.differentiableAt)
    (Eventually.of_forall fun w => (differentiable_pi.2 fun i => by
      by_cases hi : k ≤ (i : ℕ)
      · simp only [G, if_pos hi]; exact differentiable_const _
      · simp only [G, if_neg hi]; exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable) w)
    rfl hFG I (fun i => by
      by_cases hi : k ≤ (i : ℕ)
      · refine ⟨gen ⟨i, hi⟩, Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩, ?_⟩
        refine Germ.coe_eq.2 (Eventually.of_forall fun w => ?_)
        simp [F, G, hi, eq]
      · refine ⟨0, I.zero_mem, ?_⟩
        change ((fun _ => (0 : ℂ) : E → ℂ) : Germ (𝓝 b) ℂ) = _
        refine Germ.coe_eq.2 (Eventually.of_forall fun w => ?_)
        simp [F, G, hi, eq])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (holGerms b)).1 hgI
  choose cf hcf hcd using fun i => (c i).2
  have hgerm : ((h' : E → ℂ) : Germ (𝓝 b) ℂ) =
      ((fun w => ∑ i, cf i w * w i.1 : E → ℂ) : Germ (𝓝 b) ℂ) := by
    have e1 : ((h' : E → ℂ) : Germ (𝓝 b) ℂ) =
        ((fun x => hH (F x) - hH (G x) : E → ℂ) : Germ (𝓝 b) ℂ) := by
      refine Germ.coe_eq.2 ?_
      filter_upwards [hPv] with w hw
      change h' w = h' (eq.symm (eq w)) - h' (P w)
      rw [hw, sub_zero, ContinuousLinearEquiv.symm_apply_apply]
    rw [e1, ← hg, ← hc]
    change (holGerms b).subtype (∑ i, c i • gen i) = _
    rw [map_sum]
    change ∑ i, ((c i : Germ (𝓝 b) ℂ) * (gen i : Germ (𝓝 b) ℂ)) = _
    simp only [← hcf]
    change ∑ i, Germ.coeRingHom _ (cf i) * Germ.coeRingHom _ (fun w : E => w i.1) =
      Germ.coeRingHom _ _
    simp only [← map_mul, ← map_sum]
    congr 1
    funext w
    simp [Finset.sum_apply]
  have hall : ∀ᶠ w in 𝓝 b, h' w = (∑ i, cf i w * w i.1) ∧ (∀ i, DifferentiableAt ℂ (cf i) w) :=
    (Germ.coe_eq.1 hgerm).and (Filter.eventually_all.2 hcd)
  obtain ⟨T0, hT0, hT0o, hbT0⟩ := eventually_nhds_iff.1 hall
  let U' : Opens M := ⟨(φ.source ∩ φ ⁻¹' T0) ∩ U,
    (φ.continuousOn.isOpen_inter_preimage φ.open_source hT0o).inter U.isOpen⟩
  have hU'U : U' ≤ U := fun q hq => hq.2
  refine ⟨U', hU'U, ⟨⟨hyS, hbT0⟩, hy⟩, fun i q => cf i (φ q), fun i => ?_, fun q => ?_⟩
  · exact contMDiff_comp_of_mem_maximalAtlas hφ U' (fun q hq => hq.1.1) hT0o (cf i)
      (fun w hw => ((hT0 w hw).2 i).differentiableWithinAt) (fun q hq => hq.1.2)
  · have e := (hT0 _ q.2.1.2).1
    simp only [h', φ.left_inv q.2.1.1] at e
    rw [Subtype.val_injective.extend_apply h 0 ⟨q.1, hU'U q.2⟩] at e
    exact e

end AtlasCharts

section SubmanifoldIdeal

open Limits Topology

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M]

local notation "𝒜" => holSheaf n M

variable {φ : OpenPartialHomeomorph M (EuclideanSpace ℂ (Fin n))}

/-- The source of a chart, as an open set. -/
abbrev chartSrc (φ : OpenPartialHomeomorph M (EuclideanSpace ℂ (Fin n))) :
    Opens (TopCat.of M) := ⟨φ.source, φ.open_source⟩

/-- The `i`-th coordinate of a chart of the maximal atlas, a holomorphic function on its
source. -/
noncomputable def chartCoord
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M) (i : Fin n) :
    (𝒜).obj.obj (op (chartSrc φ)) :=
  (⟨fun q : chartSrc φ => φ q i, by
    have h1 : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (fun q => φ q i) φ.source :=
      (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff.comp_contMDiffOn
        (contMDiffOn_of_mem_maximalAtlas hφ)
    intro w
    exact contMDiffAt_subtype_iff.2 (h1.contMDiffAt (φ.open_source.mem_nhds w.2))⟩ :
    C^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin n)), chartSrc φ; 𝓘(ℂ), ℂ⟯)

/-- **The vanishing ideal is generated by the coordinates `φᵢ`, `i ≥ k`, near every point.** -/
theorem exists_coord_gen
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M) {Z : Set M} {k : ℕ}
    (hflat : φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0})
    {U : Opens (TopCat.of M)} (hU : U ≤ chartSrc φ) (f : (𝒜).obj.obj (op U))
    (hf : ∀ q : U, (q : M) ∈ Z → holEval n U q f = 0) {y : M} (hy : y ∈ U) :
    ∃ (U' : Opens (TopCat.of M)) (h : U' ≤ U), y ∈ U' ∧
      ∃ c : {i : Fin n // k ≤ (i : ℕ)} → (𝒜).obj.obj (op U'),
        resA h f = ∑ i, c i * resA (h.trans hU) (chartCoord hφ i.1) := by
  classical
  by_cases hL : ∀ i : Fin n, k ≤ (i : ℕ) → φ y i = 0
  · obtain ⟨U', hU', hyU', c, hc, heq⟩ := exists_eq_sum_coord_of_mem hφ hflat (U := U) hU
      (fun q => holEval n U q f) (contMDiff_holEval U f) hf hy hL
    refine ⟨U', hU', hyU', fun i => (⟨c i, hc i⟩ :
      C^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin n)), U'; 𝓘(ℂ), ℂ⟯), holEval_ext fun q => ?_⟩
    rw [holEval_resA, map_sum]
    refine (heq q).trans (Finset.sum_congr rfl fun i _ => ?_)
    rfl
  · push Not at hL
    obtain ⟨i₀, hki₀, hi₀⟩ := hL
    let u : (𝒜).obj.obj (op U) := resA hU (chartCoord hφ i₀)
    let U' := nonvanishing (n := n) u
    have hU'U : U' ≤ U := nonvanishing_le u
    have hyU' : y ∈ U' := mem_nonvanishing u ⟨y, hy⟩ hi₀
    let v : (𝒜).obj.obj (op U') := resA hU'U u
    have hv : IsUnit v := isUnit_of_holEval_ne_zero v fun w => by
      rw [holEval_resA]; exact holEval_ne_zero_of_mem_nonvanishing u w
    refine ⟨U', hU'U, hyU', fun i => if i.1 = i₀ then resA hU'U f * ↑hv.unit⁻¹ else 0, ?_⟩
    beta_reduce
    rw [Finset.sum_eq_single ⟨i₀, hki₀⟩ (fun b _ hb => by
      rw [if_neg (fun h => hb (Subtype.ext h)), zero_mul]) (by simp)]
    rw [if_pos rfl]
    have : resA (hU'U.trans hU) (chartCoord hφ i₀) = v := by
      simp only [v, u]; rw [resA_resA (A := 𝒜)]
    rw [this, mul_assoc, show (↑hv.unit⁻¹ : (𝒜).obj.obj (op U')) * v = 1 from hv.val_inv_mul,
      mul_one]

end SubmanifoldIdeal

noncomputable section ClosedEmbeddingSheaves

open Limits TopCat TopCat.Presheaf

section Godement

variable {T T' : TopCat.{0}}

/-- A terminal abelian group is trivial. -/
theorem subsingleton_of_isTerminal {X : AddCommGrpCat.{0}} (h : IsTerminal X) : Subsingleton X :=
  AddCommGrpCat.subsingleton_of_isZero h.isZero

/-- A presheaf whose sections over the opens inside `O` are trivial has trivial stalks on `O`. -/
theorem subsingleton_stalk_of_forall_le {C : Type 1} [Category.{0} C] [HasColimits C]
    {FC : C → C → Type} {CC : C → Type} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [PreservesFilteredColimits (forget C)] {F : TopCat.Presheaf C T}
    (O : Opens T) (hF : ∀ W : Opens T, W ≤ O → Subsingleton (ToType (F.obj (op W)))) {x : T}
    (hx : x ∈ O) : Subsingleton (ToType (F.stalk x)) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq a
  obtain ⟨U', hxU', t, rfl⟩ := F.exists_germ_eq b
  have := hF (U ⊓ U' ⊓ O) inf_le_right
  have h1 := F.germ_res_apply (homOfLE (inf_le_left.trans inf_le_left : U ⊓ U' ⊓ O ≤ U)) x
    ⟨⟨hxU, hxU'⟩, hx⟩ s
  have h2 := F.germ_res_apply (homOfLE (inf_le_left.trans inf_le_right : U ⊓ U' ⊓ O ≤ U')) x
    ⟨⟨hxU, hxU'⟩, hx⟩ t
  rw [← h1, ← h2, Subsingleton.elim (F.map _ s) (F.map _ t)]

variable (f : T' ⟶ T)

/-- The stalks of `f_* B` off the closed range of `f` are trivial. -/
theorem subsingleton_stalk_pushforward (hf : IsClosed (Set.range f))
    (B : TopCat.Sheaf AddCommGrpCat.{0} T') {x : T} (hx : x ∉ Set.range f) :
    Subsingleton (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B).presheaf.stalk x) := by
  refine subsingleton_stalk_of_forall_le ⟨(Set.range f)ᶜ, hf.isOpen_compl⟩ (fun W hW => ?_) hx
  have : (Opens.map f).obj W = ⊥ := by
    ext y
    simp only [Opens.map_obj, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hy
    exact hW hy ⟨y, rfl⟩
  exact subsingleton_of_isTerminal (B.isTerminalOfEqEmpty this)

variable {f}

/-- For an inducing map with closed range, a map `A ⟶ f_* B` with bijective stalk maps, where `A`
has trivial stalks off the range, is bijective on all sections. -/
theorem app_bijective_of_stalkMap_bijective_of_isClosed (hi : Topology.IsInducing f)
    (hf : IsClosed (Set.range f))
    {A : TopCat.Sheaf AddCommGrpCat.{0} T} {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    (hφ : ∀ y, Function.Bijective (stalkMap f φ y))
    (hA : ∀ x ∉ Set.range f, Subsingleton (A.presheaf.stalk x)) (U : Opens T) :
    Function.Bijective (φ.hom.app (op U)) := by
  refine app_bijective_of_stalkFunctor_map_bijective φ U fun x _ => ?_
  by_cases hx : x ∈ Set.range f
  · obtain ⟨y, rfl⟩ := hx
    have : IsIso (B.presheaf.stalkPushforward AddCommGrpCat.{0} f y) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{0}
        hi B.presheaf y
    have h2 : Function.Bijective (B.presheaf.stalkPushforward AddCommGrpCat.{0} f y) :=
      ConcreteCategory.bijective_of_isIso _
    have h := hφ y
    change Function.Bijective (⇑(B.presheaf.stalkPushforward AddCommGrpCat.{0} f y) ∘
      ⇑((stalkFunctor AddCommGrpCat.{0} (f y)).map φ.hom)) at h
    exact (Function.Bijective.of_comp_iff' h2 _).1 h
  · have h1 := hA x hx
    have h2 := subsingleton_stalk_pushforward f hf B hx
    exact ⟨fun a b _ => @Subsingleton.elim _ h1 a b, fun b => ⟨0, @Subsingleton.elim _ h2 _ _⟩⟩

/-- For an injective `f`, the lift `G(A) ⟶ f_* G(B)` of a map with bijective stalk maps, where `A`
has trivial stalks off the range, is bijective on all sections. -/
theorem godementLiftHom_app_bijective_of_subsingleton (hinj : Function.Injective f)
    {A : TopCat.Sheaf AddCommGrpCat.{0} T} {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    (hφ : ∀ y, Function.Bijective (stalkMap f φ y))
    (hA : ∀ x ∉ Set.range f, Subsingleton (A.presheaf.stalk x)) (U : Opens T) :
    Function.Bijective ((godementLiftHom f φ).hom.app (op U)) := by
  classical
  constructor
  · intro s t h
    funext x
    by_cases hx : x.1 ∈ Set.range f
    · obtain ⟨y, hy⟩ := hx
      obtain ⟨x, hxU⟩ := x
      subst hy
      exact (hφ y).1 (congrFun h ⟨y, hxU⟩)
    · haveI := hA x.1 hx
      exact Subsingleton.elim _ _
  · intro t
    let g : (y : T') → f y ∈ U → A.presheaf.stalk (f y) := fun y hy =>
      Function.surjInv (hφ y).2 (t ⟨y, hy⟩)
    let s : (x : U) → A.presheaf.stalk x.1 := fun x =>
      if hx : ∃ y, f y = x.1 then
        cast (congrArg (fun z => (A.presheaf.stalk z : Type)) hx.choose_spec)
          (g hx.choose (show f hx.choose ∈ U by rw [hx.choose_spec]; exact x.2))
      else 0
    have key : ∀ (y : T') (hy : f y ∈ U), s ⟨f y, hy⟩ = g y hy := by
      intro y hy
      have hex : ∃ y', f y' = f y := ⟨y, rfl⟩
      have : ∀ (y' : T') (e : f y' = f y) (h' : f y' ∈ U),
          cast (congrArg (fun z => (A.presheaf.stalk z : Type)) e) (g y' h') = g y hy := by
        rintro y' e h'
        obtain rfl := hinj e
        rfl
      simp only [s, dif_pos hex]
      exact this _ hex.choose_spec _
    refine ⟨s, funext fun y => ?_⟩
    change stalkMap f φ y.1 (s ⟨f y.1, y.2⟩) = t y
    rw [key y.1 y.2]
    exact Function.surjInv_eq (hφ y.1).2 _

/-- A map of sheaves bijective on all sections has bijective stalk maps along an inducing map. -/
theorem stalkMap_bijective_of_forall_app_bijective (hi : Topology.IsInducing f)
    {A : TopCat.Sheaf AddCommGrpCat.{0} T} {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    (hφ : ∀ U : Opens T, Function.Bijective (φ.hom.app (op U))) (y : T') :
    Function.Bijective (stalkMap f φ y) := by
  have h1 := stalkFunctor_map_bijective_of_app_bijective φ.hom ⊤ (fun U _ => hφ U) (f y) trivial
  have : IsIso (B.presheaf.stalkPushforward AddCommGrpCat.{0} f y) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{0}
      hi B.presheaf y
  have h2 : Function.Bijective (B.presheaf.stalkPushforward AddCommGrpCat.{0} f y) :=
    ConcreteCategory.bijective_of_isIso _
  change Function.Bijective (⇑(B.presheaf.stalkPushforward AddCommGrpCat.{0} f y) ∘
    ⇑((stalkFunctor AddCommGrpCat.{0} (f y)).map φ.hom))
  exact h2.comp h1

/-- The Godement sheaf of a sheaf with trivial stalks off a closed set has trivial stalks off
it. -/
theorem subsingleton_stalk_godement {A : TopCat.Sheaf AddCommGrpCat.{0} T} {Z : Set T}
    (hZ : IsClosed Z) (hA : ∀ x ∉ Z, Subsingleton (A.presheaf.stalk x)) {x : T} (hx : x ∉ Z) :
    Subsingleton (((godementFunctor T).obj A).presheaf.stalk x) := by
  refine subsingleton_stalk_of_forall_le ⟨Zᶜ, hZ.isOpen_compl⟩ (fun W hW => ?_) hx
  have : ∀ w : W, Subsingleton (A.presheaf.stalk w.1) := fun w => hA w.1 (hW w.2)
  exact inferInstanceAs (Subsingleton ((w : W) → A.presheaf.stalk w.1))

/-- A cokernel of a map into a sheaf with trivial stalk at `x` has trivial stalk at `x`. -/
theorem subsingleton_stalk_cokernel {A₁ A₂ : TopCat.Sheaf AddCommGrpCat.{0} T} (d : A₁ ⟶ A₂)
    {x : T} (h : Subsingleton (A₂.presheaf.stalk x)) :
    Subsingleton ((cokernel d).presheaf.stalk x) := by
  obtain ⟨hs, -⟩ := surjective_and_exact_map_cokernel
    (TopCat.Sheaf.forget AddCommGrpCat.{0} T ⋙ stalkFunctor AddCommGrpCat.{0} x) d
  haveI : Subsingleton ((TopCat.Sheaf.forget AddCommGrpCat.{0} T ⋙
    stalkFunctor AddCommGrpCat.{0} x).obj A₂) := h
  exact hs.subsingleton

/-- The stages of the comparison of Godement resolutions along a closed embedding. -/
theorem stageHom_godementPullbackLift_of_isClosedEmbedding (hf : Topology.IsClosedEmbedding f)
    {F : TopCat.Sheaf AddCommGrpCat.{0} T} {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
    (φ : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B)
    (hφ : ∀ y, Function.Bijective (stalkMap f φ y))
    (hF : ∀ x ∉ Set.range f, Subsingleton (F.presheaf.stalk x)) (n : ℕ) :
    (∀ y, Function.Bijective (stalkMap f
      (CokernelCoresolution.stageHom (godementPullbackLift f) φ n).1 y)) ∧
    (∀ y, Function.Bijective (stalkMap f
      (CokernelCoresolution.stageHom (godementPullbackLift f) φ n).2.1 y)) ∧
    (∀ x ∉ Set.range f, Subsingleton
      ((CokernelCoresolution.stage (godementFunctor T) (godementUnit T) F n).1.presheaf.stalk x)) ∧
    (∀ x ∉ Set.range f, Subsingleton
      ((CokernelCoresolution.stage (godementFunctor T) (godementUnit T) F n).2.1.presheaf.stalk
        x)) := by
  have lift : ∀ {A : TopCat.Sheaf AddCommGrpCat.{0} T} {B : TopCat.Sheaf AddCommGrpCat.{0} T'}
      (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj B),
      (∀ y, Function.Bijective (stalkMap f ψ y)) →
      (∀ x ∉ Set.range f, Subsingleton (A.presheaf.stalk x)) →
        ∀ y, Function.Bijective (stalkMap f (godementLiftHom f ψ) y) := fun ψ hψ hA =>
    stalkMap_bijective_of_forall_app_bijective hf.isInducing _
      (godementLiftHom_app_bijective_of_subsingleton hf.injective ψ hψ hA)
  induction n with
  | zero =>
    exact ⟨hφ, lift φ hφ hF, hF, fun x hx => subsingleton_stalk_godement hf.isClosed_range hF hx⟩
  | succ n ih =>
    let p := CokernelCoresolution.stageHom (godementPullbackLift f) φ n
    have hc : ∀ x ∉ Set.range f, Subsingleton ((cokernel
        (CokernelCoresolution.stage (godementFunctor T) (godementUnit T) F n).2.2).presheaf.stalk
          x) := fun x hx => subsingleton_stalk_cokernel _ (ih.2.2.2 x hx)
    refine ⟨ih.2.1, lift _ ?_ hc, ih.2.2.2,
      fun x hx => subsingleton_stalk_godement hf.isClosed_range hc hx⟩
    exact stalkMap_cokernel_bijective f _ _ p.1 p.2.1 (CokernelCoresolution.cokerDesc p) p.2.2
      (CokernelCoresolution.π_cokerDesc p) ih.1 ih.2.1

/-- **The Godement resolution along a closed embedding.** For a closed embedding `f` and a sheaf
`F` with trivial stalks off the image of `f`, the comparison `G^•(F) ⟶ f_* G^•(f⁻¹ F)` is
bijective on all sections. -/
theorem godementResolutionPullback_app_bijective_of_isClosedEmbedding
    (hf : Topology.IsClosedEmbedding f) (F : TopCat.Sheaf AddCommGrpCat.{0} T)
    (hF : ∀ x ∉ Set.range f, Subsingleton (F.presheaf.stalk x)) (n : ℕ) (U : Opens T) :
    Function.Bijective (((godementResolutionPullback f F).f n).hom.app (op U)) := by
  have h := stageHom_godementPullbackLift_of_isClosedEmbedding hf
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app F)
    (fun y => @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _
        (stalkMap f ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app F)
          y) (isIso_stalkMap_pullbackPushforwardAdjunction_unit f F y)) hF n
  exact app_bijective_of_stalkMap_bijective_of_isClosed hf.isInducing hf.isClosed_range _
    h.2.1 h.2.2.2 U

/-- Sections, hence stalks, of a zero sheaf are trivial. -/
theorem subsingleton_stalk_of_isZero {A : TopCat.Sheaf AddCommGrpCat.{0} T} (hA : IsZero A)
    (x : T) : Subsingleton (A.presheaf.stalk x) := by
  refine subsingleton_stalk_of_forall_le ⊤ (fun W _ => ⟨fun a b => ?_⟩) trivial
  have e : (𝟙 A : A ⟶ A) = 0 := hA.eq_of_src _ _
  have ha : a = 0 := congrArg (fun g : A ⟶ A => g.hom.app (op W) a) e
  have hb : b = 0 := congrArg (fun g : A ⟶ A => g.hom.app (op W) b) e
  rw [ha, hb]

/-- **Cohomology along a closed embedding.** For a closed embedding `f` and a sheaf `F` with
trivial stalks off the image of `f`, the pullback `H^n(T, F) ⟶ H^n(T', f⁻¹ F)` is an
isomorphism. -/
theorem isIso_sheafCohomologyPullback_of_isClosedEmbedding (hf : Topology.IsClosedEmbedding f)
    (F : TopCat.Sheaf AddCommGrpCat.{0} T)
    (hF : ∀ x ∉ Set.range f, Subsingleton (F.presheaf.stalk x)) (n : ℤ) :
    IsIso (sheafCohomologyPullback f F n) := by
  let K :=
    (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat.{0} T) (ComplexShape.up ℤ) 0).obj F
  have hK : ∀ q, ∀ x ∉ Set.range f, Subsingleton ((K.X q).presheaf.stalk x) := by
    intro q x hx
    by_cases hq : q = 0
    · subst hq
      exact hF x hx
    · exact subsingleton_stalk_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq) x
  have hsec : ∀ q, IsIso (godementSectionsPullback f (K.X q)) := by
    intro q
    have : IsIso (((globalSections T).mapHomologicalComplex _).map
        (godementResolutionPullback f (K.X q))) := by
      have : ∀ k, IsIso ((((globalSections T).mapHomologicalComplex _).map
          (godementResolutionPullback f (K.X q))).f k) := fun k =>
        (ConcreteCategory.isIso_iff_bijective _).2
          (godementResolutionPullback_app_bijective_of_isClosedEmbedding hf (K.X q) (hK q) k ⊤)
      exact HomologicalComplex.Hom.isIso_of_components _
    exact ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{0}).mapIso
      (asIso (((globalSections T).mapHomologicalComplex _).map
        (godementResolutionPullback f (K.X q))))).isIso_hom
  have h1 : IsIso (godementSectionsDoubleComplexPullback f K) := by
    have : ∀ q, IsIso ((godementSectionsDoubleComplexPullback f K).f q) := hsec
    exact HomologicalComplex.Hom.isIso_of_components _
  let e := asIso (godementSectionsDoubleComplexPullback f K)
  have h2 : IsIso (HomologicalComplex₂.total.map (godementSectionsDoubleComplexPullback f K)
      (ComplexShape.up ℤ)) :=
    ⟨HomologicalComplex₂.total.map e.inv (ComplexShape.up ℤ), by
      rw [← HomologicalComplex₂.total.map_comp]
      simp [e], by
      rw [← HomologicalComplex₂.total.map_comp]
      simp [e]⟩
  have h3 : IsIso (hypercohomologyPullback f K n) := by
    unfold hypercohomologyPullback
    exact (HomologicalComplex.homologyFunctor _ _ n).map_isIso _
  unfold sheafCohomologyPullback
  exact IsIso.comp_isIso' h3 (Functor.map_isIso _ _)

/-- Along an inducing map the counit `f⁻¹ f_* S ⟶ S` is an isomorphism. -/
theorem isIso_pullbackPushforwardAdjunction_counit (hi : Topology.IsInducing f)
    (S : TopCat.Sheaf AddCommGrpCat.{0} T') :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).counit.app S) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f
  have : ∀ y, IsIso ((stalkFunctor AddCommGrpCat.{0} y).map (adj.counit.app S).hom) := by
    intro y
    have htri := adj.right_triangle_components S
    have e := congrArg (fun g => stalkMap f g y) htri
    simp only at e
    rw [stalkMap_comp_pushforward] at e
    have i1 := isIso_stalkMap_pullbackPushforwardAdjunction_unit f
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj S) y
    have i2 : IsIso (stalkMap f (𝟙 ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj S)) y) := by
      have : IsIso (S.presheaf.stalkPushforward AddCommGrpCat.{0} f y) :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{0}
          hi S.presheaf y
      change IsIso ((stalkFunctor AddCommGrpCat.{0} (f y)).map (𝟙 _) ≫ _)
      rw [CategoryTheory.Functor.map_id]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (IsIso.id _) this
    rw [← e] at i2
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ i1 i2
  exact isIso_of_stalkFunctor_map_iso _

end Godement

section Restricted

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  (Z : Set M)

variable (n) in
/-- A function on an open set of `Z` is *locally a restriction* if near every point it is the
restriction of a holomorphic function on an open set of `M`. -/
def restrictedPredicate : LocalPredicate (fun _ : TopCat.of Z => ℂ) where
  pred {W} f := ∀ w : W, ∃ (U : Opens M) (hw : (w : Z).1 ∈ U) (g : 𝒪[n, M].presheaf.obj (op U)),
    ∀ v : W, ∀ hv : (v : Z).1 ∈ U, f v = g ⟨(v : Z).1, hv⟩
  res {W W'} i f hf w := by
    obtain ⟨U, hw, g, hg⟩ := hf ⟨w.1, i.le w.2⟩
    exact ⟨U, hw, g, fun v hv => hg ⟨v.1, i.le v.2⟩ hv⟩
  locality {W} f hf w := by
    obtain ⟨V, hwV, i, hV⟩ := hf w
    obtain ⟨U, hw, g, hg⟩ := hV ⟨w, hwV⟩
    obtain ⟨U', hU'⟩ := (isOpen_induced_iff.1 V.isOpen)
    refine ⟨U ⊓ ⟨U', hU'.1⟩, ⟨hw, ?_⟩, 𝒪[n, M].presheaf.map (homOfLE inf_le_left).op g,
      fun v hv => ?_⟩
    · have : (w : Z) ∈ (V : Set Z) := hwV
      rw [← hU'.2] at this
      exact this
    · have hvV : (v : Z) ∈ V := by
        rw [← SetLike.mem_coe, ← hU'.2]
        exact hv.2
      exact hg ⟨v, hvV⟩ hv.1

variable (n) in
/-- The subring of functions on an open set of `Z` which are locally restrictions of
holomorphic functions on `M`. -/
def restrictedSubring (W : Opens (TopCat.of Z)) : Subring (W → ℂ) where
  carrier := {f | (restrictedPredicate n Z).pred f}
  one_mem' w := ⟨⊤, trivial, 1, fun _ _ => rfl⟩
  zero_mem' w := ⟨⊤, trivial, 0, fun _ _ => rfl⟩
  mul_mem' {f g} hf hg w := by
    obtain ⟨U, hw, a, ha⟩ := hf w
    obtain ⟨U', hw', b, hb⟩ := hg w
    refine ⟨U ⊓ U', ⟨hw, hw'⟩, 𝒪[n, M].presheaf.map (homOfLE inf_le_left).op a *
      𝒪[n, M].presheaf.map (homOfLE inf_le_right).op b, fun v hv => ?_⟩
    change f v * g v = a ⟨_, hv.1⟩ * b ⟨_, hv.2⟩
    rw [ha v hv.1, hb v hv.2]
  add_mem' {f g} hf hg w := by
    obtain ⟨U, hw, a, ha⟩ := hf w
    obtain ⟨U', hw', b, hb⟩ := hg w
    refine ⟨U ⊓ U', ⟨hw, hw'⟩, 𝒪[n, M].presheaf.map (homOfLE inf_le_left).op a +
      𝒪[n, M].presheaf.map (homOfLE inf_le_right).op b, fun v hv => ?_⟩
    change f v + g v = a ⟨_, hv.1⟩ + b ⟨_, hv.2⟩
    rw [ha v hv.1, hb v hv.2]
  neg_mem' {f} hf w := by
    obtain ⟨U, hw, a, ha⟩ := hf w
    refine ⟨U, hw, -a, fun v hv => ?_⟩
    change -f v = -a ⟨_, hv⟩
    rw [ha v hv]

variable (n) in
/-- The presheaf of rings of functions on `Z` locally restricted from `𝒪_M`. -/
def restrictedPresheaf : TopCat.Presheaf CommRingCat.{0} (TopCat.of Z) where
  obj W := CommRingCat.of (restrictedSubring n Z W.unop)
  map {W W'} i := CommRingCat.ofHom
    { toFun := fun f => ⟨fun w => f.1 ⟨w.1, i.unop.le w.2⟩,
        (restrictedPredicate n Z).res i.unop f.1 f.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

variable (n) in
/-- The sheaf of rings `𝒪'_Z` of functions on `Z` locally restricted from `𝒪_M`. -/
def restrictedSheaf : TopCat.Sheaf CommRingCat.{0} (TopCat.of Z) where
  obj := restrictedPresheaf n Z
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget CommRingCat)]
    exact TopCat.subpresheafToTypes.isSheaf (restrictedPredicate n Z)

end Restricted

section StalkR

open TopCat.Presheaf

variable {T T' : TopCat.{0}} (f : T' ⟶ T)

/-- The stalk maps `(f_* B)_{f y} ⟶ B_y` are natural in `B`. -/
theorem stalkFunctor_map_pushforward_comp_stalkPushforwardR
    {B B' : TopCat.Presheaf CommRingCat.{0} T'} (b : B ⟶ B') (y : T') :
    (stalkFunctor CommRingCat.{0} (f y)).map ((Presheaf.pushforward CommRingCat.{0} f).map b) ≫
        B'.stalkPushforward CommRingCat.{0} f y =
      B.stalkPushforward CommRingCat.{0} f y ≫ (stalkFunctor CommRingCat.{0} y).map b := by
  refine stalk_hom_ext _ fun U hU => ?_
  erw [stalkFunctor_map_germ_assoc, stalkPushforward_germ, stalkPushforward_germ_assoc,
    stalkFunctor_map_germ]
  rfl

/-- The stalk map `A_{f y} ⟶ (f_* B)_{f y} ⟶ B_y` of a map `φ : A ⟶ f_* B` of sheaves of
rings. -/
noncomputable abbrev stalkMapR {A : TopCat.Sheaf CommRingCat.{0} T}
    {B : TopCat.Sheaf CommRingCat.{0} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward CommRingCat.{0} f).obj B) (y : T') :
    A.presheaf.stalk (f y) ⟶ B.presheaf.stalk y :=
  (stalkFunctor CommRingCat.{0} (f y)).map φ.hom ≫
    B.presheaf.stalkPushforward CommRingCat.{0} f y

/-- The stalk map of `φ` followed by the direct image of `b` is the stalk map of `φ` followed by
the stalk map of `b`. -/
theorem stalkMapR_comp_pushforward {A : TopCat.Sheaf CommRingCat.{0} T}
    {B B' : TopCat.Sheaf CommRingCat.{0} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward CommRingCat.{0} f).obj B) (b : B ⟶ B') (y : T') :
    stalkMapR f (φ ≫ (TopCat.Sheaf.pushforward CommRingCat.{0} f).map b) y =
      stalkMapR f φ y ≫ (stalkFunctor CommRingCat.{0} y).map b.hom :=
  (congrArg (fun g => CategoryStruct.comp g (B'.presheaf.stalkPushforward CommRingCat.{0} f y))
    ((stalkFunctor _ (f y)).map_comp φ.hom ((Presheaf.pushforward _ f).map b.hom))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun g => CategoryStruct.comp _ g)
        (stalkFunctor_map_pushforward_comp_stalkPushforwardR f b.hom y)).trans
        (Category.assoc _ _ _).symm))

/-- The stalk maps `F_{f y} ⟶ (f⁻¹ F)_y` of the unit `F ⟶ f_* f⁻¹ F` are isomorphisms, for
sheaves of rings. -/
theorem isIso_stalkMapR_unit (F : TopCat.Sheaf CommRingCat.{0} T) (y : T') :
    IsIso (stalkMapR f ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} f).unit.app F)
      y) :=
  Stacks.Sheaves.PullbackUnit.isIso_stalkComparison f F y

end StalkR

section Psi

open TopCat.Presheaf

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  (Z : Set M)

variable (n) in
/-- Restriction of holomorphic functions on `U ⊆ M` to `Z ∩ U`. -/
def restrictHom (U : Opens (TopCat.of M)) :
    𝒪[n, M].presheaf.obj (op U) →+*
      restrictedSubring n Z ((Opens.map (submanifoldInclusion Z)).obj U) where
  toFun g := ⟨fun w => g ⟨w.1.1, w.2⟩, fun w => ⟨U, w.2, g, fun _ _ => rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (n) in
/-- The map `𝒪_M / ℐ_Z ⟶ ι_* 𝒪'_Z`, restriction of functions to `Z`. -/
def quotientToRestricted : quotientVanishingIdealPresheaf n Z ⟶
    (TopCat.Presheaf.pushforward CommRingCat.{0} (submanifoldInclusion Z)).obj
      (restrictedPresheaf n Z) where
  app U := CommRingCat.ofHom (Ideal.Quotient.lift (vanishingIdeal n Z U.unop)
    (restrictHom n Z U.unop) fun g hg => Subtype.ext (funext fun w => hg ⟨w.1.1, w.2⟩ w.1.2))
  naturality U V i := by
    ext x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- The stalk maps of `𝒪_M / ℐ_Z ⟶ ι_* 𝒪'_Z` are bijective. -/
theorem quotientToRestricted_stalk_bijective (hZ : IsClosed Z) (x : M) :
    Function.Bijective ((stalkFunctor CommRingCat.{0} x).map (quotientToRestricted n Z)) := by
  let Q := quotientVanishingIdealPresheaf n Z
  let P' := (TopCat.Presheaf.pushforward CommRingCat.{0} (submanifoldInclusion Z)).obj
    (restrictedPresheaf n Z)
  constructor
  · refine (injective_iff_map_eq_zero (ConcreteCategory.hom
      ((stalkFunctor CommRingCat.{0} x).map (quotientToRestricted n Z)))).2 fun a ha => ?_
    obtain ⟨U, hxU, a, rfl⟩ := Q.exists_germ_eq a
    rw [stalkFunctor_map_germ_apply] at ha
    have ha' : P'.germ U x hxU ((quotientToRestricted n Z).app (op U) a) =
        P'.germ U x hxU 0 := ha.trans (map_zero _).symm
    obtain ⟨W, hxW, i1, i2, he⟩ := P'.germ_eq x hxU hxU _ _ ha'
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (I := vanishingIdeal n Z U) a
    have hmem : 𝒪[n, M].presheaf.map i1.op g ∈ vanishingIdeal n Z W := by
      intro w hw
      have := congrArg (fun h : P'.obj (op W) => h.1 ⟨⟨w.1, hw⟩, w.2⟩) he
      rwa [← hg] at this
    have h0 : Q.map i1.op a = 0 := by
      subst hg
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem
    rw [← Q.germ_res_apply i1 x hxW, h0]
    exact map_zero _
  · intro t
    obtain ⟨U, hxU, h, rfl⟩ := P'.exists_germ_eq t
    by_cases hxZ : x ∈ Z
    · obtain ⟨U₁, hx₁, g, hg⟩ := h.2 ⟨⟨x, hxZ⟩, hxU⟩
      have hx' : x ∈ U ⊓ U₁ := ⟨hxU, hx₁⟩
      let q : Q.obj (op (U ⊓ U₁)) := Ideal.Quotient.mk (vanishingIdeal n Z (U ⊓ U₁))
        (𝒪[n, M].presheaf.map (homOfLE inf_le_right).op g)
      refine ⟨Q.germ (U ⊓ U₁) x hx' q, ?_⟩
      rw [stalkFunctor_map_germ_apply, ← P'.germ_res_apply (homOfLE inf_le_left) x hx' h]
      exact congrArg _ (Subtype.ext (funext fun w =>
        (hg ⟨w.1, (inf_le_left : U ⊓ U₁ ≤ U) w.2⟩ w.2.2).symm))
    · have hs : Subsingleton (P'.stalk x) := by
        refine subsingleton_stalk_of_forall_le ⟨Zᶜ, hZ.isOpen_compl⟩ (fun W hW => ?_)
          (show x ∈ (⟨Zᶜ, hZ.isOpen_compl⟩ : Opens M) from hxZ)
        exact ⟨fun a b => Subtype.ext (funext fun w => absurd w.1.2 (hW w.2))⟩
      exact ⟨0, @Subsingleton.elim _ hs _ _⟩

variable (n) in
/-- The map `𝒪_M / ℐ_Z ⟶ ι_* 𝒪'_Z` of sheaves of rings. -/
def quotientSheafToRestricted : quotientVanishingIdealSheaf n Z ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{0} (submanifoldInclusion Z)).obj
      (restrictedSheaf n Z) :=
  ObjectProperty.homMk (sheafifyLift _ (quotientToRestricted n Z)
    ((TopCat.Sheaf.pushforward CommRingCat.{0} (submanifoldInclusion Z)).obj
      (restrictedSheaf n Z)).property)

/-- `quotientSheafToRestricted` restricts to `quotientToRestricted` along sheafification. -/
theorem toSheafify_quotientSheafToRestricted :
    toSheafify _ (quotientVanishingIdealPresheaf n Z) ≫ (quotientSheafToRestricted n Z).hom =
      quotientToRestricted n Z :=
  toSheafify_sheafifyLift _ _ _

/-- For closed `Z`, `𝒪_M / ℐ_Z ⟶ ι_* 𝒪'_Z` is an isomorphism on every stalk. -/
theorem isIso_stalk_quotientSheafToRestricted (hZ : IsClosed Z) (x : M) :
    IsIso ((stalkFunctor CommRingCat.{0} x).map (quotientSheafToRestricted n Z).hom) := by
  have i1 := stalkFunctor_map_unit_toSheafify_isIso x CommRingCat.{0}
    (quotientVanishingIdealPresheaf n Z)
  have i2 : IsIso ((stalkFunctor CommRingCat.{0} x).map (quotientToRestricted n Z)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (quotientToRestricted_stalk_bijective Z hZ x)
  rw [← toSheafify_quotientSheafToRestricted] at i2
  have e := (stalkFunctor CommRingCat.{0} x).map_comp
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
      (quotientVanishingIdealPresheaf n Z)) (quotientSheafToRestricted n Z).hom
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ i1 (cast (congrArg IsIso e) i2)

/-- For closed `Z`, `𝒪_M / ℐ_Z ⟶ ι_* 𝒪'_Z` is an isomorphism of sheaves of rings. -/
theorem isIso_quotientSheafToRestricted (hZ : IsClosed Z) :
    IsIso (quotientSheafToRestricted n Z) := by
  have := isIso_stalk_quotientSheafToRestricted (n := n) Z hZ
  exact isIso_of_stalkFunctor_map_iso _

variable (n) in
/-- The comparison `𝒪_Z ⟶ 𝒪'_Z` of the structure sheaf of `Z` with the sheaf of functions
locally restricted from `𝒪_M`. -/
def structureSheafToRestricted :
    (TopCat.Sheaf.pullback CommRingCat.{0} (submanifoldInclusion Z)).obj
      (quotientVanishingIdealSheaf n Z) ⟶ restrictedSheaf n Z :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} (submanifoldInclusion Z)).homEquiv
    _ _).symm (quotientSheafToRestricted n Z)

/-- The unit of the pullback–pushforward adjunction followed by the direct image of
`structureSheafToRestricted` is `quotientSheafToRestricted`. -/
theorem unit_comp_structureSheafToRestricted :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} (submanifoldInclusion Z)).unit.app
        (quotientVanishingIdealSheaf n Z) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{0} (submanifoldInclusion Z)).map
        (structureSheafToRestricted n Z) = quotientSheafToRestricted n Z :=
  ((Adjunction.homEquiv_unit _ _ _ _).symm).trans (Equiv.apply_symm_apply _ _)

/-- For closed `Z`, the comparison `𝒪_Z ⟶ 𝒪'_Z` is an isomorphism. -/
theorem isIso_structureSheafToRestricted (hZ : IsClosed Z) :
    IsIso (structureSheafToRestricted n Z) := by
  have hi : Topology.IsInducing (submanifoldInclusion Z) := Topology.IsInducing.subtypeVal
  have : ∀ z : Z, IsIso ((stalkFunctor CommRingCat.{0} z).map
      (structureSheafToRestricted n Z).hom) := by
    intro z
    have e := congrArg (fun g => stalkMapR (submanifoldInclusion Z) g z)
      (unit_comp_structureSheafToRestricted (n := n) Z)
    simp only at e
    rw [stalkMapR_comp_pushforward] at e
    have i1 := isIso_stalkMapR_unit (submanifoldInclusion Z) (quotientVanishingIdealSheaf n Z) z
    have i2 : IsIso (stalkMapR (submanifoldInclusion Z) (quotientSheafToRestricted n Z) z) := by
      have j1 : IsIso ((restrictedSheaf n Z).presheaf.stalkPushforward CommRingCat.{0}
          (submanifoldInclusion Z) z) :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat.{0}
          hi _ z
      have j2 := isIso_stalk_quotientSheafToRestricted (n := n) Z hZ (submanifoldInclusion Z z)
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ j2 j1
    rw [← e] at i2
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ i1 i2
  exact isIso_of_stalkFunctor_map_iso _

/-- For closed `Z`, the unit of the pullback–pushforward adjunction along `Z ⊆ M` is an isomorphism
at `𝒪_M / ℐ_Z`. -/
theorem isIso_unit_quotientVanishingIdealSheaf (hZ : IsClosed Z) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0}
      (submanifoldInclusion Z)).unit.app (quotientVanishingIdealSheaf n Z)) := by
  haveI := isIso_structureSheafToRestricted (n := n) Z hZ
  haveI := isIso_quotientSheafToRestricted (n := n) Z hZ
  have e := unit_comp_structureSheafToRestricted (n := n) Z
  have : IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0}
      (submanifoldInclusion Z)).unit.app (quotientVanishingIdealSheaf n Z) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{0} (submanifoldInclusion Z)).map
        (structureSheafToRestricted n Z)) := by rw [e]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((TopCat.Sheaf.pushforward CommRingCat.{0}
    (submanifoldInclusion Z)).map (structureSheafToRestricted n Z))

end Psi

section LocalModel

open Topology

/-- The inclusion of `ℂᵏ` into `ℂⁿ` as the first `k` coordinates. -/
def coordIncl (k n : ℕ) : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun i : Fin n =>
      if h : (i : ℕ) < k then ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) ⟨i, h⟩
      else 0) ∘L
    (EuclideanSpace.equiv (Fin k) ℂ).toContinuousLinearMap

/-- The projection of `ℂⁿ` onto its first `k` coordinates. -/
def coordProj {k n : ℕ} (hk : k ≤ n) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℂ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun j : Fin k =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE hk j)) ∘L
    (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap

/-- The coordinates of `coordIncl k n w` are those of `w` below `k` and zero from `k` on. -/
theorem coordIncl_apply {k n : ℕ} (w : EuclideanSpace ℂ (Fin k)) (i : Fin n) :
    coordIncl k n w i = if h : (i : ℕ) < k then w ⟨i, h⟩ else 0 := by
  change (if h : (i : ℕ) < k then ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) ⟨i, h⟩
      else 0) (EuclideanSpace.equiv (Fin k) ℂ w) = _
  split_ifs <;> rfl

/-- The coordinates of `coordProj hk y` are the first `k` coordinates of `y`. -/
theorem coordProj_apply {k n : ℕ} (hk : k ≤ n) (y : EuclideanSpace ℂ (Fin n)) (j : Fin k) :
    coordProj hk y j = y (Fin.castLE hk j) := rfl

/-- Projecting onto the first `k` coordinates is a left inverse of `coordIncl k n`. -/
theorem coordProj_coordIncl {k n : ℕ} (hk : k ≤ n) (w : EuclideanSpace ℂ (Fin k)) :
    coordProj hk (coordIncl k n w) = w := by
  ext j
  rw [coordProj_apply, coordIncl_apply, dif_pos (by simp)]
  rfl

/-- A point of `ℂⁿ` whose coordinates from `k` on vanish is the inclusion of its projection. -/
theorem coordIncl_coordProj {k n : ℕ} (hk : k ≤ n) (y : EuclideanSpace ℂ (Fin n))
    (hy : ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0) : coordIncl k n (coordProj hk y) = y := by
  ext i
  rw [coordIncl_apply]
  split_ifs with h
  · rfl
  · exact (hy i (not_lt.1 h)).symm

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M]
  {Z : Set M} {φ : OpenPartialHomeomorph M (EuclideanSpace ℂ (Fin n))} {k : ℕ}

/-- A function on an open subset of an open set of `ℂᵏ` which agrees near `w` with a function
complex differentiable on an open set is holomorphic at `w`. -/
theorem contMDiffAt_of_eventuallyEq_differentiableOn {V : Opens (EuclideanSpace ℂ (Fin k))}
    {W' : Opens (TopCat.of V)} {F : W' → ℂ} {G : EuclideanSpace ℂ (Fin k) → ℂ}
    {S : Set (EuclideanSpace ℂ (Fin k))} (hS : IsOpen S) (hG : DifferentiableOn ℂ G S) (w : W')
    (hw : (w : V).1 ∈ S) (hFG : ∀ᶠ w' in 𝓝 w, F w' = G (w' : V).1) :
    ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin k)) 𝓘(ℂ) ∞ F w := by
  have hGa := MMP.Analytic.analyticOnNhd_of_differentiableOn hS hG
  have hG' : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin k)) 𝓘(ℂ) ∞ G S :=
    contMDiffOn_iff_contDiffOn.2 (hGa.contDiffOn hS.uniqueDiffOn)
  have h1 : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin k)) 𝓘(ℂ) ∞ G (w : V).1 :=
    hG'.contMDiffAt (hS.mem_nhds hw)
  have h2 : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin k)) 𝓘(ℂ) ∞ (fun v : V => G v.1) (w : V) :=
    contMDiffAt_subtype_iff.2 h1
  have h3 : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin k)) 𝓘(ℂ) ∞ (fun w' : W' => G (w' : V).1) w :=
    contMDiffAt_subtype_iff.2 h2
  exact h3.congr_of_eventuallyEq hFG

/-- A holomorphic function on an open subset of an open set of `ℂᵏ`, extended by zero, is complex
differentiable on that subset. -/
theorem differentiableOn_extend_nested {V : Opens (EuclideanSpace ℂ (Fin k))}
    {W' : Opens (TopCat.of V)} (g : W' → ℂ)
    (hg : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin k)) 𝓘(ℂ) ∞ g) :
    DifferentiableOn ℂ (Function.extend (fun w : W' => (w : V).1) g 0)
      (Subtype.val '' (W' : Set V)) := by
  rintro _ ⟨v, hv, rfl⟩
  set G := Function.extend (fun w : W' => (w : V).1) g 0
  have hinj : Function.Injective (fun w : W' => (w : V).1) :=
    Subtype.val_injective.comp Subtype.val_injective
  have h1 : (fun w' : W' => G (w' : V).1) = g := funext fun w' => hinj.extend_apply g 0 w'
  have h2 : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin k)) 𝓘(ℂ) ∞
      (fun w' : W' => (fun v : V => G v.1) w') ⟨v, hv⟩ := by
    rw [h1]; exact hg _
  have h3 := contMDiffAt_subtype_iff.1 (contMDiffAt_subtype_iff.1 h2)
  exact ((contMDiffAt_iff_contDiffAt.1 h3).differentiableAt (by simp)).differentiableWithinAt

/-- An open subset of an open set `V` is open in the ambient space. -/
theorem isOpen_image_nested {V : Opens (EuclideanSpace ℂ (Fin k))}
    (W' : Opens (TopCat.of V)) : IsOpen (Subtype.val '' (W' : Set V)) :=
  V.isOpen.isOpenMap_subtype_val _ W'.isOpen

/-- If `φ` flattens `Z`, the coordinates from `k` on of `φ z` vanish for every `z ∈ Z` in the
source. -/
theorem apply_eq_zero_of_flat
    (hflat : φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0})
    {z : M} (hz : z ∈ Z) (hs : z ∈ φ.source) : ∀ i : Fin n, k ≤ (i : ℕ) → φ z i = 0 := by
  have h : φ z ∈ φ '' (Z ∩ φ.source) := ⟨z, ⟨hz, hs⟩, rfl⟩
  rw [hflat] at h
  exact h.2

/-- If `φ` flattens `Z`, a point of the target whose coordinates from `k` on vanish is sent by
`φ.symm` into `Z`. -/
theorem symm_mem_of_flat
    (hflat : φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0})
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ φ.target) (hL : ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0) :
    φ.symm y ∈ Z := by
  have h : y ∈ φ '' (Z ∩ φ.source) := by rw [hflat]; exact ⟨hy, hL⟩
  obtain ⟨z, ⟨hz, hs⟩, rfl⟩ := h
  rwa [φ.left_inv hs]

variable (Z φ) in
/-- The points of `Z` in the source of the chart `φ`, an open subset of `Z`. -/
def modelSrc : Opens (TopCat.of Z) :=
  ⟨Subtype.val ⁻¹' φ.source, φ.open_source.preimage continuous_subtype_val⟩

variable (k φ) in
/-- The points of `ℂᵏ` whose image in `ℂⁿ` lies in the target of `φ`. -/
def modelTgt : Opens (EuclideanSpace ℂ (Fin k)) :=
  ⟨coordIncl k n ⁻¹' φ.target, φ.open_target.preimage (coordIncl k n).continuous⟩

/-- If `φ` flattens `Z`, then `φ u` is the inclusion of its projection for every
`u ∈ modelSrc Z φ`. -/
theorem coordIncl_coordProj_apply (hk : k ≤ n)
    (hflat : φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0})
    (u : modelSrc Z φ) : coordIncl k n (coordProj hk (φ u.1.1)) = φ u.1.1 :=
  coordIncl_coordProj hk _ (apply_eq_zero_of_flat hflat u.1.2 u.2)

/-- The flattening chart identifies `Z ∩ φ.source` with an open subset of `ℂᵏ`. -/
def modelHomeo (hk : k ≤ n)
    (hflat : φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0}) :
    modelSrc Z φ ≃ₜ modelTgt φ k where
  toFun u := ⟨coordProj hk (φ u.1.1), by
    change coordIncl k n (coordProj hk (φ u.1.1)) ∈ φ.target
    rw [coordIncl_coordProj_apply hk hflat]
    exact φ.map_source u.2⟩
  invFun v := ⟨⟨φ.symm (coordIncl k n v), symm_mem_of_flat hflat v.2 fun i hi => by
    rw [coordIncl_apply, dif_neg (by omega)]⟩, φ.map_target v.2⟩
  left_inv u := by
    apply Subtype.ext; apply Subtype.ext
    change φ.symm (coordIncl k n (coordProj hk (φ u.1.1))) = u.1.1
    rw [coordIncl_coordProj_apply hk hflat, φ.left_inv u.2]
  right_inv v := by
    apply Subtype.ext
    change coordProj hk (φ (φ.symm (coordIncl k n v))) = v
    rw [φ.right_inv v.2, coordProj_coordIncl]
  continuous_toFun := by
    refine Continuous.subtype_mk ((coordProj hk).continuous.comp
      (φ.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        fun u => show u.1.1 ∈ φ.source from u.2)) _
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk
      (φ.continuousOn_symm.comp_continuous ((coordIncl k n).continuous.comp continuous_subtype_val)
        fun v => show coordIncl k n v.1 ∈ φ.target from v.2) _) _

/-- A point of `Z` lies in the image of an open subset `B` of `U` exactly when it lies in `U` and
in `B`. -/
theorem mem_functor_obj_iff {U : Opens (TopCat.of Z)} (B : Opens (TopCat.of U)) (z : Z) :
    z ∈ U.isOpenEmbedding.functor.obj B ↔ ∃ hz : z ∈ U, (⟨z, hz⟩ : U) ∈ B := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, h, rfl⟩

variable (hk : k ≤ n)
  (hflat : φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0})

/-- The open set of `Z` matching an open subset `W'` of the model `modelTgt φ k`. -/
abbrev modelOpen (W' : Opens (TopCat.of (modelTgt φ k))) : Opens (TopCat.of Z) :=
  (modelSrc Z φ).isOpenEmbedding.functor.obj
    ((Opens.map (TopCat.isoOfHomeo (modelHomeo hk hflat)).hom).obj W')

/-- A point of `Z` lies in `modelOpen W'` exactly when it lies in `modelSrc Z φ` and `modelHomeo`
sends it into `W'`. -/
theorem mem_modelOpen_iff (W' : Opens (TopCat.of (modelTgt φ k))) (z : Z) :
    z ∈ modelOpen hk hflat W' ↔ ∃ hz : z ∈ modelSrc Z φ, modelHomeo hk hflat ⟨z, hz⟩ ∈ W' :=
  mem_functor_obj_iff _ z

/-- The point of `W'` matching a point of `modelOpen W'`. -/
def modelPt {W' : Opens (TopCat.of (modelTgt φ k))} (a : modelOpen hk hflat W') : W' :=
  ⟨modelHomeo hk hflat ⟨a.1, ((mem_modelOpen_iff hk hflat W' a.1).1 a.2).1⟩,
    ((mem_modelOpen_iff hk hflat W' a.1).1 a.2).2⟩

/-- The point of `modelOpen W'` matching a point of `W'`. -/
def modelPtInv {W' : Opens (TopCat.of (modelTgt φ k))} (w : W') : modelOpen hk hflat W' :=
  ⟨((modelHomeo hk hflat).symm w.1).1, (mem_modelOpen_iff hk hflat W' _).2
    ⟨((modelHomeo hk hflat).symm w.1).2, by
      have e : (⟨((modelHomeo hk hflat).symm w.1).1, ((modelHomeo hk hflat).symm w.1).2⟩ :
          modelSrc Z φ) = (modelHomeo hk hflat).symm w.1 := rfl
      rw [e, Homeomorph.apply_symm_apply]
      exact w.2⟩⟩

/-- `modelPt` is a left inverse of `modelPtInv`. -/
theorem modelPt_modelPtInv {W' : Opens (TopCat.of (modelTgt φ k))} (w : W') :
    modelPt hk hflat (modelPtInv hk hflat w) = w := by
  apply Subtype.ext
  change modelHomeo hk hflat ⟨((modelHomeo hk hflat).symm w.1).1, _⟩ = w.1
  exact (modelHomeo hk hflat).apply_symm_apply w.1

/-- `modelPtInv` is a left inverse of `modelPt`. -/
theorem modelPtInv_modelPt {W' : Opens (TopCat.of (modelTgt φ k))} (a : modelOpen hk hflat W') :
    modelPtInv hk hflat (modelPt hk hflat a) = a := by
  apply Subtype.ext
  change ((modelHomeo hk hflat).symm (modelHomeo hk hflat ⟨a.1, _⟩)).1 = a.1
  rw [Homeomorph.symm_apply_apply]

variable (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M)

include hφ in
/-- A function on `modelOpen W'` locally restricted from `𝒪_M`, read on `W'`, is holomorphic. -/
theorem contMDiff_comp_modelPtInv {W' : Opens (TopCat.of (modelTgt φ k))}
    (f : restrictedSubring n Z (modelOpen hk hflat W')) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin k)) 𝓘(ℂ) ∞
      (fun w : W' => f.1 (modelPtInv hk hflat w)) := by
  intro w
  obtain ⟨U, hwU, g, hg⟩ := f.2 (modelPtInv hk hflat w)
  let G : EuclideanSpace ℂ (Fin k) → ℂ := fun y =>
    Function.extend (Subtype.val : U → M) (fun q => g q) 0 (φ.symm (coordIncl k n y))
  let S := coordIncl k n ⁻¹' (φ.target ∩ φ.symm ⁻¹' U)
  have hSo : IsOpen S :=
    (φ.isOpen_inter_preimage_symm U.isOpen).preimage (coordIncl k n).continuous
  have hG : DifferentiableOn ℂ G S :=
    (differentiableOn_comp_symm_of_mem_maximalAtlas hφ U (fun q => g q)
      (show C^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin n)), U; 𝓘(ℂ), ℂ⟯ from g).contMDiff).comp
      (coordIncl k n).differentiableOn (fun y hy => hy)
  have hwS : ((w : modelTgt φ k) : EuclideanSpace ℂ (Fin k)) ∈ S := ⟨w.1.2, hwU⟩
  refine contMDiffAt_of_eventuallyEq_differentiableOn hSo hG w hwS ?_
  have hopen : IsOpen {w' : W' | ((w' : modelTgt φ k) : EuclideanSpace ℂ (Fin k)) ∈ S} :=
    hSo.preimage (continuous_subtype_val.comp continuous_subtype_val)
  filter_upwards [hopen.mem_nhds hwS] with w' hw'
  rw [hg (modelPtInv hk hflat w') hw'.2]
  exact (Subtype.val_injective.extend_apply (fun q : U => g q) 0 ⟨_, hw'.2⟩).symm

include hφ in
/-- A holomorphic function on `W'`, read on `modelOpen W'`, is locally restricted from `𝒪_M`. -/
theorem mem_restrictedSubring_comp_modelPt {W' : Opens (TopCat.of (modelTgt φ k))}
    (g : 𝒪[k, modelTgt φ k].presheaf.obj (op W')) :
    (fun a : modelOpen hk hflat W' => g (modelPt hk hflat a)) ∈
      restrictedSubring n Z (modelOpen hk hflat W') := by
  intro a
  let B := Subtype.val '' (W' : Set (modelTgt φ k))
  have hinj : Function.Injective (fun w : W' => (w : modelTgt φ k).1) :=
    Subtype.val_injective.comp Subtype.val_injective
  let G := Function.extend (fun w : W' => (w : modelTgt φ k).1) (fun w => g w) 0
  have hG : DifferentiableOn ℂ G B := differentiableOn_extend_nested _
    (show C^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin k)), W'; 𝓘(ℂ), ℂ⟯ from g).contMDiff
  have hBo : IsOpen (coordProj hk ⁻¹' B) :=
    (isOpen_image_nested W').preimage (coordProj hk).continuous
  let U : Opens M := ⟨φ.source ∩ φ ⁻¹' (coordProj hk ⁻¹' B),
    φ.continuousOn.isOpen_inter_preimage φ.open_source hBo⟩
  let g' : 𝒪[n, M].presheaf.obj (op U) :=
    (⟨fun q => G (coordProj hk (φ q)), contMDiff_comp_of_mem_maximalAtlas hφ U (fun q hq => hq.1)
      hBo (G ∘ coordProj hk) (hG.comp (coordProj hk).differentiableOn fun y hy => hy)
      (fun q hq => hq.2)⟩ : C^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin n)), U; 𝓘(ℂ), ℂ⟯)
  have haS : ((a : Z) : M) ∈ U :=
    ⟨((mem_modelOpen_iff hk hflat W' a.1).1 a.2).1,
      ⟨(modelPt hk hflat a).1, (modelPt hk hflat a).2, rfl⟩⟩
  refine ⟨U, haS, g', fun v hv => ?_⟩
  exact (hinj.extend_apply (fun w => g w) 0 (modelPt hk hflat v)).symm

/-- Functions on `modelOpen W'` locally restricted from `𝒪_M` are the holomorphic functions
on `W'`. -/
def modelRingEquiv (W' : Opens (TopCat.of (modelTgt φ k))) :
    restrictedSubring n Z (modelOpen hk hflat W') ≃+* 𝒪[k, modelTgt φ k].presheaf.obj (op W') where
  toFun f := (⟨fun w => f.1 (modelPtInv hk hflat w), contMDiff_comp_modelPtInv hk hflat hφ f⟩ :
    C^∞⟮𝓘(ℂ, EuclideanSpace ℂ (Fin k)), W'; 𝓘(ℂ), ℂ⟯)
  invFun g := ⟨fun a => g (modelPt hk hflat a), mem_restrictedSubring_comp_modelPt hk hflat hφ g⟩
  left_inv f := Subtype.ext (funext fun a => by
    change f.1 (modelPtInv hk hflat (modelPt hk hflat a)) = f.1 a
    rw [modelPtInv_modelPt])
  right_inv g := ContMDiffMap.ext fun w => by
    change g (modelPt hk hflat (modelPtInv hk hflat w)) = g w
    rw [modelPt_modelPtInv]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable {hk hflat hφ} in
/-- For closed `Z`, the comparison `𝒪_Z ⟶ 𝒪'_Z` is an isomorphism of presheaves. -/
theorem isIso_structureSheafToRestricted_hom (hZ : IsClosed Z) :
    IsIso (structureSheafToRestricted n Z).hom := by
  haveI := isIso_structureSheafToRestricted (n := n) Z hZ
  first
  | exact (TopCat.Sheaf.forget CommRingCat.{0} _).map_isIso (structureSheafToRestricted n Z)
  | exact Functor.map_isIso (sheafToPresheaf _ _) (structureSheafToRestricted n Z)
  | exact (ObjectProperty.ι _).map_isIso (structureSheafToRestricted n Z)

variable {hk hflat hφ} in
/-- The structure sheaf `𝒪_Z` is the sheaf `𝒪'_Z` of functions locally restricted from `𝒪_M`. -/
def structurePresheafIso (hZ : IsClosed Z) :
    ((TopCat.Sheaf.pullback CommRingCat.{0} (submanifoldInclusion Z)).obj
      (quotientVanishingIdealSheaf n Z)).presheaf ≅ (restrictedSheaf n Z).presheaf :=
  @asIso _ _ _ _ (structureSheafToRestricted n Z).hom
    (isIso_structureSheafToRestricted_hom (n := n) (Z := Z) hZ)

/-- The presheaf part of the local model. -/
def modelAlpha (hZ : IsClosed Z) :
    (TopCat.Presheaf.pushforward CommRingCat.{0} (TopCat.isoOfHomeo (modelHomeo hk hflat)).hom).obj
      ((modelSrc Z φ).isOpenEmbedding.functor.op ⋙
        ((TopCat.Sheaf.pullback CommRingCat.{0} (submanifoldInclusion Z)).obj
          (quotientVanishingIdealSheaf n Z)).presheaf) ≅
      𝒪[k, modelTgt φ k].presheaf :=
  NatIso.ofComponents (fun W' => (structurePresheafIso hZ).app (op (modelOpen hk hflat W'.unop)) ≪≫
      (modelRingEquiv hk hflat hφ W'.unop).toCommRingCatIso)
    (fun {W₁ W₂} f => by
      simp only [Iso.trans_hom, Iso.app_hom]
      let str : ((TopCat.Sheaf.pullback CommRingCat.{0} (submanifoldInclusion Z)).obj
          (quotientVanishingIdealSheaf n Z)).presheaf ⟶ (restrictedSheaf n Z).presheaf :=
        (structureSheafToRestricted n Z).hom
      change _ ≫ str.app _ ≫ _ = (str.app _ ≫ _) ≫ _
      rw [← Category.assoc]
      erw [str.naturality]
      rw [Category.assoc, Category.assoc]
      congr 1)

/-- The local model of a closed submanifold in a flattening chart. -/
def modelIso (hZ : IsClosed Z) :
    SheafedSpace.restrict (C := CommRingCat.{0})
        { carrier := TopCat.of Z, presheaf := (submanifoldStructureSheaf n Z).presheaf
          IsSheaf := (submanifoldStructureSheaf n Z).property } (modelSrc Z φ).isOpenEmbedding ≅
      { carrier := TopCat.of (modelTgt φ k), presheaf := 𝒪[k, modelTgt φ k].presheaf,
        IsSheaf := 𝒪[k, modelTgt φ k].property } :=
  SheafedSpace.isoMk (PresheafedSpace.isoOfComponents (TopCat.isoOfHomeo (modelHomeo hk hflat))
    (modelAlpha hk hflat hφ hZ))

omit hk hflat hφ in
/-- **Part (4b)**: a closed complex submanifold, with its structure sheaf, is locally isomorphic
to an open subset of some `ℂᵏ` with its holomorphic functions. -/
theorem exists_local_model (hZ : IsClosedComplexSubmanifold n Z) (z : Z) :
    ∃ (U : Opens (TopCat.of Z)) (_ : z ∈ U) (k : ℕ) (V : Opens (EuclideanSpace ℂ (Fin k))),
      Nonempty (SheafedSpace.restrict (C := CommRingCat.{0})
          { carrier := TopCat.of Z, presheaf := (submanifoldStructureSheaf n Z).presheaf
            IsSheaf := (submanifoldStructureSheaf n Z).property } U.isOpenEmbedding ≅
        { carrier := TopCat.of V, presheaf := 𝒪[k, V].presheaf, IsSheaf := 𝒪[k, V].property }) := by
  obtain ⟨φ, hφ, hzφ, k, hflat⟩ := hZ.2 z.1 z.2
  have hflat' : φ '' (Z ∩ φ.source) =
      φ.target ∩ {y | ∀ i : Fin n, min k n ≤ (i : ℕ) → y i = 0} := by
    rw [hflat]
    congr 1
    ext y
    refine forall_congr' fun i => ⟨fun h hi => h (by omega), fun h hi => h (by omega)⟩
  exact ⟨modelSrc Z φ, hzφ, min k n, modelTgt φ (min k n),
    ⟨modelIso (min_le_right k n) hflat' hφ hZ.1⟩⟩

end LocalModel

section SubmanifoldModules

open Topology

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] {Z : Set M}

variable (n Z) in
/-- The composite `𝒪_M ⟶ 𝒪_M / ℐ_Z ⟶ ι_* 𝒪_Z` of sheaves of commutative rings. -/
abbrev toStructure : 𝒪[n, M] ⟶ (TopCat.Sheaf.pushforward CommRingCat.{0}
    (submanifoldInclusion Z)).obj (submanifoldStructureSheaf n Z) :=
  toQuotientVanishingIdealSheaf n Z ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0}
    (submanifoldInclusion Z)).unit.app (quotientVanishingIdealSheaf n Z)

/-- The map `𝒪_M ⟶ 𝒪_M / ℐ_Z` of sheaves is the quotient map of presheaves followed by
sheafification. -/
theorem toQuotientVanishingIdealSheaf_hom :
    (toQuotientVanishingIdealSheaf n Z).hom =
      toQuotientVanishingIdealPresheaf n Z ≫ CategoryTheory.toSheafify _ _ :=
  (fullyFaithfulSheafToPresheaf _ _).map_preimage _

/-- Read in `𝒪'_Z`, the map `𝒪_M ⟶ ι_* 𝒪_Z` is the restriction of functions to `Z`. -/
theorem structureSheafToRestricted_toStructure (U : Opens (TopCat.of M))
    (g : 𝒪[n, M].presheaf.obj (op U)) :
    (structureSheafToRestricted n Z).hom.app (op ((Opens.map (submanifoldInclusion Z)).obj U))
      ((toStructure n Z).hom.app (op U) g) = restrictHom n Z U g := by
  let q := (toQuotientVanishingIdealSheaf n Z).hom.app (op U) g
  have h1 : (structureSheafToRestricted n Z).hom.app
      (op ((Opens.map (submanifoldInclusion Z)).obj U))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0}
        (submanifoldInclusion Z)).unit.app (quotientVanishingIdealSheaf n Z)).hom.app (op U) q) =
      (quotientSheafToRestricted n Z).hom.app (op U) q :=
    congrArg (fun f => f.hom.app (op U) q) (unit_comp_structureSheafToRestricted (n := n) Z)
  have h2 : (quotientSheafToRestricted n Z).hom.app (op U)
      ((CategoryTheory.toSheafify _ (quotientVanishingIdealPresheaf n Z)).app (op U)
        (Ideal.Quotient.mk _ g)) =
      (quotientToRestricted n Z).app (op U) (Ideal.Quotient.mk _ g) :=
    congrArg (fun f => f.app (op U) (Ideal.Quotient.mk _ g))
      (toSheafify_quotientSheafToRestricted (n := n) Z)
  have h3 : q = (CategoryTheory.toSheafify _ (quotientVanishingIdealPresheaf n Z)).app (op U)
      (Ideal.Quotient.mk _ g) :=
    congrArg (fun f => f.app (op U) g) (toQuotientVanishingIdealSheaf_hom (n := n) (Z := Z))
  refine h1.trans ?_
  rw [h3, h2]
  rfl

variable (n Z) in
/-- The comparison `𝒪_Z ⟶ 𝒪'_Z` as a morphism of presheaves of rings. -/
abbrev strHom : (submanifoldStructureSheaf n Z).presheaf ⟶
    (restrictedSheaf n Z).presheaf :=
  (structureSheafToRestricted n Z).hom

/-- For closed `Z`, the comparison `𝒪_Z ⟶ 𝒪'_Z` is injective on sections over every open set. -/
theorem strHom_injective (hZc : IsClosed Z) (W : Opens (TopCat.of Z)) :
    Function.Injective ((strHom n Z).app (op W)) := by
  have hI : IsIso (strHom n Z) := isIso_structureSheafToRestricted_hom (n := n) (Z := Z) hZc
  haveI : IsIso ((strHom n Z).app (op W)) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ (strHom n Z) hI (op W)
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- The comparison `𝒪_Z ⟶ 𝒪'_Z` commutes with restriction, evaluated at a point. -/
theorem strHom_map_apply {W W' : Opens (TopCat.of Z)} (h : W' ≤ W)
    (c : (submanifoldStructureSheaf n Z).presheaf.obj (op W)) (v : W') :
    ((strHom n Z).app (op W') ((submanifoldStructureSheaf n Z).presheaf.map (homOfLE h).op c)).1 v =
      ((strHom n Z).app (op W) c).1 ⟨v.1, h v.2⟩ := by
  rw [NatTrans.naturality_apply]
  rfl

/-- **Lifting.** A section of `𝒪_Z` is, near any point, the image of a holomorphic function
on an open set of `M`. -/
theorem exists_toStructure_eq (hZc : IsClosed Z) {W : Opens (TopCat.of Z)}
    (c : (submanifoldStructureSheaf n Z).presheaf.obj (op W)) {z : Z} (hz : z ∈ W) :
    ∃ (U : Opens (TopCat.of M)) (_ : z.1 ∈ U)
      (hUW : (Opens.map (submanifoldInclusion Z)).obj U ≤ W) (g : 𝒪[n, M].presheaf.obj (op U)),
      (toStructure n Z).hom.app (op U) g =
        (submanifoldStructureSheaf n Z).presheaf.map (homOfLE hUW).op c := by
  obtain ⟨U0, hz0, g0, hg0⟩ := ((strHom n Z).app (op W) c).2 ⟨z, hz⟩
  obtain ⟨t, ht, hWt⟩ := isOpen_induced_iff.1 W.isOpen
  let U : Opens (TopCat.of M) := U0 ⊓ ⟨t, ht⟩
  have hUW : (Opens.map (submanifoldInclusion Z)).obj U ≤ W := fun v hv => by
    have : v ∈ Subtype.val ⁻¹' t := hv.2
    rw [hWt] at this
    exact this
  have hzt : z.1 ∈ t := by
    have : z ∈ (W : Set Z) := hz
    rw [← hWt] at this
    exact this
  refine ⟨U, ⟨hz0, hzt⟩, hUW, 𝒪[n, M].presheaf.map (homOfLE inf_le_left).op g0, ?_⟩
  apply strHom_injective hZc
  refine (structureSheafToRestricted_toStructure U _).trans (Subtype.ext (funext fun v => ?_))
  rw [strHom_map_apply]
  exact (hg0 ⟨v.1, hUW v.2⟩ (v.2).1).symm

/-- A holomorphic function has zero image in `ι_* 𝒪_Z` exactly when it vanishes on `Z`. -/
theorem toStructure_eq_zero_iff (hZc : IsClosed Z) {U : Opens (TopCat.of M)}
    (g : 𝒪[n, M].presheaf.obj (op U)) :
    (toStructure n Z).hom.app (op U) g = 0 ↔ g ∈ vanishingIdeal n Z U := by
  refine ⟨fun h v hv => ?_, fun h => ?_⟩
  · have e := structureSheafToRestricted_toStructure (n := n) (Z := Z) U g
    rw [h] at e
    exact (congrArg (fun c => c.1 ⟨⟨v.1, hv⟩, v.2⟩) ((map_zero _).symm.trans e)).symm
  · apply strHom_injective hZc
    refine (structureSheafToRestricted_toStructure U g).trans ?_
    exact (Subtype.ext (funext fun v => h ⟨v.1.1, v.2⟩ v.1.2)).trans (map_zero _).symm

/-- Preimage of open sets along `Z ⊆ M` is continuous for the open-cover topologies. -/
theorem isContinuous_opensMap_submanifoldInclusion :
    (Opens.map (submanifoldInclusion Z)).IsContinuous (Opens.grothendieckTopology (TopCat.of M))
      (Opens.grothendieckTopology (TopCat.of Z)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
    (coverPreserving_opens_map _)

attribute [local instance] isContinuous_opensMap_submanifoldInclusion

variable (n Z) in
/-- The structure sheaf `𝒪_Z`, as a sheaf of rings. -/
abbrev OZ : Sheaf (Opens.grothendieckTopology (TopCat.of Z)) RingCat.{0} :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{0})).obj (submanifoldStructureSheaf n Z)

variable (n Z) in
/-- The morphism of sheaves of rings `𝒪_M ⟶ ι_* 𝒪_Z`. -/
noncomputable abbrev φZ : holomorphicRingCatSheaf n M ⟶
    ((Opens.map (submanifoldInclusion Z)).sheafPushforwardContinuous RingCat.{0}
      (Opens.grothendieckTopology (TopCat.of M)) (Opens.grothendieckTopology (TopCat.of Z))).obj
      (OZ n Z) :=
  { hom := Functor.whiskerRight (toStructure n Z).hom (forget₂ CommRingCat RingCat.{0}) }

variable (n Z) in
/-- The image in `𝒪_Z` of a holomorphic function on an open set of `M`. -/
abbrev tS {U : Opens (TopCat.of M)} (a : (holSheaf n M).obj.obj (op U)) :
    (OZ n Z).obj.obj (op ((Opens.map (submanifoldInclusion Z)).obj U)) :=
  (toStructure n Z).hom.app (op U) a

/-- The direct image `ι_* S` of a sheaf of `𝒪_Z`-modules. -/
noncomputable abbrev pushZ (S : SheafOfModules.{0} (OZ n Z)) :
    SheafOfModules.{0} (holomorphicRingCatSheaf n M) :=
  (SheafOfModules.pushforward.{0} (φZ n Z)).obj S

/-- A holomorphic function `a` on `U` acts on `ι_* S` over `U` through its image in `𝒪_Z` over
`Z ∩ U`. -/
theorem pushZ_smul (S : SheafOfModules.{0} (OZ n Z)) {U : Opens (TopCat.of M)}
    (a : (holSheaf n M).obj.obj (op U)) (t : (pushZ S).val.obj (op U)) :
    a • t = (show S.val.obj (op ((Opens.map (submanifoldInclusion Z)).obj U)) from
      (show (OZ n Z).obj.obj (op ((Opens.map (submanifoldInclusion Z)).obj U)) from
        (toStructure n Z).hom.app (op U) a) • (show S.val.obj _ from t)) := rfl

/-- Restriction in `ι_* S` from `U` to `U'` is restriction in `S` from `Z ∩ U` to `Z ∩ U'`. -/
theorem pushZ_map (S : SheafOfModules.{0} (OZ n Z)) {U U' : Opens (TopCat.of M)}
    (h : U' ≤ U) (t : (pushZ S).val.obj (op U)) :
    resM (pushZ S) h t = (show (pushZ S).val.obj (op U') from
      resM S ((Opens.map (submanifoldInclusion Z)).monotone h) t) := rfl

/-- The map `𝒪_M ⟶ ι_* 𝒪_Z` commutes with restriction of sections. -/
theorem toStructure_resA {U U' : Opens (TopCat.of M)} (h : U' ≤ U)
    (g : (holSheaf n M).obj.obj (op U)) :
    (toStructure n Z).hom.app (op U') (resA h g) =
      resA (A := OZ n Z) ((Opens.map (submanifoldInclusion Z)).monotone h)
        ((toStructure n Z).hom.app (op U) g) :=
  NatTrans.naturality_apply (toStructure n Z).hom (homOfLE h).op g

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- Every open set of `Z` is the trace of an open set of `M`. -/
theorem exists_opens_map_eq (W : Opens (TopCat.of Z)) :
    ∃ W' : Opens (TopCat.of M), (Opens.map (submanifoldInclusion Z)).obj W' = W := by
  obtain ⟨t, ht, hWt⟩ := isOpen_induced_iff.1 W.isOpen
  exact ⟨⟨t, ht⟩, Opens.ext hWt⟩

/-- Finitely many sections of `𝒪_Z` lift, near a point, to holomorphic functions on a common
open set of `M`. -/
theorem exists_toStructure_eq_fun (hZc : IsClosed Z) {W : Opens (TopCat.of Z)}
    {ι' : Type} [Finite ι'] (c : ι' → (OZ n Z).obj.obj (op W)) {z : Z} (hz : z ∈ W) :
    ∃ (U : Opens (TopCat.of M)) (_ : z.1 ∈ U)
      (hUW : (Opens.map (submanifoldInclusion Z)).obj U ≤ W)
      (g : ι' → (holSheaf n M).obj.obj (op U)),
      ∀ k, (toStructure n Z).hom.app (op U) (g k) = resA (A := OZ n Z) hUW (c k) := by
  choose U hzU hUW g hg using fun k => exists_toStructure_eq (n := n) hZc (c k) hz
  obtain ⟨V, hzV, hV⟩ := exists_le_of_forall_mem U hzU
  obtain ⟨W', hW'⟩ := exists_opens_map_eq W
  have hzW' : z.1 ∈ W' := by
    have : z ∈ (Opens.map (submanifoldInclusion Z)).obj W' := hW' ▸ hz
    exact this
  refine ⟨V ⊓ W', ⟨hzV, hzW'⟩, ((Opens.map (submanifoldInclusion Z)).monotone inf_le_right).trans
    hW'.le, fun k => resA (inf_le_left.trans (hV k)) (g k), fun k => ?_⟩
  exact (toStructure_resA _ _).trans ((congrArg (resA (A := OZ n Z) _) (hg k)).trans
    (resA_resA (A := OZ n Z) _ _ _))

/-- Sections of a sheaf of modules over an open set without points vanish. -/
theorem eq_zero_of_forall_notMem {T : TopCat.{0}}
    {A : Sheaf (Opens.grothendieckTopology T) RingCat.{0}} (S : SheafOfModules.{0} A)
    {W : Opens T} (h : ∀ y, y ∉ W) (t : S.val.obj (op W)) : t = 0 :=
  eq_zero_of_locally_eq_zero S t fun y hy => absurd hy (h y)

/-- The direct image of a sheaf of `𝒪_Z`-modules of finite type is of finite type. -/
theorem finGen_pushZ (hZc : IsClosed Z) (S : SheafOfModules.{0} (OZ n Z))
    (hS : FinGen S) : FinGen (A := holSheaf n M) (pushZ S) := by
  intro x
  by_cases hx : x ∈ Z
  · obtain ⟨W, hzW, m, g, hg⟩ := hS ⟨x, hx⟩
    obtain ⟨W', hW'⟩ := exists_opens_map_eq W
    have hxW' : x ∈ W' := by
      have : (⟨x, hx⟩ : Z) ∈ (Opens.map (submanifoldInclusion Z)).obj W' := hW' ▸ hzW
      exact this
    refine ⟨W', hxW', m, fun k => (show (pushZ S).val.obj (op W') from resM S hW'.le (g k)), ?_⟩
    refine locallyGenerates_of_nhds _ fun U hU t y hy => ?_
    by_cases hyZ : y ∈ Z
    · have hyU : (⟨y, hyZ⟩ : Z) ∈ (Opens.map (submanifoldInclusion Z)).obj U := hy
      have hUW : (Opens.map (submanifoldInclusion Z)).obj U ≤ W :=
        ((Opens.map (submanifoldInclusion Z)).monotone hU).trans hW'.le
      obtain ⟨U1, h1, hy1, c, hc⟩ := hg.exists_nhds hUW (show S.val.obj _ from t) hyU
      obtain ⟨U2, hy2, h2, a, ha⟩ := exists_toStructure_eq_fun (n := n) hZc c hy1
      have hh : (Opens.map (submanifoldInclusion Z)).obj (U2 ⊓ U) ≤ U1 :=
        ((Opens.map (submanifoldInclusion Z)).monotone inf_le_left).trans h2
      refine ⟨U2 ⊓ U, inf_le_right, ⟨hy2, hy⟩, fun k => resA inf_le_left (a k), ?_⟩
      have key := congrArg (resM S hh) hc
      rw [resM_resM, resM_sum_smul] at key
      simp only [resM_resM] at key
      refine key.trans (Finset.sum_congr rfl fun k _ => ?_)
      rw [pushZ_smul, pushZ_map, resM_resM]
      congr 1
      exact ((toStructure_resA _ _).trans ((congrArg (resA (A := OZ n Z) _) (ha k)).trans
        (resA_resA (A := OZ n Z) _ _ _))).symm
    · refine ⟨U ⊓ ⟨Zᶜ, hZc.isOpen_compl⟩, inf_le_left, ⟨hy, hyZ⟩, 0, ?_⟩
      have hW0 : ∀ z : Z, z ∉ (Opens.map (submanifoldInclusion Z)).obj
          (U ⊓ ⟨Zᶜ, hZc.isOpen_compl⟩) := fun z hz => hz.2 z.2
      exact (eq_zero_of_forall_notMem S hW0 _).trans (eq_zero_of_forall_notMem S hW0 _).symm
  · refine ⟨⟨Zᶜ, hZc.isOpen_compl⟩, hx, 0, Fin.elim0,
      locallyGenerates_of_nhds _ fun U hU t y hy => ⟨U, le_rfl, hy, Fin.elim0, ?_⟩⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact eq_zero_of_forall_notMem S (fun z hz => hU hz z.2) _

/-- Relations among sections of `ι_* S` off `Z`: every vector of functions is a relation. -/
theorem relFin_pushZ_of_notMem (hZc : IsClosed Z) (S : SheafOfModules.{0} (OZ n Z))
    (V : Opens (TopCat.of M)) (p : ℕ) (f : Fin p → (pushZ S).val.obj (op V)) (x : M)
    (hxV : x ∈ V) (hx : x ∉ Z) :
    ∃ (W : Opens (TopCat.of M)) (hWV : W ≤ V), x ∈ W ∧
      ∃ (s : ℕ) (r : Fin s → Fin p → (holSheaf n M).obj.obj (op W)),
      (∀ k, ∑ j, r k j • resM (pushZ S) hWV (f j) = 0) ∧
      ∀ (U : Opens (TopCat.of M)) (hUW : U ≤ W) (a : Fin p → (holSheaf n M).obj.obj (op U)),
        ∑ j, a j • resM (pushZ S) (hUW.trans hWV) (f j) = 0 → ∀ y ∈ U,
        ∃ (U' : Opens (TopCat.of M)) (h : U' ≤ U), y ∈ U' ∧
          ∃ c : Fin s → (holSheaf n M).obj.obj (op U'),
          ∀ j, resA h (a j) = ∑ k, c k * resA (h.trans hUW) (r k j) := by
  classical
  have hW0 : ∀ z : Z, z ∉ (Opens.map (submanifoldInclusion Z)).obj
      (V ⊓ ⟨Zᶜ, hZc.isOpen_compl⟩) := fun z hz => hz.2 z.2
  refine ⟨V ⊓ ⟨Zᶜ, hZc.isOpen_compl⟩, inf_le_left, ⟨hxV, hx⟩, p,
    fun k j => if k = j then 1 else 0, fun k => eq_zero_of_forall_notMem S hW0 _,
    fun U hUW a _ y hy => ⟨U, le_rfl, hy, fun k => resA le_rfl (a k), fun j => ?_⟩⟩
  have : ∀ k, resA (A := holSheaf n M) ((le_rfl : U ≤ U).trans hUW)
      (if k = j then (1 : (holSheaf n M).obj.obj (op (V ⊓ ⟨Zᶜ, hZc.isOpen_compl⟩))) else 0) =
        if k = j then 1 else 0 := by
    intro k; split_ifs <;> simp [resA, map_one, map_zero]
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The direct image of a coherent `𝒪_Z`-module has locally finitely generated relations. -/
theorem relFin_pushZ (hZ : IsClosedComplexSubmanifold n Z) (S : SheafOfModules.{0} (OZ n Z))
    (hS : RelFin S) : RelFin (A := holSheaf n M) (pushZ S) := by
  classical
  intro V p f x hxV
  by_cases hx : x ∉ Z
  · exact relFin_pushZ_of_notMem hZ.1 S V p f x hxV hx
  rw [not_not] at hx
  have hZc := hZ.1
  obtain ⟨W1, hW1V, hzW1, s, r, hr, hgen⟩ :=
    hS _ p (fun j => show S.val.obj _ from f j) ⟨x, hx⟩ hxV
  obtain ⟨U1, hxU1, hU1W1, rt, hrt⟩ :=
    exists_toStructure_eq_fun (n := n) hZc (fun q : Fin s × Fin p => r q.1 q.2) hzW1
  obtain ⟨φ, hφ, hxφ, k, hflat⟩ := hZ.2 x hx
  let W : Opens (TopCat.of M) := U1 ⊓ V ⊓ chartSrc φ
  have hWU1 : W ≤ U1 := inf_le_left.trans inf_le_left
  have hWV : W ≤ V := inf_le_left.trans inf_le_right
  have hWφ : W ≤ chartSrc φ := inf_le_right
  have hxW : x ∈ W := ⟨⟨hxU1, hxV⟩, hxφ⟩
  let Q := Fin s ⊕ ({i : Fin n // k ≤ (i : ℕ)} × Fin p)
  let e := Fintype.equivFin Q
  let R : Q → Fin p → (holSheaf n M).obj.obj (op W) := fun q j => Sum.elim
    (fun l => resA hWU1 (rt (l, j)))
    (fun ij : {i : Fin n // k ≤ (i : ℕ)} × Fin p =>
      if ij.2 = j then resA hWφ (chartCoord hφ ij.1.1) else 0) q
  refine ⟨W, hWV, hxW, Fintype.card Q, fun l j => R (e.symm l) j, ?_, ?_⟩
  · intro l
    rcases hq : e.symm l with l0 | ⟨i, j'⟩
    · simp only [R, hq, Sum.elim_inl]
      have key := congrArg (resM S (((Opens.map (submanifoldInclusion Z)).monotone hWU1).trans
        hU1W1)) (hr l0)
      rw [resM_sum_smul, resM_zero] at key
      simp only [resM_resM] at key
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) key
      refine (pushZ_smul S _ _).trans ?_
      exact congrArg₂ (fun (a : (OZ n Z).obj.obj (op _)) (b : S.val.obj (op _)) => a • b)
        ((toStructure_resA _ _).trans ((congrArg (resA (A := OZ n Z) _) (hrt (l0, j))).trans
          (resA_resA (A := OZ n Z) _ _ _)))
        (resM_resM S _ _ _).symm
    · simp only [R, hq, Sum.elim_inr, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
      have h0 : (toStructure n Z).hom.app (op W) (resA hWφ (chartCoord hφ i.1)) = 0 :=
        (toStructure_eq_zero_iff hZc _).2 fun v hv =>
          apply_eq_zero_of_flat hflat hv (hWφ v.2) i.1 i.2
      refine (pushZ_smul S _ _).trans ?_
      refine (congrArg (fun (a : (OZ n Z).obj.obj (op _)) =>
        a • (show S.val.obj (op ((Opens.map (submanifoldInclusion Z)).obj W)) from
          resM (pushZ S) hWV (f j'))) h0).trans ?_
      exact zero_smul _ _
  · intro U hUW a ha y hy
    have hU2 : ∃ (U2 : Opens (TopCat.of M)) (h2 : U2 ≤ U), y ∈ U2 ∧
        ∃ ct : Fin s → (holSheaf n M).obj.obj (op U2), ∀ j,
          resA h2 (a j) - ∑ l, ct l * resA (h2.trans (hUW.trans hWU1)) (rt (l, j)) ∈
            vanishingIdeal n Z U2 := by
      by_cases hyZ : y ∈ Z
      · have hUW1 : (Opens.map (submanifoldInclusion Z)).obj U ≤ W1 :=
          ((Opens.map (submanifoldInclusion Z)).monotone (hUW.trans hWU1)).trans hU1W1
        have ha' : ∑ j, tS n Z (a j) • resM S (hUW1.trans hW1V) (f j) = 0 :=
          Eq.trans (Finset.sum_congr rfl fun j _ => (pushZ_smul S _ _).symm) ha
        obtain ⟨U1', h1', hy1', c, hc⟩ :=
          hgen _ hUW1 (fun j => tS n Z (a j)) ha' ⟨y, hyZ⟩ hy
        obtain ⟨U3, hy3, h3, ct, hct⟩ := exists_toStructure_eq_fun (n := n) hZc c hy1'
        refine ⟨U3 ⊓ U, inf_le_right, ⟨hy3, hy⟩, fun l => resA inf_le_left (ct l), fun j => ?_⟩
        refine (toStructure_eq_zero_iff hZc _).1 ?_
        have hh : (Opens.map (submanifoldInclusion Z)).obj (U3 ⊓ U) ≤ U1' :=
          ((Opens.map (submanifoldInclusion Z)).monotone inf_le_left).trans h3
        have e1 : tS n Z (resA inf_le_right (a j)) =
            resA (A := OZ n Z) (hh.trans h1') ((toStructure n Z).hom.app (op U) (a j)) :=
          toStructure_resA _ _
        have e2 : ∀ l, tS n Z (resA (inf_le_left : U3 ⊓ U ≤ U3) (ct l)) =
            resA (A := OZ n Z) hh (c l) := fun l =>
          (toStructure_resA _ _).trans ((congrArg (resA (A := OZ n Z) _) (hct l)).trans
            (resA_resA (A := OZ n Z) _ _ _))
        have e3 : ∀ l, tS n Z
            (resA ((inf_le_right : U3 ⊓ U ≤ U).trans (hUW.trans hWU1)) (rt (l, j))) =
            resA (A := OZ n Z) (hh.trans (h1'.trans hUW1)) (r l j) := fun l =>
          (toStructure_resA _ _).trans ((congrArg (resA (A := OZ n Z) _) (hrt (l, j))).trans
            (resA_resA (A := OZ n Z) _ _ _))
        have key := congrArg (resA (A := OZ n Z) hh) (hc j)
        rw [resA_resA, resA_sum] at key
        simp only [resA_mul, resA_resA] at key
        refine (map_sub _ _ _).trans (sub_eq_zero.2 ?_)
        refine Eq.trans ?_ (map_sum _ _ _).symm
        refine e1.trans (key.trans (Finset.sum_congr rfl fun l _ => ?_))
        exact (resA_mul (A := OZ n Z) _ _ _).trans ((congrArg₂ (· * ·) (e2 l).symm
          ((resA_resA (A := OZ n Z) _ _ _).trans (e3 l).symm)).trans (map_mul _ _ _).symm)
      · exact ⟨U ⊓ ⟨Zᶜ, hZc.isOpen_compl⟩, inf_le_left, ⟨hy, hyZ⟩, 0, fun j v hv => absurd hv v.2.2⟩
    obtain ⟨U2, h2, hy2, ct, hct⟩ := hU2
    have hU2φ : U2 ≤ chartSrc φ := h2.trans (hUW.trans hWφ)
    choose U4 h4 hy4 d hd using fun j =>
      exists_coord_gen hφ hflat hU2φ
        (resA h2 (a j) - ∑ l, ct l * resA (h2.trans (hUW.trans hWU1)) (rt (l, j)))
        (fun v hv => hct j v hv) hy2
    obtain ⟨U5', hy5', h5'⟩ := exists_le_of_forall_mem U4 hy4
    have h52 : U5' ⊓ U2 ≤ U2 := inf_le_right
    let C' : Q → (holSheaf n M).obj.obj (op (U5' ⊓ U2)) := Sum.elim (fun l => resA h52 (ct l))
      (fun ij => resA (inf_le_left.trans (h5' ij.2)) (d ij.2 ij.1))
    refine ⟨U5' ⊓ U2, h52.trans h2, ⟨hy5', hy2⟩, fun l => C' (e.symm l), fun j => ?_⟩
    rw [e.symm.sum_comp (fun q => C' q * resA _ (R q j)), Fintype.sum_sum_type,
      Fintype.sum_prod_type]
    simp only [C', R, Sum.elim_inl, Sum.elim_inr]
    have hite : ∀ (i : {i : Fin n // k ≤ (i : ℕ)}) (j' : Fin p),
        resA (A := holSheaf n M) (((h52.trans h2).trans hUW))
          (if j' = j then resA hWφ (chartCoord hφ i.1) else 0) =
        if j' = j then resA (((h52.trans h2).trans hUW).trans hWφ) (chartCoord hφ i.1) else 0 := by
      intro i j'
      split_ifs
      · exact resA_resA _ _ _
      · exact map_zero _
    simp only [hite, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have key := congrArg (resA (A := holSheaf n M) (inf_le_left.trans (h5' j) :
      U5' ⊓ U2 ≤ U4 j)) (hd j)
    rw [resA_resA] at key
    have k1 : resA (A := holSheaf n M) ((h52.trans h2)) (a j) -
        ∑ l, resA h52 (ct l) * resA (((h52.trans h2).trans hUW)) (resA hWU1 (rt (l, j))) =
        ∑ i, resA (A := holSheaf n M) (inf_le_left.trans (h5' j)) (d j i) *
          resA (((h52.trans h2).trans hUW).trans hWφ) (chartCoord hφ i.1) := by
      refine Eq.trans ?_ (key.trans ((resA_sum _ _).trans
        (Finset.sum_congr rfl fun i _ => (resA_mul _ _ _).trans ?_)))
      · rw [resA_sub, resA_resA, resA_sum]
        congr 1
      · first | rfl | rw [resA_resA]
    rw [← k1]
    exact (add_sub_cancel _ _).symm

/-- **Part (4c)**: the direct image of a coherent `𝒪_Z`-module is a coherent `𝒪_M`-module. -/
theorem isCoherentModule_pushZ (hZ : IsClosedComplexSubmanifold n Z)
    (S : SheafOfModules.{0} (OZ n Z)) (hS : IsCoherentModule S) : IsCoherentModule (pushZ S) :=
  isCoherentModule_of_finGen_of_relFin (A := holSheaf n M)
    (finGen_pushZ hZ.1 S ((isFiniteType_iff_finGen S).1 hS.1))
    (relFin_pushZ hZ S (relFin_of_isCoherentModule hS))

/-! ### The converse: modules killed by `ℐ_Z` -/

/-- Sections of `𝒪_Z` over an open set without points are trivial. -/
theorem subsingleton_OZ (hZc : IsClosed Z) {W : Opens (TopCat.of Z)}
    (h : ∀ z, z ∉ W) : Subsingleton ((OZ n Z).obj.obj (op W)) :=
  ⟨fun a b => strHom_injective (n := n) hZc W
    (Subtype.ext (funext fun w => absurd w.2 (h w)))⟩

variable (n Z) in
/-- The presheaf of rings `𝒪_M / ℐ_Z`, valued in rings. -/
abbrev Qr : (Opens (TopCat.of M))ᵒᵖ ⥤ RingCat.{0} :=
  quotientVanishingIdealPresheaf n Z ⋙ forget₂ CommRingCat RingCat.{0}

variable (n Z) in
/-- The sheaf of rings `ι_* 𝒪_Z` on `M`. -/
abbrev Bsh : Sheaf (Opens.grothendieckTopology (TopCat.of M)) RingCat.{0} :=
  ((Opens.map (submanifoldInclusion Z)).sheafPushforwardContinuous RingCat.{0}
    (Opens.grothendieckTopology (TopCat.of M)) (Opens.grothendieckTopology (TopCat.of Z))).obj
    (OZ n Z)

/-- The ring map `𝒪_M(U) → 𝒪_Z(ι⁻¹ U)`. -/
abbrev tSHom (U : Opens (TopCat.of M)) :
    (holSheaf n M).obj.obj (op U) →+*
      (OZ n Z).obj.obj (op ((Opens.map (submanifoldInclusion Z)).obj U)) :=
  ((toStructure n Z).hom.app (op U)).hom

variable (n) in
/-- The map `𝒪_M / ℐ_Z ⟶ ι_* 𝒪_Z` of presheaves of rings. -/
noncomputable def quotToB (hZc : IsClosed Z) : Qr n Z ⟶ (Bsh n Z).obj where
  app U := RingCat.ofHom (Ideal.Quotient.lift (vanishingIdeal n Z U.unop) (tSHom U.unop)
    fun g hg => (toStructure_eq_zero_iff (n := n) hZc g).2 hg)
  naturality U V f := by
    ext q
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact NatTrans.naturality_apply (toStructure n Z).hom f g

/-- The map `𝒪_M / ℐ_Z ⟶ ι_* 𝒪_Z` is injective on sections over every open set. -/
theorem quotToB_injective (hZc : IsClosed Z) (U : (Opens (TopCat.of M))ᵒᵖ) :
    Function.Injective ((quotToB n hZc).app U) := by
  intro q₁ q₂ h
  obtain ⟨g₁, rfl⟩ := Ideal.Quotient.mk_surjective q₁
  obtain ⟨g₂, rfl⟩ := Ideal.Quotient.mk_surjective q₂
  refine Ideal.Quotient.eq.2 ((toStructure_eq_zero_iff (n := n) hZc _).1 ?_)
  exact (map_sub (tSHom U.unop) g₁ g₂).trans (sub_eq_zero.2 h)

/-- The map `𝒪_M / ℐ_Z ⟶ ι_* 𝒪_Z` is locally injective. -/
theorem isLocallyInjective_quotToB (hZc : IsClosed Z) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (TopCat.of M)) (quotToB n hZc) :=
  Presheaf.isLocallyInjective_of_injective _ _ (quotToB_injective hZc)

/-- The map `𝒪_M / ℐ_Z ⟶ ι_* 𝒪_Z` is locally surjective. -/
theorem isLocallySurjective_quotToB (hZc : IsClosed Z) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of M)) (quotToB n hZc) := by
  refine ⟨fun {U} c => (Opens.mem_grothendieckTopology _).2 fun y hy => ?_⟩
  by_cases hyZ : y ∈ Z
  · obtain ⟨U1, hy1, hU1, g, hg⟩ :=
      exists_toStructure_eq_fun (n := n) hZc (fun _ : Unit => c) (show (⟨y, hyZ⟩ : Z) ∈ _ from hy)
    refine ⟨U1 ⊓ U, homOfLE inf_le_right, ⟨Ideal.Quotient.mk _ (resA inf_le_left (g ())), ?_⟩,
      ⟨hy1, hy⟩⟩
    refine ((toStructure_resA _ _).trans ((congrArg (resA (A := OZ n Z) _) (hg ())).trans
      (resA_resA (A := OZ n Z) _ _ _)))
  · refine ⟨U ⊓ ⟨Zᶜ, hZc.isOpen_compl⟩, homOfLE inf_le_left, ⟨0, ?_⟩, ⟨hy, hyZ⟩⟩
    exact @Subsingleton.elim _ (subsingleton_OZ (n := n) hZc (W := (Opens.map
      (submanifoldInclusion Z)).obj (U ⊓ ⟨Zᶜ, hZc.isOpen_compl⟩)) fun z hz => hz.2 z.2) _ _

variable (n Z) in
/-- The property that `ℐ_Z` kills a sheaf of `𝒪_M`-modules. -/
abbrev KilledBy (T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)) : Prop :=
  ∀ (U : Opens (TopCat.of M)) (g : 𝒪[n, M].presheaf.obj (op U)), g ∈ vanishingIdeal n Z U →
    ∀ t : T.val.obj (op U), (show (holomorphicRingCatSheaf n M).obj.obj (op U) from g) • t = 0

/-- The `𝒪_M(U)`-module structure of `T(U)`, over the commutative ring `𝒪_M(U)`. -/
abbrev holModule (T : SheafOfModules.{0} (holomorphicRingCatSheaf n M))
    (U : (Opens (TopCat.of M))ᵒᵖ) : Module (𝒪[n, M].presheaf.obj U) (T.val.obj U) :=
  inferInstanceAs (Module ((holomorphicRingCatSheaf n M).obj.obj U) (T.val.obj U))

/-- A module killed by `ℐ_Z` is a module over `𝒪_M / ℐ_Z`. -/
abbrev quotModule {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)}
    (hT : KilledBy n Z T) (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module ((Qr n Z).obj U) (T.val.presheaf.obj U) :=
  @Module.IsTorsionBySet.module (𝒪[n, M].presheaf.obj U) (T.val.obj U) _ _ (holModule T U)
    (vanishingIdeal n Z U.unop) _ (fun t a => hT U.unop a.1 a.2 t)

/-- A module killed by `ℐ_Z`, as a presheaf of modules over `𝒪_M / ℐ_Z`. -/
noncomputable def quotPresheafOfModules {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)}
    (hT : KilledBy n Z T) : PresheafOfModules.{0} (Qr n Z) :=
  letI := quotModule hT
  PresheafOfModules.ofPresheaf T.val.presheaf fun {X Y} f r m => by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact PresheafOfModules.map_smul T.val f g m

/-- The identification of the underlying presheaf of `quotPresheafOfModules hT` with `T`. -/
noncomputable abbrev quotPresheafId {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)}
    (hT : KilledBy n Z T) :
    (quotPresheafOfModules hT).presheaf ⟶ ((SheafOfModules.toSheaf _).obj T).obj :=
  𝟙 _

/-- The identification `quotPresheafId hT` is locally injective. -/
theorem isLocallyInjective_quotPresheafId
    {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)} (hT : KilledBy n Z T) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (TopCat.of M)) (quotPresheafId hT) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ => Function.injective_id

/-- The identification `quotPresheafId hT` is locally surjective. -/
theorem isLocallySurjective_quotPresheafId
    {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)} (hT : KilledBy n Z T) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of M)) (quotPresheafId hT) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ => Function.surjective_id

/-- A module killed by `ℐ_Z`, as a sheaf of `ι_* 𝒪_Z`-modules on `M`. -/
noncomputable def toBModule (hZc : IsClosed Z)
    {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)} (hT : KilledBy n Z T) :
    SheafOfModules.{0} (Bsh n Z) :=
  haveI := isLocallyInjective_quotToB (n := n) hZc
  haveI := isLocallySurjective_quotToB (n := n) hZc
  haveI := isLocallyInjective_quotPresheafId hT
  haveI := isLocallySurjective_quotPresheafId hT
  PresheafOfModules.sheafify (quotToB n hZc) (quotPresheafId hT)

/-- The `ι_* 𝒪_Z`-module structure on a module killed by `ℐ_Z` extends its `𝒪_M`-module
structure. -/
theorem toBModule_smul (hZc : IsClosed Z)
    {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)} (hT : KilledBy n Z T)
    {U : Opens (TopCat.of M)} (g : (holSheaf n M).obj.obj (op U)) (m : T.val.obj (op U)) :
    ((show (Bsh n Z).obj.obj (op U) from tS n Z g) •
        (show (toBModule hZc hT).val.obj (op U) from m) :
      (toBModule hZc hT).val.obj (op U)) =
      (show (toBModule hZc hT).val.obj (op U) from g • m) := by
  haveI := isLocallyInjective_quotToB (n := n) hZc
  haveI := isLocallySurjective_quotToB (n := n) hZc
  haveI := isLocallyInjective_quotPresheafId hT
  haveI := isLocallySurjective_quotPresheafId hT
  exact (((PresheafOfModules.toSheafify (quotToB n hZc) (quotPresheafId hT)).app
    (op U)).hom.map_smul (Ideal.Quotient.mk _ g) m).symm

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] in
variable (Z) in
/-- The largest open set `M ∖ (Z ∖ W)` of `M` whose trace on `Z` is `W`. -/
def wt (hZc : IsClosed Z) (W : Opens (TopCat.of Z)) : Opens (TopCat.of M) :=
  ⟨(Subtype.val '' ((W : Set Z)ᶜ))ᶜ,
    (hZc.isClosedEmbedding_subtypeVal.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- A point lies in `wt Z hZc W` exactly when, if it lies in `Z`, it lies in `W`. -/
theorem mem_wt {hZc : IsClosed Z} {W : Opens (TopCat.of Z)} {x : M} :
    x ∈ wt Z hZc W ↔ ∀ hx : x ∈ Z, (⟨x, hx⟩ : Z) ∈ W := by
  change x ∉ Subtype.val '' ((W : Set Z)ᶜ) ↔ _
  constructor
  · intro h hx
    by_contra hW
    exact h ⟨⟨x, hx⟩, hW, rfl⟩
  · rintro h ⟨z, hz, rfl⟩
    exact hz (h z.2)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- The open set `wt Z hZc W` is monotone in `W`. -/
theorem wt_mono (hZc : IsClosed Z) : Monotone (wt Z hZc) := fun _ _ h _ hx =>
  (mem_wt (hZc := hZc)).2 fun hz => h ((mem_wt (hZc := hZc)).1 hx hz)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- The trace of `wt Z hZc W` on `Z` is `W`. -/
theorem map_wt (hZc : IsClosed Z) (W : Opens (TopCat.of Z)) :
    (Opens.map (submanifoldInclusion Z)).obj (wt Z hZc W) = W := by
  ext z
  exact ⟨fun h => (mem_wt (hZc := hZc)).1 h z.2, fun h => (mem_wt (hZc := hZc)).2 fun _ => h⟩

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- An open set `U` of `M` is contained in `wt` of its trace on `Z`. -/
theorem le_wt_map (hZc : IsClosed Z) (U : Opens (TopCat.of M)) :
    U ≤ wt Z hZc ((Opens.map (submanifoldInclusion Z)).obj U) := fun _ hx =>
  (mem_wt (hZc := hZc)).2 fun _ => hx

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- `wt Z hZc` preserves binary intersections. -/
theorem wt_inf (hZc : IsClosed Z) (A B : Opens (TopCat.of Z)) :
    wt Z hZc (A ⊓ B) = wt Z hZc A ⊓ wt Z hZc B := by
  ext x
  simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
  rw [mem_wt, mem_wt, mem_wt]
  exact ⟨fun h => ⟨fun hx => (h hx).1, fun hx => (h hx).2⟩, fun h hx => ⟨h.1 hx, h.2 hx⟩⟩

variable (Z) in
/-- The functor `W ↦ M ∖ (Z ∖ W)`. -/
abbrev wtFunctor (hZc : IsClosed Z) : Opens (TopCat.of Z) ⥤ Opens (TopCat.of M) :=
  (wt_mono hZc).functor

variable (n) in
/-- The ring maps `𝒪_Z(W) → (ι_* 𝒪_Z)(M ∖ (Z ∖ W)) = 𝒪_Z(W)`. -/
noncomputable def wtRingHom (hZc : IsClosed Z) :
    (OZ n Z).obj ⟶ (wtFunctor Z hZc).op ⋙ (Bsh n Z).obj where
  app W := (OZ n Z).obj.map (homOfLE (map_wt hZc W.unop).le).op
  naturality W W' f := by
    change (OZ n Z).obj.map f ≫ (OZ n Z).obj.map _ = (OZ n Z).obj.map _ ≫ (OZ n Z).obj.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- **Restriction to `Z` of a sheaf supported on `Z`.** If `F` has no sections on opens
disjoint from `Z`, then `W ↦ F(M ∖ (Z ∖ W))` is a sheaf on `Z`. -/
theorem isSheaf_wtFunctor_comp (hZc : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M))
    (hF : ∀ (U : Opens (TopCat.of M)), (∀ x ∈ U, x ∉ Z) →
      ∀ t : ToType (F.presheaf.obj (op U)), t = 0) :
    TopCat.Presheaf.IsSheaf ((wtFunctor Z hZc).op ⋙ F.presheaf) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι' U sf hsf
  let Zc : Opens (TopCat.of M) := ⟨Zᶜ, hZc.isOpen_compl⟩
  let V : Option ι' → Opens (TopCat.of M) := fun o =>
    o.elim (wt Z hZc (iSup U) ⊓ Zc) (fun i => wt Z hZc (U i))
  have hVle : ∀ o, V o ≤ wt Z hZc (iSup U) := by
    rintro (_ | i)
    · exact inf_le_left
    · exact wt_mono hZc (le_iSup U i)
  have hcover : wt Z hZc (iSup U) ≤ iSup V := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 ((mem_wt (hZc := hZc)).1 hx hxZ)
      exact Opens.mem_iSup.2 ⟨some i, (mem_wt (hZc := hZc)).2 fun _ => hi⟩
    · exact Opens.mem_iSup.2 ⟨none, hx, hxZ⟩
  have hZcV : ∀ (A : Opens (TopCat.of M)), A ≤ Zc → ∀ t : ToType (F.presheaf.obj (op A)), t = 0 :=
    fun A hA => hF A fun x hx => hA hx
  let sf' : ∀ o, ToType (F.presheaf.obj (op (V o))) := fun o => match o with
    | none => 0
    | some i => sf i
  have hcomp : TopCat.Presheaf.IsCompatible F.presheaf V sf' := by
    rintro (_ | i) (_ | j)
    · exact (hZcV _ (inf_le_left.trans inf_le_right) _).trans
        (hZcV _ (inf_le_left.trans inf_le_right) _).symm
    · exact (hZcV _ (inf_le_left.trans inf_le_right) _).trans
        (hZcV _ (inf_le_left.trans inf_le_right) _).symm
    · exact (hZcV _ (inf_le_right.trans inf_le_right) _).trans
        (hZcV _ (inf_le_right.trans inf_le_right) _).symm
    · have h := congrArg (F.presheaf.map (homOfLE (wt_inf hZc (U i) (U j)).ge).op) (hsf i j)
      change F.presheaf.map _ (F.presheaf.map _ (sf i)) =
        F.presheaf.map _ (F.presheaf.map _ (sf j)) at h
      rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp, ← ConcreteCategory.comp_apply,
        ← F.presheaf.map_comp] at h
      exact h
  obtain ⟨s, hs, hsu⟩ := F.existsUnique_gluing' V (wt Z hZc (iSup U))
    (fun o => homOfLE (hVle o)) hcover sf' hcomp
  refine ⟨s, fun i => hs (some i), fun t ht => hsu t ?_⟩
  rintro (_ | i)
  · exact (hZcV _ inf_le_right _).trans (hZcV _ inf_le_right _).symm
  · exact ht i

/-- A module killed by `ℐ_Z` has no sections on opens disjoint from `Z`. -/
theorem eq_zero_of_killedBy {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)}
    (hT : KilledBy n Z T) {U : Opens (TopCat.of M)} (hU : ∀ x ∈ U, x ∉ Z)
    (t : T.val.obj (op U)) : t = 0 := by
  have := hT U 1 (fun x hx => absurd hx (hU x.1 x.2)) t
  change (1 : (holSheaf n M).obj.obj (op U)) • t = 0 at this
  rwa [one_smul] at this

/-- For a module killed by `ℐ_Z`, restriction `T(V) → T(U)` is bijective when `U` contains
`V ∩ Z`. -/
theorem bijective_resM_of_killedBy (hZc : IsClosed Z)
    {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)} (hT : KilledBy n Z T)
    {U V : Opens (TopCat.of M)} (h : U ≤ V) (hUV : ∀ x ∈ V, x ∈ Z → x ∈ U) :
    Function.Bijective (resM (A := holSheaf n M) T h) := by
  let Zc : Opens (TopCat.of M) := ⟨Zᶜ, hZc.isOpen_compl⟩
  constructor
  · refine (injective_iff_map_eq_zero (T.val.map (homOfLE h).op).hom).2 fun t ht => ?_
    refine eq_zero_of_locally_eq_zero (A := holSheaf n M) T t fun y hy => ?_
    by_cases hyZ : y ∈ Z
    · exact ⟨U, h, hUV y hy hyZ, ht⟩
    · exact ⟨V ⊓ Zc, inf_le_left, ⟨hy, hyZ⟩,
        eq_zero_of_killedBy hT (U := V ⊓ Zc) (fun x hx => hx.2) _⟩
  · intro s
    let F : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) := (SheafOfModules.toSheaf _).obj T
    let Vf : Bool → Opens (TopCat.of M) := fun b => Bool.rec (V ⊓ Zc) U b
    have hVf : ∀ b, Vf b ≤ V := by
      rintro (_ | _)
      · exact inf_le_left
      · exact h
    have hcover : V ≤ iSup Vf := by
      intro x hx
      by_cases hxZ : x ∈ Z
      · exact Opens.mem_iSup.2 ⟨true, hUV x hx hxZ⟩
      · exact Opens.mem_iSup.2 ⟨false, hx, hxZ⟩
    have hZ0 : ∀ (A : Opens (TopCat.of M)), A ≤ Zc → ∀ t : ToType (F.presheaf.obj (op A)),
        t = 0 := fun A hA t => eq_zero_of_killedBy hT (fun x hx => hA hx) t
    let sf : ∀ b, ToType (F.presheaf.obj (op (Vf b))) := fun b => match b with
      | false => 0
      | true => s
    have hcomp : TopCat.Presheaf.IsCompatible F.presheaf Vf sf := by
      rintro (_ | _) (_ | _)
      · exact (hZ0 _ (inf_le_left.trans inf_le_right) _).trans
          (hZ0 _ (inf_le_left.trans inf_le_right) _).symm
      · exact (hZ0 _ (inf_le_left.trans inf_le_right) _).trans
          (hZ0 _ (inf_le_left.trans inf_le_right) _).symm
      · exact (hZ0 _ (inf_le_right.trans inf_le_right) _).trans
          (hZ0 _ (inf_le_right.trans inf_le_right) _).symm
      · rfl
    obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' Vf V (fun b => homOfLE (hVf b)) hcover sf hcomp
    exact ⟨t, ht true⟩

/-- The restriction `T|_Z` of a module killed by `ℐ_Z`: the `𝒪_Z`-module
`W ↦ T(M ∖ (Z ∖ W))`. -/
noncomputable def restrZ (hZc : IsClosed Z)
    {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)} (hT : KilledBy n Z T) :
    SheafOfModules.{0} (OZ n Z) where
  val := (PresheafOfModules.pushforward (wtRingHom n hZc)).obj (toBModule hZc hT).val
  isSheaf := isSheaf_wtFunctor_comp hZc ((SheafOfModules.toSheaf _).obj T)
    fun _ hU t => eq_zero_of_killedBy hT hU t

/-- The comparison `ι_* (T|_Z) ⟶ T`, restriction along `U ⊆ M ∖ (Z ∖ (U ∩ Z))`. -/
noncomputable def restrZHom (hZc : IsClosed Z)
    {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)} (hT : KilledBy n Z T) :
    pushZ (restrZ hZc hT) ⟶ T where
  val := PresheafOfModules.homMk
    { app U := T.val.presheaf.map (homOfLE (le_wt_map hZc U.unop)).op
      naturality U V f := by
        change T.val.presheaf.map _ ≫ T.val.presheaf.map _ =
          T.val.presheaf.map _ ≫ T.val.presheaf.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl }
    fun U r m => by
      let f : op (wt Z hZc ((Opens.map (submanifoldInclusion Z)).obj U.unop)) ⟶ U :=
        (homOfLE (le_wt_map hZc U.unop)).op
      let b : (Bsh n Z).obj.obj (op (wt Z hZc ((Opens.map (submanifoldInclusion Z)).obj U.unop))) :=
        (wtRingHom n hZc).app (op ((Opens.map (submanifoldInclusion Z)).obj U.unop)) (tS n Z r)
      have h1 := PresheafOfModules.map_smul (toBModule hZc hT).val f b
        (show (toBModule hZc hT).val.obj _ from m)
      have h2 : (Bsh n Z).obj.map f b = tS n Z r := by
        change (OZ n Z).obj.map _ ((OZ n Z).obj.map _ (tS n Z r)) = _
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        have hid : ∀ g : op ((Opens.map (submanifoldInclusion Z)).obj U.unop) ⟶
            op ((Opens.map (submanifoldInclusion Z)).obj U.unop), (OZ n Z).obj.map g = 𝟙 _ :=
          fun g => by rw [Subsingleton.elim g (𝟙 _), CategoryTheory.Functor.map_id]
        rw [hid]
        rfl
      refine h1.trans ?_
      refine (congrArg (fun c : (Bsh n Z).obj.obj U => c •
        (show (toBModule hZc hT).val.obj U from (toBModule hZc hT).val.map f m)) h2).trans ?_
      exact toBModule_smul hZc hT r _

/-- For a sheaf of modules `T` killed by `ℐ_Z`, the comparison `ι_* (T|_Z) ⟶ T` is an
isomorphism. -/
theorem isIso_restrZHom (hZc : IsClosed Z)
    {T : SheafOfModules.{0} (holomorphicRingCatSheaf n M)} (hT : KilledBy n Z T) :
    IsIso (restrZHom hZc hT) := by
  let Φ := SheafOfModules.forget (holomorphicRingCatSheaf n M) ⋙
    PresheafOfModules.toPresheaf (holomorphicRingCatSheaf n M).obj
  haveI : IsIso (Φ.map (restrZHom hZc hT)) := by
    haveI : ∀ U, IsIso ((Φ.map (restrZHom hZc hT)).app U) := fun U =>
      (ConcreteCategory.isIso_iff_bijective _).2
        (bijective_resM_of_killedBy hZc hT (le_wt_map hZc U.unop)
          fun x hx hxZ => (mem_wt (hZc := hZc)).1 hx hxZ)
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ Φ

/-- Restricting a section to an equal open set and back gives the section itself. -/
theorem resM_resM_self {T : TopCat.{0}} {A : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
    (S : SheafOfModules.{0} A) {W W' : Opens T} (h : W' ≤ W) (h' : W ≤ W')
    (t : S.val.obj (op W)) : resM S h' (resM S h t) = t := by
  rw [resM_resM]
  simp only [resM]
  rw [show homOfLE (h'.trans h) = 𝟙 W from Subsingleton.elim _ _, op_id, PresheafOfModules.map_id]
  rfl

/-- A morphism of `𝒪_Z`-modules is determined by its direct image. -/
theorem app_eq_resM_pushforward_map (hZc : IsClosed Z) {S₁ S₂ : SheafOfModules.{0} (OZ n Z)}
    (f : S₁ ⟶ S₂) (W : Opens (TopCat.of Z)) (s : S₁.val.obj (op W)) :
    f.val.app (op W) s = resM S₂ (map_wt hZc W).ge
      (((SheafOfModules.pushforward.{0} (φZ n Z)).map f).val.app (op (wt Z hZc W))
        (resM S₁ (map_wt hZc W).le s)) := by
  refine (resM_resM_self S₂ (map_wt hZc W).le (map_wt hZc W).ge _).symm.trans ?_
  exact congrArg (resM S₂ (map_wt hZc W).ge) (hom_resM f (map_wt hZc W).le s).symm

/-- For closed `Z`, the direct image `ι_*` of sheaves of modules is faithful. -/
theorem faithful_pushZ (hZc : IsClosed Z) :
    (SheafOfModules.pushforward.{0} (φZ n Z)).Faithful := by
  refine ⟨fun {S₁ S₂} f g hfg => ?_⟩
  ext W s
  induction W using Opposite.rec with | op W => ?_
  rw [app_eq_resM_pushforward_map hZc f, app_eq_resM_pushforward_map hZc g, hfg]

/-- Sections of a sheaf of modules which agree locally agree. -/
theorem eq_of_locally_eq' {T : TopCat.{0}} {A : Sheaf (Opens.grothendieckTopology T) RingCat.{0}}
    (S : SheafOfModules.{0} A) {U : Opens T} (t t' : S.val.obj (op U))
    (h : ∀ y ∈ U, ∃ (U' : Opens T) (hU' : U' ≤ U), y ∈ U' ∧ resM S hU' t = resM S hU' t') :
    t = t' := by
  refine sub_eq_zero.1 (eq_zero_of_locally_eq_zero S _ fun y hy => ?_)
  obtain ⟨U', hU', hy', e⟩ := h y hy
  exact ⟨U', hU', hy', (map_sub (S.val.map (homOfLE hU').op).hom t t').trans (sub_eq_zero.2 e)⟩

/-- Naturality of a morphism of direct images, read on `𝒪_Z`-modules. -/
theorem pushZ_hom_resM {S₁ S₂ : SheafOfModules.{0} (OZ n Z)} (h : pushZ S₁ ⟶ pushZ S₂)
    {U U' : Opens (TopCat.of M)} (hU : U' ≤ U)
    (x : S₁.val.obj (op ((Opens.map (submanifoldInclusion Z)).obj U))) :
    h.val.app (op U') (resM S₁ ((Opens.map (submanifoldInclusion Z)).monotone hU) x) =
      resM S₂ ((Opens.map (submanifoldInclusion Z)).monotone hU) (h.val.app (op U) x) :=
  hom_resM h hU x

/-- The morphism of `𝒪_Z`-modules underlying a morphism of direct images. -/
noncomputable def pushZPreimage (hZc : IsClosed Z) {S₁ S₂ : SheafOfModules.{0} (OZ n Z)}
    (h : pushZ S₁ ⟶ pushZ S₂) : S₁ ⟶ S₂ where
  val := PresheafOfModules.homMk
    { app W := S₁.val.presheaf.map (homOfLE (map_wt hZc W.unop).le).op ≫
        ((PresheafOfModules.toPresheaf _).map h.val).app (op (wt Z hZc W.unop)) ≫
        S₂.val.presheaf.map (homOfLE (map_wt hZc W.unop).ge).op
      naturality W W' i := by
        induction W using Opposite.rec with | op W => ?_
        induction W' using Opposite.rec with | op W' => ?_
        have hi : W' ≤ W := i.unop.le
        have hw : wt Z hZc W' ≤ wt Z hZc W := wt_mono hZc hi
        ext s
        change resM S₂ (map_wt hZc W').ge (h.val.app (op (wt Z hZc W'))
            (resM S₁ (map_wt hZc W').le (resM S₁ hi s))) =
          resM S₂ hi (resM S₂ (map_wt hZc W).ge (h.val.app (op (wt Z hZc W))
            (resM S₁ (map_wt hZc W).le s)))
        have e1 : resM S₁ (map_wt hZc W').le (resM S₁ hi s) =
            resM S₁ ((Opens.map (submanifoldInclusion Z)).monotone hw)
              (resM S₁ (map_wt hZc W).le s) :=
          (resM_resM S₁ _ _ _).trans (resM_resM S₁ _ _ _).symm
        refine (congrArg (fun x => resM S₂ (map_wt hZc W').ge (h.val.app (op (wt Z hZc W')) x))
          e1).trans ?_
        refine (congrArg (resM S₂ (map_wt hZc W').ge) (pushZ_hom_resM h hw _)).trans ?_
        exact (resM_resM S₂ _ _ _).trans (resM_resM S₂ _ _ _).symm }
    fun W c s => by
      induction W using Opposite.rec with | op W => ?_
      have key : ∀ (x : S₁.val.obj (op W)) {U' : Opens (TopCat.of M)} (hU' : U' ≤ wt Z hZc W),
          resM S₂ (((Opens.map (submanifoldInclusion Z)).monotone hU').trans (map_wt hZc W).le)
            (resM S₂ (map_wt hZc W).ge (h.val.app (op (wt Z hZc W))
              (resM S₁ (map_wt hZc W).le x))) =
          h.val.app (op U') (resM S₁ (((Opens.map (submanifoldInclusion Z)).monotone hU').trans
            (map_wt hZc W).le) x) := fun x U' hU' =>
        (resM_resM S₂ _ _ _).trans ((pushZ_hom_resM h hU' _).symm.trans
          (congrArg (h.val.app (op U')) (resM_resM S₁ _ _ _)))
      change resM S₂ (map_wt hZc W).ge (h.val.app _ (resM S₁ (map_wt hZc W).le (c • s))) =
        c • resM S₂ (map_wt hZc W).ge (h.val.app _ (resM S₁ (map_wt hZc W).le s))
      refine eq_of_locally_eq' S₂ _ _ fun z hz => ?_
      obtain ⟨U, hzU, hUW, g, hg⟩ :=
        exists_toStructure_eq_fun (n := n) hZc (fun _ : Unit => c) hz
      have hU'W : U ⊓ wt Z hZc W ≤ wt Z hZc W := inf_le_right
      have hU'W' : (Opens.map (submanifoldInclusion Z)).obj (U ⊓ wt Z hZc W) ≤ W :=
        ((Opens.map (submanifoldInclusion Z)).monotone hU'W).trans (map_wt hZc W).le
      refine ⟨(Opens.map (submanifoldInclusion Z)).obj (U ⊓ wt Z hZc W), hU'W',
        ⟨hzU, (mem_wt (hZc := hZc)).2 fun _ => hz⟩, ?_⟩
      let g' : (holSheaf n M).obj.obj (op (U ⊓ wt Z hZc W)) := resA inf_le_left (g ())
      have eg : tS n Z g' = resA (A := OZ n Z) hU'W' c :=
        (toStructure_resA _ _).trans ((congrArg (resA (A := OZ n Z) _) (hg ())).trans
          (resA_resA (A := OZ n Z) _ _ _))
      have hR : resM S₂ hU'W' (c • resM S₂ (map_wt hZc W).ge (h.val.app _
          (resM S₁ (map_wt hZc W).le s))) =
          resA (A := OZ n Z) hU'W' c • (show S₂.val.obj (op ((Opens.map
            (submanifoldInclusion Z)).obj (U ⊓ wt Z hZc W))) from
              h.val.app (op (U ⊓ wt Z hZc W)) (resM S₁ hU'W' s)) :=
        (resM_smul S₂ _ _ _).trans (congrArg (fun (y : S₂.val.obj (op ((Opens.map
          (submanifoldInclusion Z)).obj (U ⊓ wt Z hZc W)))) => resA (A := OZ n Z) hU'W' c • y)
          (key s hU'W))
      refine Eq.trans ?_ hR.symm
      refine (key (c • s) hU'W).trans ?_
      refine (congrArg (h.val.app (op (U ⊓ wt Z hZc W))) (resM_smul S₁ hU'W' c s)).trans ?_
      have e2 : (resA (A := OZ n Z) hU'W' c • resM S₁ hU'W' s : S₁.val.obj _) =
          (show (pushZ S₁).val.obj (op (U ⊓ wt Z hZc W)) from g' • (show (pushZ S₁).val.obj
            (op (U ⊓ wt Z hZc W)) from resM S₁ hU'W' s)) :=
        (congrArg (fun a => a • resM S₁ hU'W' s) eg.symm).trans (pushZ_smul S₁ g' _).symm
      refine (congrArg (h.val.app (op (U ⊓ wt Z hZc W))) e2).trans ?_
      refine ((h.val.app (op (U ⊓ wt Z hZc W))).hom.map_smul g' _).trans ?_
      refine (pushZ_smul S₂ g' _).trans ?_
      exact congrArg (fun a => a • (show S₂.val.obj _ from
        h.val.app (op (U ⊓ wt Z hZc W)) (resM S₁ hU'W' s))) eg

/-- For closed `Z`, the direct image functor from sheaves of `𝒪_Z`-modules to sheaves of
`𝒪_M`-modules is full. -/
theorem full_pushZ (hZc : IsClosed Z) :
    (SheafOfModules.pushforward.{0} (φZ n Z)).Full := by
  refine ⟨fun {S₁ S₂} h => ⟨pushZPreimage hZc h, ?_⟩⟩
  ext U t
  induction U using Opposite.rec with | op U => ?_
  change resM S₂ (map_wt hZc _).ge (h.val.app (op (wt Z hZc ((Opens.map
    (submanifoldInclusion Z)).obj U))) (resM S₁ (map_wt hZc _).le t)) = h.val.app (op U) t
  refine (pushZ_hom_resM h (le_wt_map hZc U) _).symm.trans ?_
  exact congrArg (h.val.app (op U)) (resM_resM_self S₁ _ _ t)

/-- A sheaf of `𝒪_Z`-modules whose direct image is of finite type is of finite type. -/
theorem finGen_of_pushZ (hZc : IsClosed Z) (S : SheafOfModules.{0} (OZ n Z))
    (hS : FinGen (A := holSheaf n M) (pushZ S)) : FinGen S := by
  intro z
  obtain ⟨W, hzW, m, g, hg⟩ := hS z.1
  refine ⟨(Opens.map (submanifoldInclusion Z)).obj W, hzW, m, g,
    locallyGenerates_of_nhds _ fun U hU t y hy => ?_⟩
  have hVW : wt Z hZc U ⊓ W ≤ W := inf_le_right
  have hV : (Opens.map (submanifoldInclusion Z)).obj (wt Z hZc U ⊓ W) = U := by
    ext w
    exact ⟨fun h => (mem_wt (hZc := hZc)).1 h.1 w.2, fun h => ⟨(mem_wt (hZc := hZc)).2
      fun _ => h, hU h⟩⟩
  have hyV : y.1 ∈ wt Z hZc U ⊓ W := ⟨(mem_wt (hZc := hZc)).2 fun _ => hy, hU hy⟩
  obtain ⟨U1, h1, hy1, c, hc⟩ := hg.exists_nhds hVW
    (show (pushZ S).val.obj (op (wt Z hZc U ⊓ W)) from resM S hV.le t) hyV
  refine ⟨(Opens.map (submanifoldInclusion Z)).obj U1,
    ((Opens.map (submanifoldInclusion Z)).monotone h1).trans hV.le, hy1, fun k => tS n Z (c k), ?_⟩
  exact (resM_resM S _ _ _).symm.trans (hc.trans (Finset.sum_congr rfl fun k _ =>
    pushZ_smul S _ _))

/-- A sheaf of `𝒪_Z`-modules whose direct image has locally finitely generated relations has
locally finitely generated relations. -/
theorem relFin_of_pushZ (hZc : IsClosed Z) (S : SheafOfModules.{0} (OZ n Z))
    (hS : RelFin (A := holSheaf n M) (pushZ S)) : RelFin S := by
  intro V p f z hz
  obtain ⟨W, hWV, hzW, s, r, hr, hgen⟩ := hS (wt Z hZc V) p
    (fun j => show (pushZ S).val.obj (op (wt Z hZc V)) from resM S (map_wt hZc V).le (f j)) z.1
    ((mem_wt (hZc := hZc)).2 fun _ => hz)
  have hWV' : (Opens.map (submanifoldInclusion Z)).obj W ≤ V :=
    ((Opens.map (submanifoldInclusion Z)).monotone hWV).trans (map_wt hZc V).le
  refine ⟨(Opens.map (submanifoldInclusion Z)).obj W, hWV', hzW, s, fun k j => tS n Z (r k j),
    fun k => ?_, fun U hUW a ha y hy => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hr k)
    exact (congrArg (fun x => tS n Z (r k j) • x) (resM_resM S _ _ _).symm).trans
      (pushZ_smul S _ _).symm
  · obtain ⟨U1, hy1, hU1, at', hat⟩ := exists_toStructure_eq_fun (n := n) hZc a hy
    have hU2W : U1 ⊓ W ≤ W := inf_le_right
    have hU2 : (Opens.map (submanifoldInclusion Z)).obj (U1 ⊓ W) ≤ U :=
      ((Opens.map (submanifoldInclusion Z)).monotone inf_le_left).trans hU1
    have eat : ∀ j, tS n Z (resA (inf_le_left : U1 ⊓ W ≤ U1) (at' j)) =
        resA (A := OZ n Z) hU2 (a j) :=
      fun j => (toStructure_resA _ _).trans ((congrArg (resA (A := OZ n Z) _) (hat j)).trans
        (resA_resA (A := OZ n Z) _ _ _))
    have ha' : ∑ j, resA (inf_le_left : U1 ⊓ W ≤ U1) (at' j) •
        resM (pushZ S) (hU2W.trans hWV)
          (show (pushZ S).val.obj (op (wt Z hZc V)) from resM S (map_wt hZc V).le (f j)) = 0 := by
      have e0 := congrArg (resM S hU2) ha
      rw [resM_sum_smul, resM_zero] at e0
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) e0
      refine (pushZ_smul S _ _).trans ?_
      exact congrArg₂ (fun (b : (OZ n Z).obj.obj (op _)) (x : S.val.obj (op _)) => b • x) (eat j)
        ((resM_resM S _ _ _).trans (resM_resM S _ _ _).symm)
    obtain ⟨U3, h3, hy3, d, hd⟩ := hgen (U1 ⊓ W) hU2W _ ha' y.1 ⟨hy1, hUW hy⟩
    refine ⟨(Opens.map (submanifoldInclusion Z)).obj U3,
      ((Opens.map (submanifoldInclusion Z)).monotone h3).trans hU2, hy3, fun k => tS n Z (d k),
      fun j => ?_⟩
    have e1 := congrArg (tSHom (n := n) (Z := Z) U3) (hd j)
    rw [map_sum] at e1
    refine Eq.trans ?_ (e1.trans (Finset.sum_congr rfl fun k _ => ?_))
    · refine Eq.trans ?_ (toStructure_resA _ _).symm
      refine Eq.trans ?_ (congrArg (resA (A := OZ n Z) _) (eat j).symm)
      exact (resA_resA (A := OZ n Z) _ _ _).symm
    · refine (map_mul _ _ _).trans (congrArg (fun b => tS n Z (d k) * b) ?_)
      exact toStructure_resA _ _

/-- Coherence is invariant under isomorphism. -/
theorem isCoherentModule_of_iso' {X : TopCat.{0}}
    {A : Sheaf (Opens.grothendieckTopology X) RingCat.{0}} {S T : SheafOfModules.{0} A}
    (e : S ≅ T) (hT : IsCoherentModule T) : IsCoherentModule S :=
  isCoherentModule_of_mono e.hom hT (isFiniteType_of_iso e.symm hT.1)

/-- A sheaf of `𝒪_Z`-modules whose direct image is coherent is coherent. -/
theorem isCoherentModule_of_pushZ (hZc : IsClosed Z) (S : SheafOfModules.{0} (OZ n Z))
    (hS : IsCoherentModule (pushZ S)) : IsCoherentModule S :=
  isCoherentModule_of_finGen_of_relFin
    (finGen_of_pushZ hZc S ((isFiniteType_iff_finGen (A := holSheaf n M) _).1 hS.1))
    (relFin_of_pushZ hZc S (relFin_of_isCoherentModule (A := holSheaf n M) hS))

/-- **Part (4d)**: a coherent `𝒪_M`-module killed by `ℐ_Z` is the direct image of its coherent
restriction to `Z`. -/
theorem pullback_package (hZc : IsClosed Z) :
    haveI : (PresheafOfModules.pushforward.{0} (φZ n Z).hom).IsRightAdjoint :=
      Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
        (PresheafOfModules.pullbackObjIsDefined_eq_top (φZ n Z).hom)
    haveI : (SheafOfModules.pushforward.{0} (φZ n Z)).IsRightAdjoint :=
      (SheafOfModules.PullbackConstruction.adjunction.{0} (φZ n Z)).isRightAdjoint
    ∀ T : SheafOfModules.{0} (holomorphicRingCatSheaf n M), IsCoherentModule T →
      KilledBy n Z T →
      IsCoherentModule ((SheafOfModules.pullback.{0} (φZ n Z)).obj T) ∧
        IsIso ((SheafOfModules.pullbackPushforwardAdjunction.{0} (φZ n Z)).unit.app T) := by
  intro T hT hI
  haveI := full_pushZ (n := n) hZc
  haveI := faithful_pushZ (n := n) hZc
  haveI := isIso_restrZHom hZc hI
  let e : T ≅ pushZ (restrZ hZc hI) := (asIso (restrZHom hZc hI)).symm
  have hT' : IsCoherentModule (restrZ hZc hI) :=
    isCoherentModule_of_pushZ hZc _ (isCoherentModule_of_iso' e.symm hT)
  refine ⟨isCoherentModule_of_iso' ((SheafOfModules.pullback.{0} (φZ n Z)).mapIso e ≪≫
    asIso ((SheafOfModules.pullbackPushforwardAdjunction.{0} (φZ n Z)).counit.app _)) hT', ?_⟩
  exact (SheafOfModules.pullbackPushforwardAdjunction.{0} (φZ n Z)).isIso_unit_app_of_iso e

end SubmanifoldModules

end ClosedEmbeddingSheaves

section PartFourA

open Limits Topology

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M]

local notation "𝒜" => holSheaf n M

variable {φ : OpenPartialHomeomorph M (EuclideanSpace ℂ (Fin n))}

/-- A coordinate `φᵢ`, `i ≥ k`, of a chart flattening `Z`, as a section of `ℐ_Z`. -/
noncomputable def chartCoordIdeal {Z : Set M}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M) {k : ℕ}
    (hflat : φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0})
    (i : {i : Fin n // k ≤ (i : ℕ)}) : vanishingIdeal n Z (chartSrc φ) :=
  ⟨chartCoord hφ i.1, fun q hq => by
    have h : φ q ∈ φ '' (Z ∩ φ.source) := ⟨q, ⟨hq, q.2⟩, rfl⟩
    rw [hflat] at h
    exact h.2 i.1 i.2⟩

/-- **Part (4a)**: in a chart flattening `Z`, the ideal `ℐ_Z` is generated by the coordinates
`φᵢ`, `i ≥ k`. -/
theorem vanishingIdeal_generated_by_coords {Z : Set M}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M) (k : ℕ)
    (hflat : φ '' (Z ∩ φ.source) = φ.target ∩ {y | ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0}) :
    ∃ y : {i : Fin n // k ≤ (i : ℕ)} →
        ((vanishingIdealSheaf n Z).over ⟨φ.source, φ.open_source⟩).sections,
      (∀ i (q : (⟨φ.source, φ.open_source⟩ : Opens (TopCat.of M))),
        (show vanishingIdeal n Z ⟨φ.source, φ.open_source⟩ from
          (y i).1 (op (Over.mk (𝟙 _)))).1 q = φ q i) ∧
      Epi (((vanishingIdealSheaf n Z).over ⟨φ.source, φ.open_source⟩).freeHomEquiv.symm y) := by
  refine ⟨fun i => overSection (vanishingIdealSheaf n Z) (chartCoordIdeal hφ hflat i),
    fun i q => rfl, ?_⟩
  refine epi_of_locally_surjective _ fun U q => ?_
  let f : (𝒜).obj.obj (op U.left) := (show vanishingIdeal n Z U.left from q).1
  have hf : ∀ w : U.left, (w : M) ∈ Z → holEval n U.left w f = 0 :=
    (show vanishingIdeal n Z U.left from q).2
  choose U' hU' hyU' c hc using fun (y : M) (hy : y ∈ U.left) =>
    exists_coord_gen hφ hflat U.hom.le f hf hy
  let T' : Sieve U :=
    { arrows := fun Y _ => ∃ y : U.left, Y.left ≤ U' y.1 y.2
      downward_closed := fun {Y Y'} _ ⟨y, hy⟩ g => ⟨y, g.left.le.trans hy⟩ }
  refine ⟨T', ?_, ?_⟩
  · rw [GrothendieckTopology.mem_over_iff]
    refine (Opens.mem_grothendieckTopology _).2 fun y hy => ?_
    refine ⟨U' y hy, homOfLE (hU' y hy), ?_, hyU' y hy⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨⟨y, hy⟩, le_rfl⟩
  · rintro Y g ⟨⟨y, hy⟩, hle⟩
    refine ⟨∑ i, (show ((𝒜).over _).obj.obj (op Y) from resA hle (c y hy i)) •
      (show (SheafOfModules.free (R := (𝒜).over (chartSrc φ))
        {i : Fin n // k ≤ (i : ℕ)}).val.obj (op Y) from
          (SheafOfModules.freeSection (R := (𝒜).over (chartSrc φ)) i).1 (op Y)), ?_⟩
    refine (freeHomEquiv_symm_app_sum _ (op Y) _).trans ?_
    apply Subtype.ext
    have key := congrArg (resA (A := 𝒜) hle) (hc y hy)
    rw [resA_resA, resA_sum] at key
    simp only [resA_mul, resA_resA] at key
    change _ = resA (hle.trans (hU' y hy)) f
    rw [key]
    erw [Submodule.coe_sum]
    rfl

end PartFourA

end MMP.Analytic.CoherentAnalytic
