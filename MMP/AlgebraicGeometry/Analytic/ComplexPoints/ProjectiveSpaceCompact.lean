module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceCompact
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartBasicOpen
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compactness of `ℙⁿ(K)`

Let `K` be a normed field. The set `ℙⁿ(K)` of `K`-points of projective space, with the classical
topology, is covered by the charts `Uᵢ(K) = {xᵢ ≠ 0}` carrying the affine coordinates
`y_{ij} = x_j / xᵢ`. These satisfy `y_{ii} = 1`, `y_{ik}(p) ≠ 0` iff `p ∈ U_k`, and
`y_{ij} = y_{ik} · y_{kj}` on `Uᵢ ∩ U_k`. The coordinate ring of `Uᵢ` is generated over `K` by the
`y_{ij}`, so `Uᵢ(K)` embeds as a closed subset of `K^{n+1}` and the closed unit polydisc
`{p ∈ Uᵢ(K) : |y_{ij}(p)| ≤ 1}` is compact when `K` is a proper metric space (for instance
`K = ℂ`). Hence `ℙⁿ(K)` is compact.

## Main results

* `MMP.UnderlyingSpace.isCompact_setOf_eval_mem`: for an affine open `U ⊆ X` whose
  coordinate ring is generated over `K` by sections `yᵢ`, the points of `U(K)` at which `(yᵢ)`
  takes values in a compact set form a compact set.
* `MMP.UnderlyingSpace.compactSpace_projectiveSpace`: `ℙⁿ(K)` is compact, for
  `ℙⁿ_K = Proj K[x₀, …, xₙ]` over `K` through `projToSpecCoeff`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology HomogeneousLocalization

universe u

namespace MMP

namespace UnderlyingSpace

section AffineOpen

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- The structure map `K → Γ(X, U)` of a scheme over `K`, on an open `U`. -/
def structureRingHomOpens (U : X.Opens) : K →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫
    (X ↘ Spec (.of K)).appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top _).ge)).hom

/-- A section coming from `K` takes its constant value at every point. -/
lemma eval_structureRingHomOpens {U : X.Opens} (p : UnderlyingSpace K X)
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ U) (c : K) : eval p hp (structureRingHomOpens U c) = c := by
  have key : ∀ (q : Spec (.of K) ⟶ Spec (.of K)) (_ : q = 𝟙 _) (e : ⊤ ≤ q ⁻¹ᵁ ⊤),
      q.appLE ⊤ ⊤ e = 𝟙 _ := by
    rintro _ rfl e
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    exact (Spec (.of K)).presheaf.map_id (Opposite.op ⊤)
  change ((Scheme.ΓSpecIso (.of K)).inv ≫
    (X ↘ Spec (.of K)).appLE ⊤ U (le_top.trans (Scheme.Hom.preimage_top _).ge) ≫
      p.toHom.appLE U ⊤ hp ≫ (Scheme.ΓSpecIso (.of K)).hom) c = c
  rw [Scheme.Hom.appLE_comp_appLE_assoc, key _ p.toHom_comp_over, Category.id_comp,
    Iso.inv_hom_id]
  rfl

/-- Evaluating a section `g ∈ Γ(X, U)` at the image in `X(K)` of a point `q` of `U(K)` is
evaluating the restriction of `g` to the scheme `U` at `q`. -/
lemma eval_mapFun_ι (U : X.Opens) (q : UnderlyingSpace K U.toScheme)
    (hq : ⊤ ≤ (mapFun U.ι q).toHom ⁻¹ᵁ U) (g : Γ(X, U)) :
    eval (mapFun U.ι q) hq g = evalTop q (U.ι.appLE U ⊤ U.ι_preimage_self.ge g) := by
  rw [evalTop, eval_appLE]

/-- The structure map `K → Γ(U, ⊤)` of the open subscheme `U` is the structure map
`K → Γ(X, U)` followed by the identification `Γ(X, U) ≅ Γ(U, ⊤)`. -/
lemma structureRingHom_opens (U : X.Opens) :
    structureRingHom K U.toScheme =
      (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom.comp (structureRingHomOpens U) := by
  rw [structureRingHom, structureRingHomOpens, ← CommRingCat.hom_comp, Category.assoc,
    Scheme.Hom.appLE_comp_appLE, ← Scheme.Opens.ι_comp_over, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl

variable [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T2Space K]

/-- Let `U ⊆ X` be an affine open whose coordinate ring is generated over `K` by sections
`yᵢ ∈ Γ(X, U)`. For `C ⊆ K^ι` compact, the points of `U(K)` at which `(yᵢ)` takes a value in `C`
form a compact subset of `X(K)`. -/
theorem isCompact_setOf_eval_mem {U : X.Opens} (hU : IsAffineOpen U) {ι : Type*}
    (y : ι → Γ(X, U))
    (hy : Subring.closure (Set.range (structureRingHomOpens (K := K) U) ∪ Set.range y) = ⊤)
    {C : Set (ι → K)} (hC : IsCompact C) :
    IsCompact {p : UnderlyingSpace K X |
      ∃ hp : ⊤ ≤ p.toHom ⁻¹ᵁ U, (fun i ↦ eval p hp (y i)) ∈ C} := by
  have : IsAffine U.toScheme := hU
  let φ := U.ι.appLE U ⊤ U.ι_preimage_self.ge
  have hgen : Subring.closure (Set.range (structureRingHom K U.toScheme) ∪
      Set.range (fun i ↦ φ (y i))) = ⊤ := by
    have : Set.range (structureRingHom K U.toScheme) ∪ Set.range (fun i ↦ φ (y i)) =
        φ.hom '' (Set.range (structureRingHomOpens (K := K) U) ∪ Set.range y) := by
      rw [Set.image_union, ← Set.range_comp, ← Set.range_comp, structureRingHom_opens]
      rfl
    rw [this, ← RingHom.map_closure, hy, ← RingHom.range_eq_map, RingHom.range_eq_top]
    exact (ConcreteCategory.bijective_of_isIso φ).2
  have heval : ∀ (q : UnderlyingSpace K U.toScheme) hp,
      (fun i ↦ eval (mapFun U.ι q) hp (y i)) = evalFamily (fun i ↦ φ (y i)) q :=
    fun q hp ↦ funext fun i ↦ eval_mapFun_ι U q hp (y i)
  have hrange : ∀ p, p ∈ Set.range (mapFun (K := K) U.ι) ↔ ⊤ ≤ p.toHom ⁻¹ᵁ U := fun p ↦ by
    rw [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
    exact Iff.rfl
  have hset : {p : UnderlyingSpace K X |
      ∃ hp : ⊤ ≤ p.toHom ⁻¹ᵁ U, (fun i ↦ eval p hp (y i)) ∈ C} =
      map U.ι '' (evalFamily (fun i ↦ φ (y i)) ⁻¹' C) := by
    ext p
    constructor
    · rintro ⟨hp, hpC⟩
      obtain ⟨q, rfl⟩ := (hrange p).mpr hp
      exact ⟨q, (heval q hp ▸ hpC : evalFamily _ q ∈ C), rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(hrange _).mp ⟨q, rfl⟩, (heval q _).symm ▸ hq⟩
  rw [hset]
  exact ((isClosedEmbedding_evalFamily (K := K) (fun i ↦ φ (y i)) hgen).isCompact_preimage
    hC).image (map U.ι).continuous

end AffineOpen

section ProjectiveSpace

open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K] (n : ℕ)

/-- The standard chart `Uᵢ = D₊(xᵢ)` of `ℙⁿ_K`. -/
abbrev projectiveSpaceStdChart (i : Fin (n + 1)) :
    (AlgebraicGeometry.Proj (polyGrading K n)).Opens :=
  Proj.basicOpen (polyGrading K n) (MvPolynomial.X i)

/-- The affine coordinate `x_j / xᵢ` on the standard chart `Uᵢ` of `ℙⁿ_K`. -/
def projectiveSpaceStdCoord (i j : Fin (n + 1)) :
    Γ(AlgebraicGeometry.Proj (polyGrading K n), projectiveSpaceStdChart K n i) :=
  (Proj.awayToSection (polyGrading K n) (MvPolynomial.X i)).hom
    (Away.mk (polyGrading K n) (X_mem_one K n i) 1 (MvPolynomial.X j) (X_mem_smul K n j))

variable {K n}

/-- On the chart `Uᵢ`, the affine coordinate `xᵢ / xᵢ` is `1`. -/
lemma projectiveSpaceStdCoord_self (i : Fin (n + 1)) :
    projectiveSpaceStdCoord K n i i = 1 := by
  rw [projectiveSpaceStdCoord]
  convert map_one (Proj.awayToSection (polyGrading K n) (MvPolynomial.X i)).hom
  ext
  rw [Away.val_mk, HomogeneousLocalization.val_one, ← Localization.mk_one,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

/-- The locus in `Uᵢ` where `x_k / xᵢ` does not vanish is `Uᵢ ∩ U_k`. -/
lemma basicOpen_projectiveSpaceStdCoord (i k : Fin (n + 1)) :
    (AlgebraicGeometry.Proj (polyGrading K n)).basicOpen (projectiveSpaceStdCoord K n i k) =
      projectiveSpaceStdChart K n i ⊓ projectiveSpaceStdChart K n k :=
  Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk _ (X_mem_one K n i) one_pos 1
    (MvPolynomial.X k) (X_mem_smul K n k)

/-- On the standard chart `Uᵢ`, the structure map from `K` is the coefficient map into the
homogeneous localization `K[x₀, …, xₙ]_{(xᵢ)}`, for the structure morphism `projToSpecCoeff`. -/
lemma structureRingHomOpens_projectiveSpaceStdChart
    [hO : (AlgebraicGeometry.Proj (polyGrading K n)).Over (Spec (.of K))]
    (hP : (AlgebraicGeometry.Proj (polyGrading K n) ↘ Spec (.of K)) = projToSpecCoeff K n)
    (i : Fin (n + 1)) (c : K) :
    structureRingHomOpens (projectiveSpaceStdChart K n i) c =
      (Proj.awayToSection (polyGrading K n) (MvPolynomial.X i)).hom (coeffToAway K n i c) := by
  obtain ⟨f⟩ := hO
  change f = _ at hP
  subst hP
  have hV := Proj.isAffineOpen_basicOpen (polyGrading K n) (MvPolynomial.X i)
    (X_mem_one K n i) one_pos
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec (projToSpecCoeff K n)
    (isAffineOpen_top _) hV (le_top.trans (Scheme.Hom.preimage_top _).ge)
  rw [← Stacks.ProjChartBasicOpen.SpecMap_awayToSection_awayι _ (X_mem_one K n i) one_pos] at h1
  rw [Category.assoc, projToSpecCoeff,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h1
  have h2 := congrArg (fun φ ↦ φ.hom c) (Spec.map_injective h1)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  have h3 : GradedRing.projZeroRingHom' (polyGrading K n)
      (algebraMap K (MvPolynomial (Fin (n + 1)) K) c) = algebraMap K (polyGrading K n 0) c :=
    GradedRing.projZeroRingHom'_apply_coe (polyGrading K n) (algebraMap K (polyGrading K n 0) c)
  rwa [h3] at h2

/-- On `Uᵢ ∩ U_k = D₊(xᵢ x_k)` the affine coordinates satisfy
`x_j / xᵢ = (x_k / xᵢ)(x_j / x_k)`. -/
lemma projectiveSpaceStdCoord_mul (i j k : Fin (n + 1)) :
    (AlgebraicGeometry.Proj (polyGrading K n)).presheaf.map
      (homOfLE (Proj.basicOpen_mono (polyGrading K n) _ _
        ⟨MvPolynomial.X k, rfl⟩ : Proj.basicOpen (polyGrading K n)
          (MvPolynomial.X i * MvPolynomial.X k) ≤ _)).op (projectiveSpaceStdCoord K n i j) =
      (AlgebraicGeometry.Proj (polyGrading K n)).presheaf.map
      (homOfLE (Proj.basicOpen_mono (polyGrading K n) _ _
        ⟨MvPolynomial.X k, rfl⟩ : Proj.basicOpen (polyGrading K n)
          (MvPolynomial.X i * MvPolynomial.X k) ≤ _)).op (projectiveSpaceStdCoord K n i k) *
      (AlgebraicGeometry.Proj (polyGrading K n)).presheaf.map
      (homOfLE (Proj.basicOpen_mono (polyGrading K n) _ _
        ⟨MvPolynomial.X i, mul_comm _ _⟩ : Proj.basicOpen (polyGrading K n)
          (MvPolynomial.X i * MvPolynomial.X k) ≤ _)).op (projectiveSpaceStdCoord K n k j) := by
  have hi := congrArg (fun φ ↦ φ.hom) (Proj.awayMap_awayToSection (polyGrading K n)
    (f := MvPolynomial.X i) (X_mem_one K n k) (rfl : MvPolynomial.X i * MvPolynomial.X k = _))
  have hk := congrArg (fun φ ↦ φ.hom) (Proj.awayMap_awayToSection (polyGrading K n)
    (f := MvPolynomial.X k) (X_mem_one K n i)
    (mul_comm _ _ : MvPolynomial.X i * MvPolynomial.X k = _))
  simp only [CommRingCat.hom_comp] at hi hk
  simp only [projectiveSpaceStdCoord]
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.comp_apply, ← hi, ← hk,
    RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
  congr 1
  simp only [CommRingCat.hom_ofHom, awayMap_mk]
  ext
  simp only [Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]; ring⟩

/-- The coordinate ring of `Uᵢ` is generated over `K` by the affine coordinates `x_j / xᵢ`. -/
lemma closure_projectiveSpaceStdCoord
    [(AlgebraicGeometry.Proj (polyGrading K n)).Over (Spec (.of K))]
    (hP : (AlgebraicGeometry.Proj (polyGrading K n) ↘ Spec (.of K)) = projToSpecCoeff K n)
    (i : Fin (n + 1)) :
    Subring.closure (Set.range (structureRingHomOpens (K := K) (projectiveSpaceStdChart K n i)) ∪
      Set.range (projectiveSpaceStdCoord K n i)) = ⊤ := by
  let φ := (Proj.awayToSection (polyGrading K n) (MvPolynomial.X i)).hom
  have hφ : Function.Surjective φ := by
    have := (ConcreteCategory.bijective_of_isIso
      (Proj.basicOpenIsoAway (polyGrading K n) (MvPolynomial.X i) (X_mem_one K n i)
        one_pos).hom).2
    rwa [Proj.basicOpenIsoAway_hom] at this
  have hA : Subring.closure (Set.range (coeffToAway K n i) ∪
      Set.range (fun j ↦ Away.mk (polyGrading K n) (X_mem_one K n i) 1 (MvPolynomial.X j)
        (X_mem_smul K n j))) = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨P, rfl⟩ := chartHom_surjective K n i z
    induction P using MvPolynomial.induction_on with
    | C a => exact Subring.subset_closure (Or.inl ⟨a, (chartHom_C K n i a).symm⟩)
    | add p q hp hq =>
      rw [map_add]
      exact Subring.add_mem _ (hp trivial) (hq trivial)
    | mul_X p j hp =>
      rw [map_mul, chartHom_X]
      exact Subring.mul_mem _ (hp trivial) (Subring.subset_closure (Or.inr ⟨j.1, rfl⟩))
  have : Set.range (structureRingHomOpens (K := K) (projectiveSpaceStdChart K n i)) ∪
      Set.range (projectiveSpaceStdCoord K n i) =
      φ '' (Set.range (coeffToAway K n i) ∪
        Set.range (fun j ↦ Away.mk (polyGrading K n) (X_mem_one K n i) 1 (MvPolynomial.X j)
          (X_mem_smul K n j))) := by
    rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply]
    exact ⟨fun ⟨c, hc⟩ ↦ ⟨c, by rw [← hc, structureRingHomOpens_projectiveSpaceStdChart hP]⟩,
      fun ⟨c, hc⟩ ↦ ⟨c, by rw [← hc, structureRingHomOpens_projectiveSpaceStdChart hP]⟩⟩
  rwa [this, ← RingHom.map_closure, hA, ← RingHom.range_eq_map, RingHom.range_eq_top]

end ProjectiveSpace

section Compact

open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [NormedField K] [ProperSpace K]

/-- **`ℙⁿ(K)` is compact** for a normed field `K` which is a proper metric space, such as `ℂ`.
Here `ℙⁿ_K = Proj K[x₀, …, xₙ]` is a scheme over `K` through its structure morphism
`projToSpecCoeff K n`. -/
theorem compactSpace_projectiveSpace (n : ℕ)
    [(AlgebraicGeometry.Proj (polyGrading K n)).Over (Spec (.of K))]
    (hP : (AlgebraicGeometry.Proj (polyGrading K n) ↘ Spec (.of K)) = projToSpecCoeff K n) :
    CompactSpace (UnderlyingSpace K (AlgebraicGeometry.Proj (polyGrading K n))) := by
  refine compactSpace_of_charts (projectiveSpaceStdChart K n) (iSup_basicOpen_X_eq_top K n)
    (projectiveSpaceStdCoord K n) (fun i p hp ↦ ?_) (fun i k p hp h ↦ ?_)
    (fun i k j p hpi hpk ↦ ?_) (fun i ↦ ?_)
  · rw [projectiveSpaceStdCoord_self, ← evalRingHom_apply, map_one]
  · have := (top_le_preimage_basicOpen_iff p hp _).mpr h
    rw [basicOpen_projectiveSpaceStdCoord] at this
    exact this.trans (Scheme.Hom.preimage_mono _ inf_le_right)
  · have hW : ⊤ ≤ p.toHom ⁻¹ᵁ Proj.basicOpen (polyGrading K n)
        (MvPolynomial.X i * MvPolynomial.X k) := by
      rw [Proj.basicOpen_mul]
      exact fun x hx ↦ ⟨hpi hx, hpk hx⟩
    have e1 := eval_restrict (Proj.basicOpen_mono (polyGrading K n) _ _
      ⟨MvPolynomial.X k, rfl⟩) p hW (projectiveSpaceStdCoord K n i j)
    have e2 := eval_restrict (Proj.basicOpen_mono (polyGrading K n) _ _
      ⟨MvPolynomial.X k, rfl⟩) p hW (projectiveSpaceStdCoord K n i k)
    have e3 := eval_restrict (Proj.basicOpen_mono (polyGrading K n) _ _
      ⟨MvPolynomial.X i, mul_comm _ _⟩) p hW (projectiveSpaceStdCoord K n k j)
    rw [← e1, ← e2, ← e3, projectiveSpaceStdCoord_mul, ← evalRingHom_apply, map_mul]
    rfl
  · have hC : IsCompact {v : Fin (n + 1) → K | ∀ j, ‖v j‖ ≤ 1} := by
      convert isCompact_univ_pi (fun _ : Fin (n + 1) ↦ isCompact_closedBall (0 : K) 1) using 1
      ext v
      simp
    exact isCompact_setOf_eval_mem (Proj.isAffineOpen_basicOpen (polyGrading K n)
      (MvPolynomial.X i) (X_mem_one K n i) one_pos) _ (closure_projectiveSpaceStdCoord hP i) hC

end Compact

end UnderlyingSpace

end MMP
