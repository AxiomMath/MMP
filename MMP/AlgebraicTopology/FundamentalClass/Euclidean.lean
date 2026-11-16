module

public import MMP.AlgebraicTopology.FundamentalClass.RealLine
public import MMP.AlgebraicTopology.FundamentalClass.Homeomorphism
public import Mathlib.Topology.Algebra.Module.FiniteDimension
/-!
# The fundamental class of `ℝ^N`, in every universe

Borel–Moore homology takes the space and the coefficient ring in one universe, so for coefficients
`R : Type u` the space `ℝ^N` is taken as `Fin N → ULift.{u} ℝ` (a copy of `ℝ^N` in the universe
`u`; at `u = 0` it is `Fin N → ULift.{0} ℝ`). Oriented by its standard basis, it has a Borel–Moore
fundamental class `μ_{ℝ^N} ∈ H_N ℝ^N`, built by induction on `N`: `μ_{ℝ^0}` is the class of the
point, and `μ_{ℝ^{N+1}}` is the push-forward of the exterior product `μ_{ℝ^N} × μ_ℝ` along the
homeomorphism `ℝ^N × ℝ ≅ ℝ^{N+1}`, `(w, a) ↦ (w₀, …, w_{N-1}, a)`. Here `μ_ℝ` is the class of the
locally finite cycle `∑_{n ∈ ℤ} [n, n + 1]` of the lifted line `ULift ℝ`; its local computation is
pulled back to `ℝ` (`MMP.FundamentalClass.finsum_relCocycle_segSimplex`). By the product formula
(`MMP.IsFundamentalClass.exteriorProduct`) and the invariance of fundamental classes under
orientation-preserving homeomorphisms (`MMP.IsFundamentalClass.pushforward_homeomorph`), it is the
fundamental class. Transporting along a linear isomorphism, every finite-dimensional real normed
space `V : Type u` oriented by a basis has a fundamental class.

A linear isomorphism `L : H ≃ₗ H'` is orientation preserving from the orientation of a basis `b`
to that of the image basis `L b`: it carries positively oriented affine simplices to positively
oriented affine simplices.

## Main definitions

* `MMP.FundamentalClass.liftLineClass`: `μ_ℝ ∈ H_1 (ULift ℝ)`.
* `MMP.FundamentalClass.liftEuclideanBasis`: the standard basis of
  `Fin N → ULift ℝ`.
* `MMP.FundamentalClass.pointClass`: the class of the point `ℝ^0`.
* `MMP.FundamentalClass.snocHomeomorph`: `ℝ^N × ℝ ≅ ℝ^{N+1}`.
* `MMP.FundamentalClass.euclideanClass`: `μ_{ℝ^N} ∈ H_N ℝ^N`.

## Main results

* `MMP.ThomClass.IsOrientedSimplexAroundZero.map`: linear isomorphisms preserve
  oriented simplices, for the image basis.
* `MMP.FundamentalClass.isOrientationPreserving_of_linearEquiv`: a homeomorphism
  which is a linear isomorphism in charts preserves orientations.
* `MMP.FundamentalClass.isFundamentalClass_liftLineClass`.
* `MMP.FundamentalClass.isFundamentalClass_euclideanClass`: `μ_{ℝ^N}` is the
  fundamental class of `ℝ^N` for the orientation of the standard basis.
* `MMP.FundamentalClass.exists_isFundamentalClass_of_basis`: a fundamental class of
  a finite-dimensional real normed space oriented by any basis, in every universe.

## References

* [B. Iversen, *Cohomology of Sheaves*][iversen1986], IX.4.
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology Opposite Simplicial TensorProduct
open MMP.SingularChain MMP.SingularCochain
  MMP.ThomClass MMP.LocallyFiniteChain
  MMP.borelMooreHomology

universe u

namespace MMP

namespace ThomClass

variable {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']

/-- A linear isomorphism `L` carries an oriented simplex around `0` for `b` to an oriented simplex
around `0` for the image basis `L b`. -/
lemma IsOrientedSimplexAroundZero.map {n : ℕ} {b : Module.Basis (Fin n) ℝ V}
    {w : Fin (n + 1) → V} (h : IsOrientedSimplexAroundZero b w) (L : V ≃ₗ[ℝ] V') :
    IsOrientedSimplexAroundZero (b.map L) (L ∘ w) := by
  obtain ⟨⟨t, ht, hs, hc⟩, hdet⟩ := h
  refine ⟨⟨t, ht, hs, ?_⟩, ?_⟩
  · simpa [map_sum, map_smul] using congrArg L hc
  · rw [Module.Basis.det_map]
    convert hdet using 2
    funext k
    simp

end ThomClass

namespace FundamentalClass

section Orientation

variable {H H' : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H] [AddCommGroup H'] [Module ℝ H'] [TopologicalSpace H'] [ContinuousAdd H']
  [ContinuousSMul ℝ H'] {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- A homeomorphism `φ : M ≃ₜ H'` which in every chart `e` of `M` is a linear isomorphism `L`
(`φ ∘ e⁻¹ = L` on the image of `e`) is orientation preserving from the orientation of a basis `b`
to that of `L b`, `H'` being charted by itself. -/
theorem isOrientationPreserving_of_linearEquiv {H' : Type u} [AddCommGroup H'] [Module ℝ H']
    [TopologicalSpace H'] [ContinuousAdd H'] [ContinuousSMul ℝ H'] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ H) (L : H ≃ₗ[ℝ] H') (φ : M ≃ₜ H')
    (hφ : ∀ e ∈ atlas H M, ∀ y ∈ e.target, φ (e.symm y) = L y) :
    IsOrientationPreserving (M' := H') b (b.map L) φ := by
  intro e he e' he' x hx _ v hv hvt v' hv' hvt'
  rw [chartedSpaceSelf_atlas] at he'
  subst he'
  have hφx : φ x = L (e x) := by
    rw [← hφ e he (e x) (e.map_source hx), e.left_inv hx]
  refine isLocallyHomologous_of_isOrientedSimplexAroundZero (OpenPartialHomeomorph.refl H')
    (x := φ x) (mem_univ _) (b := b.map L) (v := L ∘ v) ?_ (fun _ _ ↦ mem_univ _) hv' hvt'
    (fun t ↦ ?_) (fun t ↦ rfl)
  · convert hv.map L using 1
    funext k
    simp [hφx]
  · change φ (e.symm (affineSimplex v t)) = affineSimplex (L ∘ v) t
    rw [hφ e he _ (hvt ⟨t, rfl⟩), affineSimplex_apply, affineSimplex_apply, map_sum]
    simp

end Orientation

section ULiftLine

/-- `x ↦ ULift.up x`, as a continuous map `ℝ → ULift ℝ`. -/
def upMap : C(ℝ, ULift.{u} ℝ) := ⟨ULift.up, continuous_uliftUp⟩

/-- The segment `[a, b]` of the lifted line `ULift ℝ`. -/
def liftSegSimplex (a b : ℝ) : Simplex (ULift.{u} ℝ) 1 := upMap.comp (segSimplex a b)

/-- The affine `1`-simplex with vertices `v 0`, `v 1` of `ULift ℝ` is the segment
`[(v 0).down, (v 1).down]`. -/
lemma affineSimplex_eq_liftSegSimplex (v : Fin 2 → ULift.{u} ℝ) :
    affineSimplex v = liftSegSimplex (v 0).down (v 1).down := by
  ext1 t
  apply ULift.ext
  simp [liftSegSimplex, upMap, segSimplex, affineSimplex_apply, Fin.sum_univ_two]

variable {R : Type*} [CommRing R] {x : ULift.{u} ℝ}

/-- The pull-back `φ ∘ (up ∘ -)` of a relative cocycle of `(ULift ℝ, ULift ℝ - x)` is a relative
cocycle of `(ℝ, ℝ - x)`. -/
lemma comp_upMap_mem_relCocycles {φ : Simplex (ULift.{u} ℝ) 1 → R}
    (hφ : φ ∈ relCocycles R ({x}ᶜ : Set (ULift.{u} ℝ)) 1) :
    (fun τ : Simplex ℝ 1 ↦ φ (upMap.comp τ)) ∈ relCocycles R ({x.down}ᶜ : Set ℝ) 1 := by
  refine ⟨fun τ hτ ↦ hφ.1 _ ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩ h
    exact hτ ⟨t, rfl⟩ (by rw [← h]; rfl)
  · refine LinearMap.mem_ker.2 (funext fun σ ↦ ?_)
    have h := congrFun (LinearMap.mem_ker.1 hφ.2) (upMap.comp σ)
    rwa [coboundary_apply] at h ⊢

end ULiftLine

section ULiftCycle

variable (R : Type u) [CommRing R]

/-- The segment `[n, n + 1]` of `ULift ℝ`, as a `1`-simplex of its singular simplicial set. -/
def liftIntegerSegment (n : ℤ) : (TopCat.toSSet.obj (TopCat.of (ULift.{u} ℝ))).obj (op ⦋1⦌) :=
  (SingularCochain.simplexEquiv (TopCat.of (ULift.{u} ℝ)) 1).symm (liftSegSimplex n (n + 1))

/-- The segments `[n, n + 1]`, `n ∈ ℤ`, are pairwise distinct simplices. -/
lemma liftIntegerSegment_injective : Function.Injective liftIntegerSegment.{u} := by
  intro m n h
  have h' := congrArg (fun σ ↦ ((SingularCochain.simplexEquiv (TopCat.of (ULift.{u} ℝ)) 1 σ :
    Simplex (ULift.{u} ℝ) 1) (stdSimplex.vertex 0)).down) h
  simp only [liftIntegerSegment, Equiv.apply_symm_apply] at h'
  change segSimplex _ _ (stdSimplex.vertex 0) = segSimplex _ _ (stdSimplex.vertex 0) at h'
  rw [segSimplex_vertex_zero, segSimplex_vertex_zero] at h'
  exact_mod_cast h'

/-- The image of `[n, n + 1]` lies in the interval `[n, n + 1]` of `ULift ℝ`. -/
lemma singularSimplexImage_liftIntegerSegment_subset (n : ℤ) :
    singularSimplexImage (TopCat.of (ULift.{u} ℝ)) (liftIntegerSegment n) ⊆
      ULift.down ⁻¹' Icc (n : ℝ) (n + 1) := by
  rw [← uIcc_of_le (by linarith), ← range_simplexEquiv]
  intro y hy
  obtain ⟨t, rfl⟩ := hy
  exact range_segSimplex_subset _ _ ⟨t, by rw [liftIntegerSegment, Equiv.apply_symm_apply]; rfl⟩

open Classical in
/-- The coefficients of `∑_{n ∈ ℤ} [n, n + 1]` on `ULift ℝ`. -/
def liftLineCycleFun : (TopCat.toSSet.obj (TopCat.of (ULift.{u} ℝ))).obj (op ⦋1⦌) → R :=
  fun σ ↦ if σ ∈ range liftIntegerSegment then 1 else 0

/-- The coefficient of `[n, n + 1]` in `∑_{n ∈ ℤ} [n, n + 1]` is `1`. -/
lemma liftLineCycleFun_liftIntegerSegment (n : ℤ) :
    liftLineCycleFun R (liftIntegerSegment n) = 1 := by
  simp [liftLineCycleFun]

/-- The support of `∑_{n ∈ ℤ} [n, n + 1]` consists of segments `[n, n + 1]`. -/
lemma support_liftLineCycleFun_subset :
    Function.support (liftLineCycleFun R) ⊆ range liftIntegerSegment := fun σ hσ ↦ by
  by_contra h
  exact hσ (by simp [liftLineCycleFun, h])

/-- The support of `∑_{n ∈ ℤ} [n, n + 1]` is locally finite in `ULift ℝ`. -/
lemma isLocallyFiniteSet_liftLineCycleFun :
    IsLocallyFiniteSet (singularSimplexImage (TopCat.of (ULift.{u} ℝ)))
      (Function.support (liftLineCycleFun R)) := fun x ↦ by
  refine ⟨ULift.down ⁻¹' Ioo (x.down - 1) (x.down + 1),
    continuous_uliftDown.continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
  refine ((Set.finite_Ioo (⌊x.down⌋ - 2) (⌊x.down⌋ + 2)).image liftIntegerSegment).subset ?_
  rintro σ ⟨hσ, y, hy, hyV⟩
  obtain ⟨n, rfl⟩ := support_liftLineCycleFun_subset R hσ
  have hn := singularSimplexImage_liftIntegerSegment_subset n hy
  refine ⟨n, ⟨?_, ?_⟩, rfl⟩
  · have h1 : ((⌊x.down⌋ - 2 : ℤ) : ℝ) < n := by
      push_cast
      linarith [Int.floor_le x.down, hn.2, hyV.1]
    exact_mod_cast h1
  · have h1 : (n : ℝ) < ((⌊x.down⌋ + 2 : ℤ) : ℝ) := by
      push_cast
      linarith [Int.lt_floor_add_one x.down, hn.1, hyV.2]
    exact_mod_cast h1

/-- The locally finite chain `∑_{n ∈ ℤ} [n, n + 1]` of `ULift ℝ`. -/
def liftLineChain : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ))).X 1 :=
  (⟨liftLineCycleFun R, isLocallyFiniteSet_liftLineCycleFun R⟩ :
    lfChains R (ModuleCat.of R R) (singularSimplexImage (TopCat.of (ULift.{u} ℝ))))

/-- A finite sum over `1`-simplices of `ULift ℝ` of a function supported on the segments
`[n, n + 1]` is the sum over `n ∈ ℤ` of its values on them. -/
lemma finsum_eq_finsum_liftIntegerSegment {M : Type*} [AddCommMonoid M]
    (f : (TopCat.toSSet.obj (TopCat.of (ULift.{u} ℝ))).obj (op ⦋1⦌) → M)
    (hf : Function.support f ⊆ range liftIntegerSegment) :
    ∑ᶠ σ, f σ = ∑ᶠ n : ℤ, f (liftIntegerSegment n) := by
  rw [← finsum_mem_range liftIntegerSegment_injective, finsum_mem_def,
    Set.indicator_eq_self.2 hf]

/-- The faces of `[n, n + 1]` are the points `n + 1` and `n`. -/
lemma δ_liftIntegerSegment (i : Fin 2) (n : ℤ) :
    (SingularCochain.simplexEquiv (TopCat.of (ULift.{u} ℝ)) _
      ((TopCat.toSSet.obj (TopCat.of (ULift.{u} ℝ))).δ i (liftIntegerSegment n)) :
      Simplex (ULift.{u} ℝ) 0) = upMap.comp (affineSimplex ![(n : ℝ) + i.rev]) := by
  rw [toSSetObjEquiv_δ]
  simp only [liftIntegerSegment, Equiv.apply_symm_apply]
  change (upMap.comp (segSimplex _ _)).comp _ = _
  rw [ContinuousMap.comp_assoc, segSimplex]
  erw [affineSimplex_comp_face]
  congr 2
  funext j
  fin_cases i <;> fin_cases j <;> simp

/-- `∑_{n ∈ ℤ} [n, n + 1]` is a cycle. -/
lemma d_liftLineChain :
    ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ))).d 1 0).hom
      (liftLineChain R) = 0 := by
  classical
  apply Subtype.ext
  rw [borelMooreChainComplex_d_apply]
  funext τ
  have hpush : ∀ i : Fin 2, pushforwardFun ((TopCat.toSSet.obj (TopCat.of (ULift.{u} ℝ))).δ i)
      (liftLineCycleFun R) τ = ∑ᶠ n : ℤ,
        if upMap.comp (affineSimplex ![(n : ℝ) + i.rev]) =
          (SingularCochain.simplexEquiv (TopCat.of (ULift.{u} ℝ)) _ τ : Simplex (ULift.{u} ℝ) 0)
        then (1 : R) else 0 := by
    intro i
    rw [pushforwardFun, finsum_eq_finsum_liftIntegerSegment]
    · refine finsum_congr fun n ↦ ?_
      rw [liftLineCycleFun_liftIntegerSegment, ← δ_liftIntegerSegment]
      exact if_congr (SingularCochain.simplexEquiv (TopCat.of (ULift.{u} ℝ)) _).apply_eq_iff_eq.symm rfl rfl
    · intro σ hσ
      by_contra h
      exact hσ (by simp [liftLineCycleFun, h])
  change ∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • pushforwardFun _ (liftLineCycleFun R) τ = 0
  rw [Fin.sum_univ_two, hpush, hpush]
  have hshift : (∑ᶠ n : ℤ, if upMap.comp (affineSimplex ![(n : ℝ) + (0 : Fin 2).rev]) =
      (SingularCochain.simplexEquiv (TopCat.of (ULift.{u} ℝ)) _ τ : Simplex (ULift.{u} ℝ) 0) then (1 : R)
        else 0) =
      ∑ᶠ n : ℤ, if upMap.comp (affineSimplex ![(n : ℝ) + (1 : Fin 2).rev]) =
        (SingularCochain.simplexEquiv (TopCat.of (ULift.{u} ℝ)) _ τ : Simplex (ULift.{u} ℝ) 0) then (1 : R)
          else 0 := by
    conv_rhs => rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
    refine finsum_congr fun n ↦ ?_
    simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
    congr 4
    simp [Fin.rev]
  rw [hshift]
  simp

/-- The cycle `∑_{n ∈ ℤ} [n, n + 1]` of `ULift ℝ`. -/
def liftLineCycle :
    (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ))).cycles 1 :=
  ((borelMooreChainComplex R (ModuleCat.of R R)
    (TopCat.of (ULift.{u} ℝ))).sc 1).moduleCatCyclesIso.inv.hom
    ⟨liftLineChain R, by
      change ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ))).d 1
        ((ComplexShape.down ℕ).next 1)).hom (liftLineChain R) = 0
      rw [ChainComplex.next_nat_succ]
      exact d_liftLineChain R⟩

/-- The underlying chain of the cycle `liftLineCycle R` is `liftLineChain R`. -/
lemma iCycles_liftLineCycle :
    (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ))).iCycles 1
      (liftLineCycle R) = liftLineChain R := by
  rw [← coe_moduleCatCyclesIso_hom, liftLineCycle]
  erw [Iso.inv_hom_id_apply]

/-- The fundamental class `μ ∈ H_1 (ULift ℝ)`: the class of `∑_{n ∈ ℤ} [n, n + 1]`. -/
def liftLineClass : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ)) (1 : ℕ) :=
  (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ)) 1).inv.hom
    ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ))).homologyπ 1
      (liftLineCycle R))

variable {R}

/-- The pairing of `∑_{n ∈ ℤ} [n, n + 1]` with a cochain `φ` is `∑_{n ∈ ℤ} φ [n, n + 1]`. -/
lemma localPairing_liftLineChain (φ : Simplex (TopCat.of (ULift.{u} ℝ)) 1 → R) :
    localPairing ((liftLineChain R).1 :
      (TopCat.toSSet.obj (TopCat.of (ULift.{u} ℝ))).obj (op ⦋1⦌) → R) φ =
      ∑ᶠ n : ℤ, φ (liftSegSimplex n (n + 1)) := by
  rw [localPairing, finsum_eq_finsum_liftIntegerSegment]
  · refine finsum_congr fun n ↦ ?_
    change liftLineCycleFun R (liftIntegerSegment n) * _ = _
    rw [liftLineCycleFun_liftIntegerSegment, one_mul]
    simp [liftIntegerSegment]
  · intro σ hσ
    by_contra h
    exact hσ (by simp [liftLineChain, liftLineCycleFun, h])

/-- The class of `∑ [n, n + 1]` is locally, at `x`, the class of every segment `[a, b]` with
`a < x < b`. -/
theorem isLocallyClassOf_liftLineClass {x : ULift.{u} ℝ} {a b : ℝ} (ha : a < x.down)
    (hb : x.down < b) :
    IsLocallyClassOf R (liftLineClass R) (x : TopCat.of (ULift.{u} ℝ)) (liftSegSimplex a b) := by
  intro z hz φ hφ
  have hz' : (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ))).homologyπ 1 z =
      (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (ULift.{u} ℝ))).homologyπ 1
        (liftLineCycle R) := by
    rw [hz, liftLineClass]
    exact Iso.inv_hom_id_apply _ _
  rw [localPairing_eq_of_homologyπ_eq hz' hφ, iCycles_liftLineCycle,
    localPairing_liftLineChain]
  exact finsum_relCocycle_segSimplex (comp_upMap_mem_relCocycles hφ) ha hb

end ULiftCycle

section ULiftFundamental

/-- The standard basis `1` of the lifted line `ULift ℝ`. -/
def liftLineBasis : Module.Basis (Fin 1) ℝ (ULift.{u} ℝ) :=
  (Module.Basis.singleton (Fin 1) ℝ).map ULift.moduleEquiv.symm

/-- The coordinate of `w : ULift ℝ` in the basis `liftLineBasis` is `w.down`. -/
@[simp]
lemma liftLineBasis_repr (w : ULift.{u} ℝ) (i : Fin 1) : liftLineBasis.repr w i = w.down := by
  simp [liftLineBasis, ULift.moduleEquiv]
  rfl

variable {R : Type u} [CommRing R]

/-- **The fundamental class of the lifted line.** The class of `∑_{n ∈ ℤ} [n, n + 1]` is the
fundamental class of `ULift ℝ` for the orientation of its standard basis. -/
theorem isFundamentalClass_liftLineClass :
    IsFundamentalClass (H := ULift.{u} ℝ) (M := ULift.{u} ℝ) R liftLineBasis
      (liftLineClass R) := by
  intro e he x v hv hvt
  rw [chartedSpaceSelf_atlas] at he
  subst he
  apply IsLocallyClassOf.restrict
  have hΔ : inclChainSimplex (chartOpens (OpenPartialHomeomorph.refl (ULift.{u} ℝ)))
      (chartSimplex (OpenPartialHomeomorph.refl (ULift.{u} ℝ)) v hvt) =
        liftSegSimplex (v 0).down (v 1).down := by
    rw [← affineSimplex_eq_liftSegSimplex]
    rfl
  rw [hΔ]
  obtain ⟨⟨t, ht, hsum, hcomb⟩, hdet⟩ := hv
  simp only [OpenPartialHomeomorph.refl_apply, id_eq] at hcomb hdet
  rw [Module.Basis.det_apply, Matrix.det_unique] at hdet
  simp only [Module.Basis.toMatrix_apply, liftLineBasis_repr] at hdet
  have hcomb' := congrArg ULift.down hcomb
  rw [Fin.sum_univ_two] at hsum hcomb'
  simp only [ULift.add_down, ULift.smul_down, ULift.zero_down, smul_eq_mul] at hcomb'
  set x' : ULift.{u} ℝ := ((x : chartOpens (OpenPartialHomeomorph.refl (ULift.{u} ℝ))) :
    ULift.{u} ℝ)
  have hd : 0 < (v 1).down - (v 0).down := by
    change 0 < (v 1 - x').down - (v 0 - x').down at hdet
    simp only [ULift.sub_down] at hdet
    linarith
  simp only [ULift.sub_down] at hcomb'
  have hx0 : x'.down - (v 0).down = t 1 * ((v 1).down - (v 0).down) := by
    linear_combination -hcomb' - (x'.down - (v 0).down) * hsum
  have hx1 : (v 1).down - x'.down = t 0 * ((v 1).down - (v 0).down) := by
    linear_combination hcomb' - ((v 1).down - x'.down) * hsum
  refine isLocallyClassOf_liftLineClass (x := x') ?_ ?_
  · nlinarith [mul_pos (ht 1) hd]
  · nlinarith [mul_pos (ht 0) hd]

/-- The standard basis of `ℝ^N = Fin N → ULift ℝ`, a copy of `ℝ^N` in the universe `u`. -/
def liftEuclideanBasis (N : ℕ) : Module.Basis (Fin N) ℝ (Fin N → ULift.{u} ℝ) :=
  (Pi.basisFun ℝ (Fin N)).map (LinearEquiv.piCongrRight fun _ ↦ ULift.moduleEquiv.symm)

/-- The `i`-th vector of `liftEuclideanBasis N` is the indicator `Pi.single i (ULift.up 1)`. -/
lemma liftEuclideanBasis_apply (N : ℕ) (i : Fin N) :
    liftEuclideanBasis N i = Pi.single i (ULift.up 1) := by
  classical
  funext k
  simp only [liftEuclideanBasis, Module.Basis.map_apply, Pi.basisFun_apply,
    LinearEquiv.piCongrRight_apply]
  by_cases h : k = i
  · subst h
    simp
  · simp [h]
    rfl

end ULiftFundamental

section Point

variable (R : Type u) [CommRing R]

/-- The point `ℝ^0 = Fin 0 → ULift ℝ`, as a `0`-simplex of its singular simplicial set. -/
def pointSimplex : (TopCat.toSSet.obj (TopCat.of (Fin 0 → ULift.{u} ℝ))).obj (op ⦋0⦌) :=
  (SingularCochain.simplexEquiv (TopCat.of (Fin 0 → ULift.{u} ℝ)) 0).symm (ContinuousMap.const _ 0)

/-- The `0`-cycle `[pt]` of the point `ℝ^0`. -/
def pointCycle :
    (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (Fin 0 → ULift.{u} ℝ))).cycles 0 :=
  ((borelMooreChainComplex R (ModuleCat.of R R)
    (TopCat.of (Fin 0 → ULift.{u} ℝ))).sc 0).moduleCatCyclesIso.inv.hom
    ⟨singleChain R (pointSimplex), by
      change ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (Fin 0 → ULift.{u} ℝ))).d 0
        ((ComplexShape.down ℕ).next 0)).hom (singleChain R (pointSimplex)) = 0
      rw [ChainComplex.next_nat_zero,
        (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (Fin 0 → ULift.{u} ℝ))).shape 0 0
          (by simp)]
      rfl⟩

/-- The class of the point `ℝ^0` in `H_0 ℝ^0`. -/
def pointClass :
    borelMooreHomology R (ModuleCat.of R R) (TopCat.of (Fin 0 → ULift.{u} ℝ)) (0 : ℕ) :=
  (borelMooreHomologyIsoOfNat R (ModuleCat.of R R) (TopCat.of (Fin 0 → ULift.{u} ℝ)) 0).inv.hom
    ((borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (Fin 0 → ULift.{u} ℝ))).homologyπ 0
      (pointCycle R))

variable {R}

/-- The class of the point is locally the class of the (unique) `0`-simplex. -/
theorem isLocallyClassOf_pointClass (x : TopCat.of (Fin 0 → ULift.{u} ℝ))
    (Δ : Simplex (TopCat.of (Fin 0 → ULift.{u} ℝ)) 0) : IsLocallyClassOf R (pointClass R) x Δ := by
  classical
  intro z hz φ hφ
  have hz' : (borelMooreChainComplex R (ModuleCat.of R R)
      (TopCat.of (Fin 0 → ULift.{u} ℝ))).homologyπ 0 z =
      (borelMooreChainComplex R (ModuleCat.of R R) (TopCat.of (Fin 0 → ULift.{u} ℝ))).homologyπ 0
        (pointCycle R) := by
    rw [hz, pointClass]
    exact Iso.inv_hom_id_apply _ _
  have hi : (borelMooreChainComplex R (ModuleCat.of R R)
      (TopCat.of (Fin 0 → ULift.{u} ℝ))).iCycles 0 (pointCycle R) =
        singleChain R pointSimplex := by
    rw [← coe_moduleCatCyclesIso_hom, pointCycle]
    erw [Iso.inv_hom_id_apply]
  rw [localPairing_eq_of_homologyπ_eq hz' hφ, hi, localPairing, coe_singleChain,
    finsum_eq_single _ pointSimplex (fun σ hσ ↦ by rw [Pi.single_eq_of_ne hσ, zero_mul]),
    Pi.single_eq_same, one_mul]
  exact congrArg φ (Subsingleton.elim _ _)

/-- The class of the point is the fundamental class of `ℝ^0`. -/
theorem isFundamentalClass_pointClass :
    IsFundamentalClass (H := Fin 0 → ULift.{u} ℝ) (M := Fin 0 → ULift.{u} ℝ) R
      (liftEuclideanBasis 0) (pointClass R) := by
  intro e he x v hv hvt
  rw [chartedSpaceSelf_atlas] at he
  subst he
  exact IsLocallyClassOf.restrict _ (isLocallyClassOf_pointClass _ _)

end Point

section Euclidean

variable (N : ℕ)

/-- The linear isomorphism `ℝ^N × ℝ ≅ ℝ^{N+1}`, `(w, a) ↦ (w₀, …, w_{N-1}, a)`, on the model
space `ModelProd ℝ^N ℝ` of the product (`ℝ = ULift ℝ`, `ℝ^N = Fin N → ULift ℝ`). -/
def snocLinearEquiv :
    ModelProd (Fin N → ULift.{u} ℝ) (ULift.{u} ℝ) ≃ₗ[ℝ] (Fin (N + 1) → ULift.{u} ℝ) where
  toFun p := Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) (p : (Fin N → ULift.{u} ℝ) × ULift.{u} ℝ).1
    (p : (Fin N → ULift.{u} ℝ) × ULift.{u} ℝ).2
  invFun f := ((Fin.init f, f (Fin.last N)) : (Fin N → ULift.{u} ℝ) × ULift.{u} ℝ)
  map_add' p q := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [Fin.snoc_last, Pi.add_apply]
      rfl
    · simp only [Fin.snoc_castSucc, Pi.add_apply]
      rfl
  map_smul' r p := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [Fin.snoc_last, Pi.smul_apply, RingHom.id_apply]
      rfl
    · simp only [Fin.snoc_castSucc, Pi.smul_apply, RingHom.id_apply]
      rfl
  left_inv p := by
    change ((Fin.init (Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) _ _),
      Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) _ _ (Fin.last N)) :
      (Fin N → ULift.{u} ℝ) × ULift.{u} ℝ) = p
    rw [Fin.init_snoc, Fin.snoc_last]
    rfl
  right_inv f := Fin.snoc_init_self (α := fun _ ↦ ULift.{u} ℝ) f

/-- The homeomorphism `ℝ^N × ℝ ≅ ℝ^{N+1}`, `(w, a) ↦ (w₀, …, w_{N-1}, a)`. -/
def snocHomeomorph : ((Fin N → ULift.{u} ℝ) × ULift.{u} ℝ) ≃ₜ (Fin (N + 1) → ULift.{u} ℝ) where
  toFun p := Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) p.1 p.2
  invFun f := (Fin.init f, f (Fin.last N))
  left_inv p := by
    change (Fin.init (Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) _ _),
      Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) _ _ (Fin.last N)) = p
    rw [Fin.init_snoc, Fin.snoc_last]
  right_inv f := Fin.snoc_init_self (α := fun _ ↦ ULift.{u} ℝ) f
  continuous_toFun := Continuous.finSnoc continuous_fst continuous_snd
  continuous_invFun := (continuous_pi fun _ ↦ continuous_apply _).prodMk (continuous_apply _)

/-- The image of the product basis of `ℝ^N × ℝ` under `ℝ^N × ℝ ≅ ℝ^{N+1}` is the standard basis. -/
lemma map_snocLinearEquiv_basis :
    (((liftEuclideanBasis N).prod liftLineBasis).reindex finSumFinEquiv).map
      (snocLinearEquiv N) = liftEuclideanBasis.{u} (N + 1) := by
  classical
  refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
  rw [Module.Basis.map_apply, Module.Basis.reindex_apply, liftEuclideanBasis_apply]
  funext k
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [finSumFinEquiv_symm_last, Module.Basis.prod_apply]
    refine Fin.lastCases ?_ (fun l ↦ ?_) k
    · change Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) _ _ (Fin.last N) = _
      simp only [Fin.snoc_last, Sum.elim_inr, LinearMap.coe_inr, Pi.single_eq_same]
      simp [liftLineBasis]
    · change Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) _ _ (Fin.castSucc l) = _
      simp [Fin.castSucc_ne_last]
  · rw [finSumFinEquiv_symm_apply_castSucc, Module.Basis.prod_apply]
    refine Fin.lastCases ?_ (fun l ↦ ?_) k
    · change Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) _ _ (Fin.last N) = _
      simp [(Fin.castSucc_ne_last j).symm]
    · change Fin.snoc (α := fun _ ↦ ULift.{u} ℝ) _ _ (Fin.castSucc l) = _
      simp [liftEuclideanBasis_apply, Pi.single_apply, Fin.castSucc_inj]

variable (R : Type u) [CommRing R]

/-- The fundamental class `μ_{ℝ^N} ∈ H_N ℝ^N` of `ℝ^N = Fin N → ULift ℝ` (a copy of `ℝ^N` in
every universe): the class of the point for `N = 0`, and the push-forward of `μ_{ℝ^N} × μ_ℝ`
along `ℝ^N × ℝ ≅ ℝ^{N+1}`. -/
def euclideanClass (N : ℕ) :
    borelMooreHomology R (ModuleCat.of R R) (TopCat.of (Fin N → ULift.{u} ℝ)) (N : ℕ) :=
  match N with
  | 0 => pointClass R
  | m + 1 => borelMooreHomology.pushforward R (ModuleCat.of R R)
      (TopCat.ofHom (snocHomeomorph m : C((Fin m → ULift.{u} ℝ) × ULift.{u} ℝ,
        Fin (m + 1) → ULift.{u} ℝ)))
      (snocHomeomorph m).isProperMap (m + 1)
      (BorelMooreCross.congrDegree R _ (Nat.cast_add m 1).symm
        (borelMooreHomology.exteriorProduct R (TopCat.of (Fin m → ULift.{u} ℝ))
          (TopCat.of (ULift.{u} ℝ)) m 1 (euclideanClass m ⊗ₜ liftLineClass R)))

/-- **The fundamental class of `ℝ^N`.** `μ_{ℝ^N}` is the fundamental class of
`ℝ^N = Fin N → ULift ℝ` for the orientation of the standard basis. -/
theorem isFundamentalClass_euclideanClass (N : ℕ) :
    IsFundamentalClass (H := Fin N → ULift.{u} ℝ) (M := Fin N → ULift.{u} ℝ) R
      (liftEuclideanBasis N) (euclideanClass R N) := by
  induction N with
  | zero => exact isFundamentalClass_pointClass
  | succ m ih =>
    have h := ih.exteriorProduct R (isFundamentalClass_liftLineClass (R := R))
    have h' := h.pushforward_homeomorph R (snocHomeomorph m)
      (isOrientationPreserving_of_linearEquiv _ (snocLinearEquiv m) (snocHomeomorph m)
        (by
          rintro E ⟨e, he, e', he', rfl⟩ y -
          rw [chartedSpaceSelf_atlas] at he he'
          subst he he'
          rfl))
    rwa [map_snocLinearEquiv_basis] at h'

/-- **Existence of fundamental classes of real vector spaces**, in every universe: a
finite-dimensional real normed space `V`, charted by itself and oriented by a basis `b`, has a
fundamental class (the push-forward of `μ_{ℝ^N}` along the linear isomorphism `ℝ^N ≅ V`
carrying the standard basis to `b`). -/
theorem exists_isFundamentalClass_of_basis {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {N : ℕ} (b : Module.Basis (Fin N) ℝ V) :
    ∃ μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of V) N,
      IsFundamentalClass (H := V) (M := V) R b μ := by
  set L : (Fin N → ULift.{u} ℝ) ≃ₗ[ℝ] V := (liftEuclideanBasis N).equiv b (Equiv.refl _)
  let φ : (Fin N → ULift.{u} ℝ) ≃ₜ V := L.toContinuousLinearEquiv.toHomeomorph
  have hL : (liftEuclideanBasis N).map L = b := by
    refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
    rw [Module.Basis.map_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
  have h := (isFundamentalClass_euclideanClass R N).pushforward_homeomorph R φ
    (isOrientationPreserving_of_linearEquiv _ L φ (by
      rintro e he y -
      rw [chartedSpaceSelf_atlas] at he
      subst he
      rfl))
  rw [hL] at h
  exact ⟨_, h⟩

end Euclidean

end FundamentalClass

end MMP
