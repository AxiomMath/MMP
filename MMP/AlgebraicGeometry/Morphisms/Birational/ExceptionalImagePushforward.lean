module

public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.PushforwardTwist
import MMP.AlgebraicGeometry.Morphisms.Birational.IsoInCodimOne
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.SncRoundDownRelativeCanonical
import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureAssociatedPoints

/-!
# Exceptional images and push-forwards along resolutions

Let `μ : X' ⟶ X` be a proper birational morphism of varieties over a field `K`, with `X`
normal. The image `μ(Exc μ)` of the exceptional locus is a closed subset of `X` of
codimension at least two, and `μ_* 𝒪_{X'} = 𝒪_X`: the canonical map
`μ.app U : Γ(X, U) ⟶ Γ(X', μ ⁻¹ᵁ U)` is an isomorphism for every open `U ⊆ X`.

Now let `X` be a non-singular variety over a perfect field `k`, `D` an `ℝ`-divisor on `X`
whose Weil divisor has simple normal crossing support, and `μ : X' ⟶ X` a proper birational
morphism from a non-singular variety. Then `μ_*𝒪_{X'}(K_{X'/X} - ⌊μ^*D⌋) = 𝒪_X(-⌊D⌋)`
(Lazarsfeld Lem. 9.2.19). Writing `D = ⌊D⌋ + {D}`, the divisor `K_{X'/X} - ⌊μ^*{D}⌋` is
effective and `μ`-exceptional, so its push-forward is `𝒪_X`, and twisting by `-⌊D⌋` gives
the claim. Consequently, for `G` an `ℝ`-divisor with SNC support on `X'` and `g : V ⟶ X'` a
further resolution, `μ_*𝒪_{X'}(K_{X'/X} - ⌊G⌋) = (g ≫ μ)_*𝒪_V(K_{V/X} - ⌊g^*G⌋)`: apply
Lem. 9.2.19 to `g`, twist by `K_{X'/X}` using `K_{V/X} = K_{V/X'} + g^*K_{X'/X}`, and push
forward along `μ`.

## Main results

* `MMP.isClosed_image_exceptionalLocus_and_isIso_app_of_isBirational`
* `MMP.Intersection.IsRelativeCanonicalDivisor.multiplierIdealSections_sub_roundDown_eq`
* `MMP.Intersection.IsRelativeCanonicalDivisor.multiplierIdealSections_sub_roundDown_eq_comp`

## Implementation notes

A variety over `K` is an integral scheme separated and of finite type over `K`
(`MMP.Intersection.IsSeparatedAlgebraicScheme`), and `μ` is a morphism over `K`. The codimension
of the closed subset `Z = μ(Exc μ)` is that of its reduced induced closed subscheme,
`MMP.Intersection.Scheme.IdealSheafData.codim (vanishingIdeal Z)`, which is `⊤` when `Z` is
empty. The ground field `ℂ` is generalized to an arbitrary field.

`μ_*𝒪_{X'}(E)` is `MMP.Intersection.multiplierIdealSections μ E`, a family of subsets of `K(X)`
indexed by the opens of `X`, and `𝒪_X(-⌊D⌋)` is `multiplierIdealSections (𝟙 X) (-⌊[D]⌋)`; the
equalities are stated over every open `U ⊆ X`. As Lazarsfeld remarks (Rem. 9.2.20), the
coefficients of the divisors may be real.

## References

* [Lazarsfeld, *Positivity in Algebraic Geometry II*][lazarsfeld2004], §9.2, Lem. 9.2.19 and
  the proof of Thm. 9.2.18
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace MMP

/-! ### The exceptional image -/

/-- The local rings of a scheme have dimension at least two at every point of a closed subset
whose reduced subscheme has codimension at least two. -/
private theorem le_ringKrullDim_stalk_of_le_codim {X : Scheme.{u}} {Z : Closeds X}
    (hZ : 2 ≤ MMP.Intersection.Scheme.IdealSheafData.codim
      (Scheme.IdealSheafData.vanishingIdeal Z)) {y : X} (hy : y ∈ (Z : Set X)) :
    2 ≤ ringKrullDim (X.presheaf.stalk y) := by
  set W := Scheme.IdealSheafData.vanishingIdeal Z
  obtain ⟨w, rfl⟩ : y ∈ Set.range W.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hC := irreducibleComponent_mem_irreducibleComponents w
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := w))
    (isClosed_of_mem_irreducibleComponents _ hC)
  have hsp : ξ ⤳ w := hξ.specializes mem_irreducibleComponent
  have h1 : 2 ≤ ringKrullDim (X.presheaf.stalk (W.subschemeι ξ)) :=
    hZ.trans (iInf₂_le ξ (by rw [hξ.def]; exact hC))
  refine h1.trans ?_
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact WithBot.coe_le_coe.mpr (Order.coheight_anti (hsp.map W.subschemeι.continuous))

/-- A closed subset all of whose points have local rings of dimension at least two has
codimension at least two. -/
private theorem le_codim_of_le_ringKrullDim_stalk {X : Scheme.{u}} {Z : Closeds X}
    (h : ∀ y ∈ (Z : Set X), 2 ≤ ringKrullDim (X.presheaf.stalk y)) :
    2 ≤ MMP.Intersection.Scheme.IdealSheafData.codim
      (Scheme.IdealSheafData.vanishingIdeal Z) := by
  refine le_iInf₂ fun η _ ↦ h _ ?_
  have hmem := Set.mem_range_self (f :=
    ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) η
  rwa [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem

/-- The exceptional locus is closed. -/
private theorem isClosed_exceptionalLocus {X' X : Scheme.{u}} (μ : X' ⟶ X) :
    IsClosed (MMP.Intersection.exceptionalLocus μ) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  simp only [Set.mem_compl_iff, MMP.Intersection.exceptionalLocus, Set.mem_setOf_eq,
    not_not] at hx
  obtain ⟨U, hxU, hU⟩ := hx
  refine ⟨U, fun x' hx' ↦ ?_, U.isOpen, hxU⟩
  simp only [Set.mem_compl_iff, MMP.Intersection.exceptionalLocus, Set.mem_setOf_eq, not_not]
  exact ⟨U, hx', hU⟩

/-- No point over the complement of `Z` is exceptional when `μ ∣_ Zᶜ` is an isomorphism. -/
private theorem image_exceptionalLocus_subset {X' X : Scheme.{u}} (μ : X' ⟶ X) (Z : Closeds X)
    (hZ : IsIso (μ ∣_ Z.compl)) : μ '' MMP.Intersection.exceptionalLocus μ ⊆ Z := by
  rintro _ ⟨x', hx', rfl⟩
  by_contra h
  refine hx' ⟨μ ⁻¹ᵁ Z.compl, h, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

/-- The pushforward `μ_* 𝒪_{X'}` is `𝒪_X` for a proper birational morphism onto a normal integral
scheme: Zariski's main theorem in the Stein-factorization form [Stacks, Tag 03H0]. -/
private theorem isIso_app_of_isBirational {X' X : Scheme.{u}} [IsIntegral X'] [IsIntegral X]
    [IsNormal X] (μ : X' ⟶ X) [IsProper μ] (hμ : IsBirational μ) (U : X.Opens) :
    IsIso (μ.app U) := by
  have : IsIso (μ.fiberToSpecResidueField (genericPoint X)) :=
    isIso_fiberToSpecResidueField_genericPoint_of_isBirational μ hμ
  have : IsIso (μ.fiberToSpecResidueField (genericPoint X)).c :=
    PresheafedSpace.c_isIso_of_iso (μ.fiberToSpecResidueField (genericPoint X)).toPshHom
  have : IsIso (μ.fiberToSpecResidueField (genericPoint X)).appTop :=
    NatIso.isIso_app_of_isIso _ (Opposite.op ⊤)
  have : IsIso μ.c := Stacks.SteinFactorization.isIso_c_of_isNormal μ
    (fun x hx ↦ by simpa [genericPoints_eq_singleton] using hμ.1.mapsTo hx) inferInstance
  exact NatIso.isIso_app_of_isIso μ.c (Opposite.op U)

/-- If `μ : X' ⟶ X` is a proper birational morphism of varieties over a field `K` and `X` is
normal, then the image `μ(Exc μ)` of the exceptional locus `MMP.Intersection.exceptionalLocus μ`
is a closed subset `Z` of `X` of codimension at least two, and `μ_* 𝒪_{X'} = 𝒪_X`: the canonical
map `μ.app U` is an isomorphism for every open `U` of `X`. -/
@[mmp "lem_mmp_foundation_laz_exceptional_image_codimension_two"]
theorem isClosed_image_exceptionalLocus_and_isIso_app_of_isBirational (K : Type u)
    [Field K] {X' X : Scheme.{u}} [X'.Over (Spec (.of K))] [X.Over (Spec (.of K))]
    [Intersection.IsSeparatedAlgebraicScheme K X'] [Intersection.IsSeparatedAlgebraicScheme K X]
    [IsIntegral X'] [IsIntegral X] [IsNormal X]
    (μ : X' ⟶ X) [μ.IsOver (Spec (.of K))] [IsProper μ] (hμ : IsBirational μ) :
    (∃ Z : Closeds X, (Z : Set X) = μ '' Intersection.exceptionalLocus μ ∧
      2 ≤ Intersection.Scheme.IdealSheafData.codim (Scheme.IdealSheafData.vanishingIdeal Z)) ∧
    ∀ U : X.Opens, IsIso (μ.app U) := by
  refine ⟨?_, isIso_app_of_isBirational μ hμ⟩
  obtain ⟨Z₀, hZ₀, hiso⟩ := MMP.exists_isIso_morphismRestrict_of_isBirational K μ hμ
  exact ⟨⟨_, μ.isClosedMap _ (isClosed_exceptionalLocus μ)⟩, rfl,
    le_codim_of_le_ringKrullDim_stalk fun y hy ↦
      le_ringKrullDim_stalk_of_le_codim hZ₀ (image_exceptionalLocus_subset μ Z₀ hiso hy)⟩

end MMP

namespace MMP.Intersection

open MMP.Mori (Divisor RDivisor)

/-! ### Push-forward along a resolution of an SNC divisor -/

/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    change (primeDivisorSubvariety P).genericPoint ∈ cartierSupport A
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- On an integral locally Noetherian scheme with factorial local rings, every Weil divisor is
the Weil divisor of a Cartier divisor. -/
private theorem exists_isWeilDivisorOfCartier_of_uniqueFactorizationMonoid {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (w : Divisor X) : ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A w :=
  MMP.Resolution.Bridges.exists_isOrderAlong_of_weilDivisor hX
    (⟨w, (AlgebraicGeometry.mem_weilDivisor_iff _).mpr fun x =>
      ⟨Set.univ, Filter.univ_mem, w.support.finite_toSet.subset fun Z hZ => by
        by_cases h : w Z = 0
        · simp [h] at hZ
        · simpa using h⟩⟩ : AlgebraicGeometry.WeilDivisor X)

/-- A dominant morphism of integral locally Noetherian schemes satisfies the pull-back condition
for every Cartier divisor. -/
private theorem pullbackCondition_of_isDominant {X X' : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsIntegral X'] [IsLocallyNoetherian X'] (μ : X' ⟶ X) [IsDominant μ]
    (A : X.CartierDivisor) : PullbackCondition μ A := by
  intro η hη hμη
  rw [AlgebraicGeometry.schemeAssociatedPoints_eq_singleton_genericPoint] at hη
  rw [Set.mem_singleton_iff.mp hη] at hμη
  have hsub : (Set.univ : Set X') ⊆ μ ⁻¹' cartierSupport A := by
    rw [← genericPoint_spec X']
    exact closure_minimal (Set.singleton_subset_iff.mpr hμη)
      ((isClosed_cartierSupport A).preimage μ.continuous)
  have hdense : closure (Set.range μ) ⊆ cartierSupport A :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact hsub (Set.mem_univ y))
      (isClosed_cartierSupport A)
  rw [μ.denseRange.closure_range] at hdense
  have : IsArtinianRing (X.presheaf.stalk (genericPoint X)) :=
    (inferInstance : IsArtinianRing X.functionField)
  exact notMem_cartierSupport_of_isArtinianRing A (genericPoint X) (hdense (Set.mem_univ _))

/-- Adding an integral divisor `B` to an `ℝ`-divisor adds its Weil divisor `[B]`. -/
private theorem isWeilRDivisorOf_add_ofDivisor {X : Scheme.{u}} {D : RCartierDivisor X}
    {w : RDivisor X} (h : IsWeilRDivisorOf D w) {B : X.CartierDivisor} {wB : Divisor X}
    (hB : IsWeilDivisorOfCartier B wB) :
    IsWeilRDivisorOf (D + CartierDivisorWithCoeffs.ofDivisor ℝ B)
      (w + MMP.Mori.Divisor.toRDivisor wB) := by
  obtain ⟨m, c, A, wA, hrep, hA, rfl⟩ := h
  refine ⟨m + 1, Fin.snoc c 1, Fin.snoc A B, Fin.snoc wA wB, ?_, fun i => ?_, ?_⟩
  · rw [CartierDivisorWithCoeffs.IsRepresentation] at hrep ⊢
    rw [Fin.sum_univ_castSucc, hrep]
    simp [Fin.snoc_castSucc, Fin.snoc_last, CartierDivisorWithCoeffs.ofDivisor]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Fin.snoc_last] using hB
    · simpa [Fin.snoc_castSucc] using hA j
  · rw [Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Adding an integral divisor `B` to an `ℝ`-divisor adds the Weil divisor of its pull-back. -/
private theorem isWeilPullback_add_ofDivisor {X X' : Scheme.{u}} {μ : X' ⟶ X}
    {D : RCartierDivisor X} {F : RDivisor X'} (hF : IsWeilPullback μ D F)
    {B : X.CartierDivisor} {B' : X'.CartierDivisor} (hB' : MMP.Intersection.IsPullback μ B B')
    {wB' : Divisor X'} (hwB' : IsWeilDivisorOfCartier B' wB') :
    IsWeilPullback μ (D + CartierDivisorWithCoeffs.ofDivisor ℝ B)
      (F + MMP.Mori.Divisor.toRDivisor wB') := by
  obtain ⟨m, c, A, D', ⟨hrep, hpc, A', hrep', hA'⟩, hD'⟩ := hF
  refine ⟨m + 1, Fin.snoc c 1, Fin.snoc A B, D' + CartierDivisorWithCoeffs.ofDivisor ℝ B',
    ⟨?_, fun i => ?_, Fin.snoc A' B', ?_, fun i => ?_⟩,
    isWeilRDivisorOf_add_ofDivisor hD' hwB'⟩
  · rw [CartierDivisorWithCoeffs.IsRepresentation] at hrep ⊢
    rw [Fin.sum_univ_castSucc, hrep]
    simp [Fin.snoc_castSucc, Fin.snoc_last, CartierDivisorWithCoeffs.ofDivisor]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Fin.snoc_last] using hB'.1
    · simpa [Fin.snoc_castSucc] using hpc j
  · rw [CartierDivisorWithCoeffs.IsRepresentation] at hrep' ⊢
    rw [Fin.sum_univ_castSucc, hrep']
    simp [Fin.snoc_castSucc, Fin.snoc_last, CartierDivisorWithCoeffs.ofDivisor]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Fin.snoc_last] using hB'
    · simpa [Fin.snoc_castSucc] using hA' j

open Pointwise in
/-- If `N` agrees with `𝒪_X` over every non-empty open, then the sheaf product `𝒪_X(A) · N` is
`𝒪_X(A)`. -/
private theorem setOf_mem_span_mul_eq {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (wA : Divisor X) (N : X.Opens → Set X.functionField)
    (hN : ∀ V : X.Opens, Nonempty V → N V = multiplierIdealSections (𝟙 X) 0 V) (U : X.Opens) :
    {g | (U = ⊥ → g = 0) ∧ ∀ x ∈ U, ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
        g ∈ Submodule.span ℤ (multiplierIdealSections (𝟙 X) wA V * N V)} =
      multiplierIdealSections (𝟙 X) wA U := by
  ext g
  constructor
  · rintro ⟨h0, hg⟩
    refine ⟨fun hU => h0 (by simpa using hU), fun P hP => ?_⟩
    have hη : P.genericPoint ∈ U := genericPoint_mem_of_support_inter_nonempty P hP
    obtain ⟨V, hxV, -, hgV⟩ := hg _ hη
    have hPV : (P.support ∩ (𝟙 X) ⁻¹ᵁ V).Nonempty :=
      support_inter_nonempty_of_genericPoint_mem P hxV
    refine (Submodule.span_le
      (p := ((P.valuationOver (𝟙 X)).leAddSubgroup _).toIntSubmodule)).mpr ?_ hgV
    rintro _ ⟨a, ha, m, hm, rfl⟩
    rw [hN V ⟨⟨_, hxV⟩⟩] at hm
    change P.valuationOver (𝟙 X) (a * m) ≤ _
    rw [map_mul]
    calc _ ≤ WithZero.exp (wA.coeff P) * WithZero.exp ((0 : Divisor X).coeff P) :=
          mul_le_mul' (ha.2 P hPV) (hm.2 P hPV)
      _ = _ := by simp
  · intro hg
    refine ⟨fun hU => hg.1 (by simpa using hU), fun x hx =>
      ⟨U, hx, le_rfl, Submodule.subset_span ⟨g, hg, 1, ?_, mul_one g⟩⟩⟩
    rw [hN U ⟨⟨x, hx⟩⟩]
    refine ⟨fun hU => absurd (show x ∈ (𝟙 X) ⁻¹ᵁ U from hx) (by rw [hU]; exact id), fun P _ => ?_⟩
    simp

/-- The fractional part of an `ℝ`-divisor with SNC support has SNC support. -/
private theorem hasSNCSupport_fract {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of k)} {wD : RDivisor X} (hsnc : HasSNCSupport sX wD) :
    HasSNCSupport sX (WeilRDivisor.fract wD) := by
  refine hsnc.of_support_subset (isReducedEffective_reducedDivisorOf _) ?_
  rw [reducedDivisor, reducedDivisor, support_reducedDivisorOf, support_reducedDivisorOf]
  intro P hP
  rw [Finsupp.mem_support_iff] at hP ⊢
  intro h
  apply hP
  rw [← MMP.Mori.DivisorWithCoeffs.coeff_apply, WeilRDivisor.coeff_fract,
    MMP.Mori.DivisorWithCoeffs.coeff_apply, h, Int.fract_zero]

/-- The heart of Lazarsfeld 9.2.19: with `B` a Cartier divisor of `-⌊D⌋` and `B'` its pull-back,
`K_{X'/X} - ⌊μ^*D⌋ = G + [B']` for an effective `μ`-exceptional divisor `G`
(namely `G = K_{X'/X} - ⌊μ^*{D}⌋`). -/
private theorem exists_sub_roundDown_eq_exceptional_add_pullback {k : Type u} [Field k]
    [PerfectField k] {X X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [MMP.Mori.IsVariety k sX] (hX : MMP.Mori.IsSmoothScheme sX)
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {μ : X' ⟶ X} [MMP.Mori.IsVariety k (μ ≫ sX)] (hX' : MMP.Mori.IsSmoothScheme (μ ≫ sX))
    [IsProper μ] [IsDominant μ] (hμ : MMP.Mori.IsBirationalMorphism μ)
    {D : RCartierDivisor X} {wD : RDivisor X} (hwD : IsWeilRDivisorOf D wD)
    (hsnc : HasSNCSupport sX wD)
    {K : X'.CartierDivisor} (hK : IsRelativeCanonicalDivisor sX μ K) {wK : Divisor X'}
    (hwK : IsWeilDivisorOfCartier K wK) {F : RDivisor X'} (hF : IsWeilPullback μ D F) :
    ∃ (B : X.CartierDivisor) (B' : X'.CartierDivisor) (wB' G : Divisor X'),
      IsWeilDivisorOfCartier B (-WeilRDivisor.roundDown wD) ∧
      MMP.Intersection.IsPullback μ B B' ∧ IsWeilDivisorOfCartier B' wB' ∧ 0 ≤ G ∧
      (∀ P : MMP.Mori.PrimeDivisor X', G.coeff P ≠ 0 → P.support ⊆ exceptionalLocus μ) ∧
      wK - WeilRDivisor.roundDown F = G + wB' := by
  classical
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  have : IsNoetherian X' := ⟨⟩
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  have : MMP.Mori.IsVariety k (X ↘ Spec (.of k)) := inferInstanceAs (MMP.Mori.IsVariety k sX)
  obtain ⟨B, hB⟩ := exists_isWeilDivisorOfCartier_of_uniqueFactorizationMonoid
    (uniqueFactorizationMonoid_stalk_of_isSmoothScheme (X := X) (k := k) hX)
    (-WeilRDivisor.roundDown wD)
  obtain ⟨B', hB'⟩ := exists_isPullback (pullbackCondition_of_isDominant μ B)
  obtain ⟨wB', hwB'⟩ := exists_isWeilDivisorOfCartier B'
  /- `{D} = D + B` and its pull-back `F + [B']`. -/
  have hwD₁ : IsWeilRDivisorOf (D + CartierDivisorWithCoeffs.ofDivisor ℝ B)
      (WeilRDivisor.fract wD) := by
    simpa [WeilRDivisor.fract, sub_eq_add_neg] using isWeilRDivisorOf_add_ofDivisor hwD hB
  have hF₁ := isWeilPullback_add_ofDivisor hF hB' hwB'
  have hle := hK.roundDown_le_of_hasSNCSupport hX hX' hμ hwD₁ (hasSNCSupport_fract hsnc)
    (fun P => ((WeilRDivisor.fract_coeff_mem_Ico_and_supp_le wD).1 P).2) hwK hF₁
  rw [WeilRDivisor.roundDown_add_toRDivisor] at hle
  refine ⟨B, B', wB', wK - WeilRDivisor.roundDown F - wB', hB, hB', hwB',
    by rw [sub_sub]; exact sub_nonneg.mpr hle, fun P hP => by_contra fun hE => hP ?_, by abel⟩
  /- Along a non-exceptional prime divisor, `K_{X'/X}` and `⌊μ^*{D}⌋` vanish. -/
  have h1 : wK.coeff P = 0 :=
    by_contra fun h => hE (hK.support_subset_exceptionalLocus _ hX' hμ hwK h)
  obtain ⟨Q, -, hQ⟩ := MMP.Positivity.exists_primeDivisor_coeff_weilPullback_eq hX hX' hμ P hE
  have h2 : (WeilRDivisor.roundDown (F + MMP.Mori.Divisor.toRDivisor wB')).coeff P = 0 := by
    rw [WeilRDivisor.coeff_roundDown, hQ _ _ _ hwD₁ hF₁, WeilRDivisor.coeff_fract,
      Int.floor_eq_zero_iff]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rw [WeilRDivisor.roundDown_add_toRDivisor, MMP.Mori.DivisorWithCoeffs.coeff_add] at h2
  simp only [MMP.Mori.DivisorWithCoeffs.coeff_sub, h1]
  omega

variable {k : Type u} [Field k] [PerfectField k] {X X' V : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- **Lazarsfeld Lem. 9.2.19, (9.9).** Let `X` be a non-singular variety over a perfect field `k`,
`D` an `ℝ`-divisor on `X` with Weil divisor `wD` of simple normal crossing support, and
`μ : X' ⟶ X` a proper birational morphism from a non-singular variety, with relative canonical
divisor `K` (Weil divisor `wK`) and `F` the Weil divisor of `μ^*D`. Then over every open
`U ⊆ X`, the sections of `μ_*𝒪_{X'}(K_{X'/X} - ⌊μ^*D⌋)` are those of `𝒪_X(-⌊D⌋)`. -/
@[mmp "lem_p09a_snc_log_resolution_pushforward"]
theorem IsRelativeCanonicalDivisor.multiplierIdealSections_sub_roundDown_eq
    [MMP.Mori.IsVariety k sX] (hX : MMP.Mori.IsSmoothScheme sX)
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {μ : X' ⟶ X} [MMP.Mori.IsVariety k (μ ≫ sX)] (hX' : MMP.Mori.IsSmoothScheme (μ ≫ sX))
    [IsProper μ] [IsDominant μ] (hμ : MMP.Mori.IsBirationalMorphism μ)
    {D : RCartierDivisor X} {wD : RDivisor X} (hwD : IsWeilRDivisorOf D wD)
    (hsnc : HasSNCSupport sX wD)
    {K : X'.CartierDivisor} (hK : IsRelativeCanonicalDivisor sX μ K) {wK : Divisor X'}
    (hwK : IsWeilDivisorOfCartier K wK) {F : RDivisor X'} (hF : IsWeilPullback μ D F)
    (U : X.Opens) :
    multiplierIdealSections μ (wK - WeilRDivisor.roundDown F) U =
      multiplierIdealSections (𝟙 X) (-WeilRDivisor.roundDown wD) U := by
  obtain ⟨B, B', wB', G, hB, hB', hwB', hG0, hGexc, hkey⟩ :=
    exists_sub_roundDown_eq_exceptional_add_pullback hX hX' hμ hwD hsnc hK hwK hF
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  letI : X'.Over (Spec (.of k)) := ⟨μ ≫ sX⟩
  have : μ.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : MMP.Mori.IsVariety k (X ↘ Spec (.of k)) := inferInstanceAs (MMP.Mori.IsVariety k sX)
  have : MMP.Mori.IsVariety k (X' ↘ Spec (.of k)) :=
    inferInstanceAs (MMP.Mori.IsVariety k (μ ≫ sX))
  rw [hkey, multiplierIdealSections_add_pullback G hB hB' hwB' U]
  refine setOf_mem_span_mul_eq _ _ (fun V hV => ?_) U
  rw [multiplierIdealSections_eq_range_of_exceptional (k := k) hμ hG0 hGexc V,
    multiplierIdealSections_eq_range_of_exceptional (k := k) (μ := 𝟙 X)
      (MMP.Mori.isBirationalMorphism_of_isIso _) le_rfl (fun P h => absurd rfl h) V]

/-! ### Push-forward to a further resolution -/

/-- Function-field maps compose contravariantly. -/
private theorem functionFieldMap_comp_apply {X Y W : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral W] (f : X ⟶ Y) (g : Y ⟶ W) [IsDominant f] [IsDominant g]
    (a : W.functionField) :
    functionFieldMap (f ≫ g) a = functionFieldMap f (functionFieldMap g a) := by
  suffices h : CommRingCat.ofHom (functionFieldMap (f ≫ g)) =
      CommRingCat.ofHom ((functionFieldMap f).comp (functionFieldMap g)) from
    congrArg (fun φ : W.functionField ⟶ X.functionField ↦ φ.hom a) h
  apply Spec.map_injective
  apply (cancel_mono (W.fromSpecStalk (genericPoint W))).mp
  rw [functionFieldMap_fromSpecStalk (f ≫ g)]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk g,
    ← Category.assoc (Spec.map (CommRingCat.ofHom (functionFieldMap f))),
    functionFieldMap_fromSpecStalk f]
  exact (Category.assoc _ _ _).symm

/-- `(g ≫ μ)_* = μ_* g_*` on sections: a rational function on `X` is a section of
`(g ≫ μ)_*𝒪_V(E)` over `U` iff its pull-back to `X'` is a section of `g_*𝒪_V(E)` over
`μ⁻¹(U)`. -/
private theorem multiplierIdealSections_comp {X X' V : Scheme.{u}} [IsIntegral X]
    [IsIntegral X'] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (g : V ⟶ X') (μ : X' ⟶ X) [IsDominant g] [IsDominant μ] (E : Divisor V) (U : X.Opens) :
    multiplierIdealSections (g ≫ μ) E U =
      functionFieldMap μ ⁻¹' multiplierIdealSections g E (μ ⁻¹ᵁ U) := by
  ext f
  simp only [multiplierIdealSections, Set.mem_setOf_eq, Set.mem_preimage,
    MMP.Mori.PrimeDivisor.valuationOver_apply, functionFieldMap_comp_apply,
    Scheme.Hom.comp_preimage, map_eq_zero]

section DivisorOfHom

variable {X : Scheme.{u}} {L M : X.Modules}

/-- Two trivializations of `L` and `M` near `p` represent a homomorphism `φ : L ⟶ M` by
functions whose germs at `p` differ by a unit of `𝒪_{X,p}`. -/
private theorem exists_germ_eq_mul_units (φ : L ⟶ M) {U U' : X.Opens} {e : Γ(L, U)}
    {e' : Γ(M, U)} {f : Γ(L, U')} {f' : Γ(M, U')}
    (he : IsTrivializingGenerator L U e) (he' : IsTrivializingGenerator M U e')
    (hf : IsTrivializingGenerator L U' f) (hf' : IsTrivializingGenerator M U' f')
    {r : Γ(X, U)} {s : Γ(X, U')} (hr : φ.app U e = r • e') (hs : φ.app U' f = s • f')
    {p : X} (hp : p ∈ U) (hp' : p ∈ U') :
    ∃ w : (X.presheaf.stalk p)ˣ, X.presheaf.germ U' p hp' s = X.presheaf.germ U p hp r * w := by
  let W : X.Opens := U ⊓ U'
  have hpW : p ∈ W := ⟨hp, hp'⟩
  let i : W ⟶ U := homOfLE inf_le_left
  let j : W ⟶ U' := homOfLE inf_le_right
  have heW := he.res (inf_le_left : W ≤ U)
  have he'W := he'.res (inf_le_left : W ≤ U)
  have hfW := hf.res (inf_le_right : W ≤ U')
  have hf'W := hf'.res (inf_le_right : W ≤ U')
  obtain ⟨a, ha⟩ := heW.bijective.2 (L.presheaf.map j.op f)
  obtain ⟨b, hb⟩ := hfW.bijective.2 (L.presheaf.map i.op e)
  obtain ⟨a', ha'⟩ := he'W.bijective.2 (M.presheaf.map j.op f')
  obtain ⟨b', hb'⟩ := hf'W.bijective.2 (M.presheaf.map i.op e')
  simp only at ha hb ha' hb'
  have hab' : a' * b' = 1 := by
    apply hf'W.bijective.1
    simp only
    rw [← smul_smul, hb', ha', one_smul]
  have hab : b * a = 1 := by
    apply heW.bijective.1
    simp only
    rw [← smul_smul, ha, hb, one_smul]
  have hnat : ∀ {Y Z : X.Opens} (k : Y ⟶ Z) (m : Γ(L, Z)),
      φ.app Y (L.presheaf.map k.op m) = M.presheaf.map k.op (φ.app Z m) := fun k m ↦ by
    simpa only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (φ.mapPresheaf.naturality k.op) m
  have key : a * X.presheaf.map i.op r = X.presheaf.map j.op s * a' := by
    apply he'W.bijective.1
    simp only
    rw [← smul_smul, ← smul_smul, ha', ← Scheme.Modules.map_smul, ← Scheme.Modules.map_smul,
      ← hr, ← hs, ← hnat, ← hnat, ← Scheme.Modules.Hom.app_smul, ha]
  have hu : IsUnit (X.presheaf.germ W p hpW (a * b')) := by
    refine IsUnit.of_mul_eq_one (X.presheaf.germ W p hpW (b * a')) ?_
    rw [← map_mul, show a * b' * (b * a') = (b * a) * (a' * b') by ring, hab, hab', mul_one,
      map_one]
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, ← TopCat.Presheaf.germ_res_apply X.presheaf j p hpW,
    ← TopCat.Presheaf.germ_res_apply X.presheaf i p hpW, ← map_mul]
  congr 1
  calc X.presheaf.map j.op s = X.presheaf.map j.op s * (a' * b') := by rw [hab', mul_one]
    _ = _ := by rw [← mul_assoc, ← key]; ring

/-- A homomorphism `φ` of line bundles is represented near every point by a function. -/
private theorem exists_isTrivializingGenerator_app_eq_smul [Stacks.Ample.IsInvertibleModule X L]
    [Stacks.Ample.IsInvertibleModule X M] (φ : L ⟶ M) (x : X) :
    ∃ (U : X.Opens) (e : Γ(L, U)) (e' : Γ(M, U)) (r : Γ(X, U)), x ∈ U ∧
      IsTrivializingGenerator L U e ∧ IsTrivializingGenerator M U e' ∧ φ.app U e = r • e' := by
  obtain ⟨U₁, -, e₁, hx₁, he₁⟩ := exists_isTrivializingGenerator L (V := ⊤) (x := x) trivial
  obtain ⟨U, hU, e', hx, he'⟩ := exists_isTrivializingGenerator M hx₁
  obtain ⟨r, hr⟩ := he'.bijective.2 (φ.app U (L.presheaf.map (homOfLE hU).op e₁))
  exact ⟨U, _, e', r, hx, he₁.res hU, he', hr.symm⟩

/-- **The divisor of a regular homomorphism of line bundles exists**: a regular `φ : L ⟶ M`
between invertible modules on a locally Noetherian scheme has a divisor `div(φ)`. -/
private theorem exists_isDivisorOfHom [IsLocallyNoetherian X]
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X M] {φ : L ⟶ M}
    (hφ : IsRegularHom φ) : ∃ D : X.CartierDivisor, IsDivisorOfHom φ D := by
  have hunit : ∀ (U : X.Opens) (e : Γ(L, U)) (e' : Γ(M, U)), IsTrivializingGenerator L U e →
      IsTrivializingGenerator M U e' → ∀ r : Γ(X, U), φ.app U e = r • e' →
        IsUnit (toTotalQuotient U r) := fun U e e' he he' r hr =>
    isUnit_toTotalQuotientSheaf_app X.sheaf U r (hφ U e e' he he' r hr)
  choose U e e' r hx he he' hr using exists_isTrivializingGenerator_app_eq_smul φ
  have hu := fun x => hunit (U x) (e x) (e' x) (he x) (he' x) (r x) (hr x)
  obtain ⟨D, hD⟩ := exists_isLocalEquationOn_of_germ_eq_mul U
    (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
    (fun x => (hu x).unit) (fun i j p hi hj => by
      obtain ⟨w, hw⟩ := exists_germ_eq_mul_units φ (he i) (he' i) (he j) (he' j) (hr i) (hr j)
        hi hj
      refine ⟨w, ?_⟩
      simp only [IsUnit.unit_spec, germ_toTotalQuotient, hw, map_mul])
  refine ⟨D, hφ, fun x => ⟨U x, hx x, r x, hu x, hD x⟩, fun V f f' hf hf' s hs => ?_⟩
  refine ⟨hunit V f f' hf hf' s hs, isLocalEquationOn_of_forall_isLocalEquationAt fun p hp => ?_⟩
  obtain ⟨w, hw⟩ := exists_germ_eq_mul_units φ (he p) (he' p) hf hf' (hr p) hs (hx p) hp
  have := (show IsLocalEquationAt D p _ from ⟨U p, hx p, (hu p).unit, hD p, rfl⟩).mul_units w
  simpa only [IsUnit.unit_spec, germ_toTotalQuotient, hw, map_mul] using this

end DivisorOfHom

/-- On an integral locally Noetherian scheme, a Cartier divisor is its own pull-back along the
identity. -/
private theorem isPullback_id {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (A : X.CartierDivisor) : MMP.Intersection.IsPullback (𝟙 X) A A := by
  refine ⟨pullbackCondition_of_isDominant (𝟙 X) A, fun y => ?_⟩
  obtain ⟨f, hf⟩ := exists_isLocalEquationAt A y
  obtain ⟨a, b, ha, hb, hab⟩ := hf.exists_isFraction
  refine ⟨a, b, ⟨f, hf, hab⟩, ?_, ?_, f, hf, ?_⟩ <;>
    simpa only [Scheme.Hom.stalkMap_id, CommRingCat.hom_id, RingHom.id_apply]

/-- The relative canonical divisor `K_{V/X'}` of a birational morphism of non-singular
varieties exists. -/
private theorem exists_isRelativeCanonicalDivisor {k : Type u} [Field k] {X' V : Scheme.{u}}
    {sX' : X' ⟶ Spec (.of k)} [IsIntegral V] [MMP.Mori.IsVariety k sX']
    (hX' : MMP.Mori.IsSmoothScheme sX') {g : V ⟶ X'} [MMP.Mori.IsVariety k (g ≫ sX')]
    (hV : MMP.Mori.IsSmoothScheme (g ≫ sX')) (hg : MMP.Mori.IsBirationalMorphism g) {n : ℕ}
    (hn : topologicalKrullDim V = n) :
    ∃ K : V.CartierDivisor, IsRelativeCanonicalDivisor sX' g K := by
  have : LocallyOfFiniteType sX' := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX') := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sX' :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : LocallyOfFinitePresentation (g ≫ sX') :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth sX' := (MMP.Mori.isSmoothScheme_iff _).mp hX'
  have : Smooth (g ≫ sX') := (MMP.Mori.isSmoothScheme_iff _).mp hV
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX')
  have hdX' : topologicalKrullDim X' = topologicalKrullDim V :=
    topologicalKrullDim_eq_of_isBirationalMorphism sX' (g ≫ sX') hg
  have := smoothOfRelativeDimension_of_isVariety sX' n (hdX'.trans hn)
  have := smoothOfRelativeDimension_of_isVariety (g ≫ sX') n hn
  have hiX' := Stacks.Discriminant.isInvertible_relativeDifferentialForms sX' n
  have hiV := Stacks.Discriminant.isInvertible_relativeDifferentialForms (g ≫ sX') n
  have : Stacks.Ample.IsInvertibleModule V
      (Scheme.Hom.relativeDifferentialForms (g ≫ sX') n) := hiV
  have : Stacks.Ample.IsInvertibleModule V ((Scheme.Modules.pullback g).obj
      (Scheme.Hom.relativeDifferentialForms sX' n)) :=
    @Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback _ _
      g.toLRSHom.toShHom _ hiX'
  have hreg := isRegularHom_jacobianSection sX' hg n
  obtain ⟨K, hK⟩ := exists_isDivisorOfHom hreg
  exact ⟨K, n, hn, Or.inl ⟨hreg, hK⟩⟩

/-- The Weil divisor of a sum of Cartier divisors is the sum of their Weil divisors. -/
private theorem eq_add_of_isWeilDivisorOfCartier {X : Scheme.{u}} {A B : X.CartierDivisor}
    {w wA wB : Divisor X} (hw : IsWeilDivisorOfCartier (A + B) w)
    (hA : IsWeilDivisorOfCartier A wA) (hB : IsWeilDivisorOfCartier B wB) : w = wA + wB :=
  MMP.Mori.DivisorWithCoeffs.ext' fun P => (hw P).unique (by
    simpa only [MMP.Mori.DivisorWithCoeffs.coeff_add] using (hA P).add (hB P))

/-- **Lazarsfeld, proof of Thm. 9.2.18.** Let `μ : X' ⟶ X` be a proper birational morphism of
non-singular varieties over a perfect field `k`, `G` an `ℝ`-divisor on `X'` with Weil divisor
`wG` of simple normal crossing support, and `g : V ⟶ X'` a proper birational morphism from a
non-singular variety. Let `K` (Weil divisor `wK`) be the relative canonical divisor of `μ`, `KV`
(Weil divisor `wKV`) that of `g ≫ μ`, and `F` the Weil divisor of `g^*G`. Then over every open
`U ⊆ X`, the sections of `μ_*𝒪_{X'}(K_{X'/X} - ⌊G⌋)` are those of
`(g ≫ μ)_*𝒪_V(K_{V/X} - ⌊g^*G⌋)`. -/
@[mmp "lem_p09a_pushforward_further_resolution"]
theorem IsRelativeCanonicalDivisor.multiplierIdealSections_sub_roundDown_eq_comp
    [MMP.Mori.IsVariety k sX] (hX : MMP.Mori.IsSmoothScheme sX)
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {μ : X' ⟶ X} [MMP.Mori.IsVariety k (μ ≫ sX)] (hX' : MMP.Mori.IsSmoothScheme (μ ≫ sX))
    [IsProper μ] [IsDominant μ] (hμ : MMP.Mori.IsBirationalMorphism μ)
    {g : V ⟶ X'} [MMP.Mori.IsVariety k (g ≫ μ ≫ sX)]
    (hV : MMP.Mori.IsSmoothScheme (g ≫ μ ≫ sX))
    [IsProper g] [IsDominant g] (hg : MMP.Mori.IsBirationalMorphism g)
    {G : RCartierDivisor X'} {wG : RDivisor X'} (hwG : IsWeilRDivisorOf G wG)
    (hsnc : HasSNCSupport (μ ≫ sX) wG)
    {K : X'.CartierDivisor} (hK : IsRelativeCanonicalDivisor sX μ K) {wK : Divisor X'}
    (hwK : IsWeilDivisorOfCartier K wK)
    {KV : V.CartierDivisor} (hKV : IsRelativeCanonicalDivisor sX (g ≫ μ) KV) {wKV : Divisor V}
    (hwKV : IsWeilDivisorOfCartier KV wKV)
    {F : RDivisor V} (hF : IsWeilPullback g G F) (U : X.Opens) :
    multiplierIdealSections μ (wK - WeilRDivisor.roundDown wG) U =
      multiplierIdealSections (g ≫ μ) (wKV - WeilRDivisor.roundDown F) U := by
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (g ≫ μ ≫ sX)
  have : IsNoetherian X' := ⟨⟩
  have : IsNoetherian V := ⟨⟩
  obtain ⟨n, hn, -⟩ := id hKV
  obtain ⟨K', hK'⟩ := exists_isRelativeCanonicalDivisor hX' hV hg hn
  obtain ⟨G', hG'⟩ := exists_isPullback (pullbackCondition_of_isDominant g K)
  obtain ⟨wK', hwK'⟩ := exists_isWeilDivisorOfCartier K'
  obtain ⟨wG', hwG'⟩ := exists_isWeilDivisorOfCartier G'
  /- `K_{V/X} = K_{V/X'} + g^*K_{X'/X}`. -/
  obtain rfl := MMP.Positivity.IsRelativeCanonicalDivisor.comp hX hX' hV hμ hg hK' hK hKV hG'
  obtain rfl := eq_add_of_isWeilDivisorOfCartier hwKV hwK' hwG'
  /- Twist `g_*𝒪_V(K_{V/X'} - ⌊g^*G⌋) = 𝒪_{X'}(-⌊G⌋)` (Lazarsfeld 9.2.19 on `X'`) by `K_{X'/X}`. -/
  have hX'eq (W : X'.Opens) :
      multiplierIdealSections g (wK' + wG' - WeilRDivisor.roundDown F) W =
        multiplierIdealSections (𝟙 X') (wK - WeilRDivisor.roundDown wG) W := by
    rw [add_sub_right_comm, sub_eq_neg_add wK,
      multiplierIdealSections_add_pullback _ hwK hG' hwG',
      multiplierIdealSections_add_pullback _ hwK (isPullback_id K) hwK]
    simp only [IsRelativeCanonicalDivisor.multiplierIdealSections_sub_roundDown_eq
      hX' hV hg hwG hsnc hK' hwK' hF]
  rw [multiplierIdealSections_comp g μ, hX'eq, ← multiplierIdealSections_comp (𝟙 X') μ]
  congr 1 <;> simp

end MMP.Intersection

end
