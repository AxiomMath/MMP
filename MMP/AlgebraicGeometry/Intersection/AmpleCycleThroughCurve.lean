module

public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PicardForm

/-!
# An ample complete-intersection cycle containing a prescribed curve

Let `X` be a projective variety of dimension `d ≥ 2` over an infinite field `k`, `H` an ample
invertible sheaf and `C ⊆ X` an integral curve. Cutting `X` successively by `d - 1` sections of
a power `H^{⊗ p}` which vanish on `C` produces an effective `1`-cycle `Γ = [C] + Z` with
`Z ≥ 0`, numerically equal to `(H^{⊗ p})^{d-1}`: for every invertible sheaf `N` on `X`,
`(N · (H^{⊗ p})^{d-1}) = (N · C) + (N · Z)`. For an ample Cartier divisor `H` on a normal `X`
this is the statement for `𝒪_X(H)`, with `𝒪_X(pH) ≅ 𝒪_X(H)^{⊗ p}`.

## Main results

* `MMP.Mori.exists_oneCycle_nonneg_intersectionNumber_cons_tensorPowModule_eq`: the existence of
  `p > 0` and of an effective integral `1`-cycle `Z` with
  `(N · (H^{⊗ p})^{d-1}) = (N · C) + (N · Z)` for every invertible sheaf `N`.
* `MMP.Mori.Divisor.IsAmple.exists_oneCycle_nonneg_intersectionNumberOn_nsmul_eq`: the same for
  Cartier divisors `H`, `N` on a normal projective variety.

## Implementation notes

The dimension is written `d = n + 2`, so that `d ≥ 2` is built in and `d - 1 = n + 1`. The
intersection number `(N · (H^{⊗ p})^{d-1})` is `AlgebraicGeometry.intersectionNumber` of the
family `(N, H^{⊗ p}, …, H^{⊗ p})` on `X` itself (the identity immersion); `(N · C)` is the
degree `MMP.Mori.ProperCurve.degree` of `N` along `C`, and `(N · Z) = ∑ zᵢ (N · Zᵢ)` is
`MMP.Mori.OneCycle.degree` for `Z = ∑ zᵢ Zᵢ`. Effectivity of `Z` is `0 ≤ Z` in the pointwise
order of finitely supported functions. A Cartier divisor is given by its invertible sheaf; on the
integral scheme `X` every invertible sheaf is `𝒪_X(N)` for a Cartier divisor `N`. The form for
Weil divisors that are Cartier, which needs `X` normal, goes through
`MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber`.

The proof inducts on the dimension of an integral closed subscheme `i : Z ⟶ X`, cutting each
one by its own section `t` of `H^{⊗ p}` whose nonvanishing locus contains the generic point of
`Z` and misses `C`. One `p` serves every point outside `C`, since the nonvanishing loci of
sections of powers of an ample sheaf form a basis of the topology and `X ∖ C` is quasi-compact.
The zero scheme of `t` on `Z` is an effective Cartier divisor `D`; Stacks Tag 0BEU replaces
`(H^{⊗ p} · L₂ ⋯ · Z)` by `(L₂ ⋯ · D)` and Stacks Tag 0BES writes the latter as the weighted
sum over the top-dimensional components of `D`. A component of `D` through `C` has the expected
dimension by Krull's principal ideal theorem, and has positive multiplicity. Choosing one section
per integral subscheme, rather than one general member for all of them, needs no infinitude of
`k`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

attribute [local instance] isInvertible_finCons

/-- The family `(M, …, M, N)` of `r + 1` modules, with `N` in the last slot. -/
private def fam {X : Scheme} (M N : X.Modules) (r : ℕ) : Fin (r + 1) → X.Modules :=
  fun j => if (j : ℕ) = r then N else M

private instance fam_isInvertible {X : Scheme} (M N : X.Modules)
    [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (r : ℕ) (j : Fin (r + 1)) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (fam M N r j) := by
  unfold fam
  split_ifs
  · exact hN
  · exact hM

/-- The intersection numbers of `(M, …, M, N)` against `i : Z ⟶ X` are those of an effective
`1`-cycle, which contains `C` with positive coefficient when `C` lies in the image of `i`. -/
private def Good {k : Type u} [Field k] {X : Scheme} (sX : X ⟶ Spec (.of k))
    [IsProper sX] (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (C : ProperCurve sX) (r : ℕ) {Z : Scheme} (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : topologicalKrullDim Z ≤ ((r + 1 : ℕ) : WithBot ℕ∞)) : Prop :=
  ∃ Γ : OneCycle ℤ sX, 0 ≤ Γ ∧ (C.point ∈ Set.range i → 1 ≤ Γ C) ∧
    ∀ (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N],
      intersectionNumber k sX i (r + 1) hZ (fam M N r) = OneCycle.degree ℤ sX N Γ

/-! ### Transcendence degrees of residue fields -/

/-- The transcendence degree over `k` of the residue field at `x` of a `k`-scheme. -/
private noncomputable def td (k : Type u) [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
    (x : X) : ℕ∞ :=
  letI : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  Cardinal.toENat (Algebra.trdeg k (X.residueField x))

private theorem td_comp (k : Type u) [Field k] {X Y : Scheme} (f : X ⟶ Spec (.of k))
    (i : Y ⟶ X) [SurjectiveOnStalks i] (y : Y) : td k (i ≫ f) y = td k f (i y) :=
  congrArg Cardinal.toENat (trdeg_residueField_of_surjectiveOnStalks k f i y).symm

private theorem dim_eq_td (k : Type u) [Field k] (X : Scheme) (f : X ⟶ Spec (.of k))
    [IrreducibleSpace X] [LocallyOfFiniteType f] (x : X) (hx : IsGenericPoint x Set.univ) :
    topologicalKrullDim X = (td k f x : WithBot ℕ∞) :=
  topologicalKrullDim_eq_trdeg_residueField k X f x hx

private theorem dim_eq_td_add (k : Type u) [Field k] (X : Scheme)
    (f : X ⟶ Spec (.of k)) [IrreducibleSpace X] [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDim X = (td k f x : WithBot ℕ∞) + ringKrullDim (X.presheaf.stalk x) :=
  (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x).trans
    (topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X f x)

/-- The reduced closed subscheme on `{y}⁻` has dimension `trdeg_k κ(y)`. -/
private theorem dim_closure_eq_td (k : Type u) [Field k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (y : X) :
    topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subscheme =
      (td k f y : WithBot ℕ∞) := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure y
  rw [dim_eq_td k _ ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))).subschemeι ≫ f) _ (genericPoint_spec _), td_comp,
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure]

/-- Cancellation in `WithBot ℕ∞`: `(a + 1 : ℕ) = b + 1` forces `b = a`. -/
private theorem td_eq_of_eq_add_one {a : ℕ} {b : ℕ∞}
    (h : ((a + 1 : ℕ) : WithBot ℕ∞) = (b : WithBot ℕ∞) + 1) : b = a := by
  have h' : ((a + 1 : ℕ) : WithBot ℕ∞) = ((b + 1 : ℕ∞) : WithBot ℕ∞) := by
    rw [h]; rfl
  have h'' : ((a + 1 : ℕ) : ℕ∞) = b + 1 := WithBot.coe_injective h'
  induction b using ENat.recTopCoe with
  | top => simp at h''
  | coe n =>
    have : a + 1 = n + 1 := by exact_mod_cast h''
    exact_mod_cast (by omega : n = a)

/-- Cancellation in `WithBot ℕ∞`: `a = a + ρ` with `0 ≤ ρ` forces `ρ = 0`. -/
private theorem ringKrullDim_eq_zero_of_eq_add {a : ℕ} {b : ℕ∞} {ρ : WithBot ℕ∞} (hρ : 0 ≤ ρ)
    (hb : b = a) (h : (a : WithBot ℕ∞) = (b : WithBot ℕ∞) + ρ) : ρ = 0 := by
  subst hb
  induction ρ using WithBot.recBotCoe with
  | bot => exact absurd hρ (by simp)
  | coe m =>
    have h' : ((a : ℕ∞) : WithBot ℕ∞) = (((a : ℕ∞) + m : ℕ∞) : WithBot ℕ∞) := by
      push_cast at h ⊢; exact h
    have h'' : (a : ℕ∞) = a + m := WithBot.coe_injective h'
    induction m using ENat.recTopCoe with
    | top => simp at h''
    | coe n =>
      have : a = a + n := by exact_mod_cast h''
      have hn : n = 0 := by omega
      subst hn; rfl

/-! ### The base case: curves -/

private theorem good_base {k : Type u} [Field k] {X : Scheme} (sX : X ⟶ Spec (.of k))
    [IsProper sX] (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (C : ProperCurve sX) {Z : Scheme} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hZ : topologicalKrullDim Z = ((0 + 1 : ℕ) : WithBot ℕ∞)) : Good sX M C 0 i hZ.le := by
  classical
  set x : X := i (genericPoint Z)
  have hsub : Set.range i ⊆ closure ({x} : Set X) := by
    rintro _ ⟨z, rfl⟩
    have hz : genericPoint Z ⤳ z :=
      specializes_iff_mem_closure.mpr (by rw [(genericPoint_spec Z).def]; trivial)
    exact specializes_iff_mem_closure.mp (hz.map i.continuous)
  have hrange : (Closeds.closure (Set.range i) : Closeds X) = Closeds.closure {x} := by
    apply SetLike.coe_injective
    simp only [Closeds.coe_closure]
    exact subset_antisymm (closure_minimal hsub isClosed_closure)
      (closure_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩))
  have hk : (curveSubschemeAtι x).ker = i.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hrange]
  haveI := IsClosedImmersion.isIso_lift (curveSubschemeAtι x) i hk
  let e : Z ≅ curveSubschemeAt x := asIso (IsClosedImmersion.lift (curveSubschemeAtι x) i hk.le)
  have he : e.hom ≫ curveSubschemeAtι x = i := IsClosedImmersion.lift_fac _ _ _
  have hdimC : topologicalKrullDim (curveSubschemeAt x) = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.Hom.homeomorph e.hom).isHomeomorph, hZ]
    rfl
  let C' : ProperCurve sX := ⟨x, isProperCurve_of_isProper sX hdimC⟩
  refine ⟨Finsupp.single C' 1, ?_, ?_, ?_⟩
  · intro D
    by_cases h : D = C' <;> simp [Finsupp.single_apply, h, eq_comm]
  · rintro ⟨c, hc⟩
    have hCeq : C = C' := by
      have h1 : (td k sX C.point : WithBot ℕ∞) = ((0 + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← dim_closure_eq_td k sX C.point]; exact C.dim_eq
      have hb : td k sX C.point = ((0 + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
      have h2 := dim_eq_td_add k Z (i ≫ sX) c
      rw [hZ, td_comp, hc] at h2
      have hρ := ringKrullDim_eq_zero_of_eq_add ringKrullDim_nonneg_of_nontrivial hb h2
      rw [ringKrullDim_stalk_eq_coheight] at hρ
      have hmax : IsMax c := Order.coheight_eq_zero.mp (by exact_mod_cast hρ)
      have hspec : genericPoint Z ⤳ c :=
        specializes_iff_mem_closure.mpr (by rw [(genericPoint_spec Z).def]; trivial)
      have hle : c ≤ genericPoint Z := hspec
      have hge : genericPoint Z ≤ c := hmax hle
      have hceq : c = genericPoint Z := (hspec.antisymm hge).symm.eq
      exact ProperCurve.ext (by rw [← hc, hceq])
    simp [hCeq]
  · intro N _
    have hfam : fam M N 0 = fun _ => N := by
      funext j
      simp [fam, Fin.val_eq_zero j]
    rw [intersectionNumber_congr_family k sX i (0 + 1) hZ.le hfam]
    rw [intersectionNumber_one_eq_invertibleCurveDegree k sX i hZ.le N]
    rw [OneCycle.degree_apply, Finsupp.sum_single_index (zero_mul _), one_mul]
    exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i C'.ι hZ.le C'.dim_le e he N

/-! ### The inductive step: cutting by a section -/

private theorem good_step {k : Type u} [Field k] {X : Scheme} (sX : X ⟶ Spec (.of k))
    [IsProper sX] (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (C : ProperCurve sX) (r : ℕ)
    (ih : ∀ {Z : Scheme} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (hZ : topologicalKrullDim Z = ((r + 1 : ℕ) : WithBot ℕ∞)), Good sX M C r i hZ.le)
    {Z : Scheme} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hZ : topologicalKrullDim Z = ((r + 1 + 1 : ℕ) : WithBot ℕ∞))
    (σ : Γ(M, ⊤)) (hσ : i (genericPoint Z) ∈ Stacks.Ample.nonvanishingLocus M σ)
    (hσC : C.point ∉ Stacks.Ample.nonvanishingLocus M σ) :
    Good sX M C (r + 1) i hZ.le := by
  classical
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  -- the section of `i^* M` and its zero scheme
  set L : Z.Modules := (Scheme.Modules.pullback i).obj M
  haveI : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L :=
    MMP.Mori.isInvertible_pullback_obj i M
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv Z L).symm
    (Stacks.NonvanishingPullback.pullbackGlobalSection i M σ)
  have hs : s.eval (op ⊤) ≠ 0 :=
    MMP.Threefold.Mori.eval_pullbackSection_ne_zero i M σ ⟨_, hσ⟩
  have hreg := isRegularSection_of_eval_top_ne_zero L s hs
  set Dv : Z.IdealSheafData := zeroScheme Z L (s.eval (op ⊤))
  haveI hDv : Stacks.Divisors.IsEffectiveCartierDivisor Dv :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Z L s).2 hreg
  obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme Z L s hreg).exists
  have hsupp : Dv.supportSet = (i ⁻¹' Stacks.Ample.nonvanishingLocus M σ)ᶜ := by
    have h1 := nonvanishingLocus_eq_compl_supportSet_zeroScheme L s hs
    have h2 := MMP.Threefold.Mori.nonvanishingLocus_pullbackSection i M σ
    rw [h2] at h1
    rw [h1, compl_compl]
  -- the pushed-forward structure sheaf of the divisor and its components
  set F : X.Modules := (Scheme.Modules.pushforward (Dv.subschemeι ≫ i)).obj
    (Stacks.Ample.unitModule Dv.subscheme)
  have hdD : topologicalKrullDim Dv.subscheme ≤ ((r + 1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k sX i (r + 1)
      hZ.le Dv
  have hsuppF : _root_.SheafOfModules.supp F = Set.range (Dv.subschemeι ≫ i) :=
    Stacks.Chow.supp_pushforwardStructureSheaf _
  have hdimF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤
      ((r + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hsuppF, topologicalKrullDim_range_eq]; exact hdD
  haveI : Finite (DimIntegralSubscheme F (r + 1)) := by
    rcases lt_or_eq_of_le hdimF with hlt | heq
    · haveI := isEmpty_dimIntegralSubscheme_of_topologicalKrullDim_lt F hlt
      infer_instance
    · haveI := finite_topDimIntegralSubscheme k sX F
      exact Finite.of_injective (fun W : DimIntegralSubscheme F (r + 1) =>
        (⟨W.1, W.2.1, W.2.2.1, by rw [heq]; exact W.2.2.2⟩ : TopDimIntegralSubscheme F))
        (fun W W' h => Subtype.ext (congrArg (fun T : TopDimIntegralSubscheme F => T.1) h))
  letI := Fintype.ofFinite (DimIntegralSubscheme F (r + 1))
  have ih' : ∀ V : DimIntegralSubscheme F (r + 1),
      Good sX M C r V.1.subschemeι V.topologicalKrullDim_le := fun V => by
    haveI := V.2.1
    exact ih V.1.subschemeι V.2.2.2
  choose Γv hΓv0 hΓvC hΓveq using ih'
  have hm0 : ∀ x, 0 ≤ Stacks.Chow.sheafMultiplicity F x := fun _ => by
    unfold Stacks.Chow.sheafMultiplicity; positivity
  refine ⟨∑ V, Stacks.Chow.sheafMultiplicity F V.genericPt • Γv V, ?_, ?_, ?_⟩
  · intro D
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun V _ =>
      mul_nonneg (hm0 _) (hΓv0 V D)
  · rintro ⟨c, hc⟩
    -- `C` lies on the divisor
    have hcD : c ∈ Dv.supportSet := by
      rw [hsupp]
      intro h
      exact hσC (hc ▸ h)
    obtain ⟨d0, hd0⟩ : c ∈ Set.range Dv.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hcD
    -- the component of the divisor through `C`
    set T : Set Dv.subscheme := irreducibleComponent d0
    have hTmem : T ∈ irreducibleComponents Dv.subscheme :=
      irreducibleComponent_mem_irreducibleComponents d0
    have hTcl : IsClosed T := isClosed_irreducibleComponent
    set ξ : Dv.subscheme := hTmem.1.genericPoint
    have hξT : IsGenericPoint ξ T := by
      have := hTmem.1.isGenericPoint_genericPoint_closure
      rwa [hTcl.closure_eq] at this
    have hξd0 : ξ ⤳ d0 :=
      specializes_iff_mem_closure.mpr (by rw [hξT.def]; exact mem_irreducibleComponent)
    set x : X := (Dv.subschemeι ≫ i) ξ
    have hloc : ringKrullDim (Z.presheaf.stalk (Dv.subschemeι ξ)) = 1 :=
      ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor Dv hDv ξ ⟨⟨T, hTmem⟩, hξT⟩
    have htd : td k sX x = ((r + 1 : ℕ) : ℕ∞) := by
      have h := dim_eq_td_add k Z (i ≫ sX) (Dv.subschemeι ξ)
      rw [hZ, hloc, td_comp] at h
      exact td_eq_of_eq_add_one h
    set V0 : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})
    haveI hV0int : IsIntegral V0.subscheme :=
      Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
    have hV0dim : topologicalKrullDim V0.subscheme = ((r + 1 : ℕ) : WithBot ℕ∞) := by
      rw [dim_closure_eq_td k sX x, htd]; rfl
    have hV0supp : (V0.support : Set X) ⊆ _root_.SheafOfModules.supp F := by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hsuppF, Closeds.coe_closure]
      exact closure_minimal (Set.singleton_subset_iff.mpr ⟨ξ, rfl⟩)
        (Dv.subschemeι ≫ i).isClosedEmbedding.isClosed_range
    let V0' : DimIntegralSubscheme F (r + 1) := ⟨V0, hV0int, hV0supp, hV0dim⟩
    have hCV0 : C.point ∈ Set.range V0'.1.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        Closeds.coe_closure, ← specializes_iff_mem_closure, ← hc, ← hd0]
      exact hξd0.map (Dv.subschemeι ≫ i).continuous
    have hΓ1 : 1 ≤ Γv V0' C := hΓvC V0' hCV0
    -- the multiplicity of that component is positive
    have hdimsupp : topologicalKrullDim V0.subscheme =
        topologicalKrullDim (_root_.SheafOfModules.supp F) := by
      refine le_antisymm ?_ (hdimF.trans hV0dim.ge)
      rw [← topologicalKrullDim_support_eq]
      exact (Topology.IsEmbedding.inclusion hV0supp).isInducing.topologicalKrullDim_le
    haveI : (Stacks.Ample.unitModule Dv.subscheme).IsCoherent :=
      Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k ((Dv.subschemeι ≫ i) ≫ sX)
    haveI : F.IsCoherent :=
      isCoherent_pushforward_of_isClosedImmersion (Dv.subschemeι ≫ i)
        (Stacks.Ample.unitModule Dv.subscheme)
    have hm : 0 < Stacks.Chow.sheafMultiplicity F V0'.genericPt :=
      sheafMultiplicity_genericPt_pos k sX F ⟨V0, hV0int, hV0supp, hdimsupp⟩
    rw [Finsupp.finset_sum_apply]
    calc (1 : ℤ) ≤ (Stacks.Chow.sheafMultiplicity F V0'.genericPt • Γv V0') C := by
          rw [Finsupp.smul_apply, smul_eq_mul]
          nlinarith
      _ ≤ ∑ V, (Stacks.Chow.sheafMultiplicity F V.genericPt • Γv V) C :=
          Finset.single_le_sum (f := fun V => (Stacks.Chow.sheafMultiplicity F V.genericPt •
            Γv V) C) (fun V _ => mul_nonneg
              (hm0 _) (hΓv0 V C))
            (Finset.mem_univ V0')
  · intro N _
    have hL0 : (Scheme.Modules.pullback i).obj (fam M N (r + 1) 0) ≅
        Stacks.Divisors.invertibleSheaf Dv :=
      eqToIso (by simp [fam] <;> rfl) ≪≫ e.symm
    rw [intersectionNumber_eq_of_isEffectiveCartierDivisor' k sX i (r + 1) hZ.le
      (fam M N (r + 1)) Dv hL0]
    have hfam : (fun t : Fin (r + 1) => fam M N (r + 1) t.succ) = fam M N r := by
      funext t
      simp [fam, Fin.val_succ]
    rw [intersectionNumber_congr_family k sX _ (r + 1) _ hfam,
      intersectionNumber_eq_sum_dimComponents, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun V _ => ?_
    rw [map_zsmul, smul_eq_mul, ← hΓveq V N]

/-! ### All dimensions -/

/-- An integral closed subscheme of dimension at least two does not lie in the curve `C`. -/
private theorem genericPoint_notMem_closure {k : Type u} [Field k] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] (C : ProperCurve sX) {Z : Scheme} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (r : ℕ)
    (hZ : topologicalKrullDim Z = ((r + 1 + 1 : ℕ) : WithBot ℕ∞)) :
    i (genericPoint Z) ∉ closure ({C.point} : Set X) := by
  intro hmem
  have h1 : topologicalKrullDim Z = (td k sX (i (genericPoint Z)) : WithBot ℕ∞) := by
    rw [dim_eq_td k Z (i ≫ sX) _ (genericPoint_spec Z), td_comp]
  rw [← dim_closure_eq_td k sX, ← topologicalKrullDim_support_eq,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure] at h1
  have hsub : closure ({i (genericPoint Z)} : Set X) ⊆ closure ({C.point} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
  have h2 : topologicalKrullDim (closure ({C.point} : Set X)) = 1 := by
    rw [← C.dim_eq, ← topologicalKrullDim_support_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
  have h3 := (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  rw [← h1, h2, hZ] at h3
  have : ((r + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) := h3
  have : r + 1 + 1 ≤ 1 := by exact_mod_cast this
  omega

private theorem good_all {k : Type u} [Field k] {X : Scheme} (sX : X ⟶ Spec (.of k))
    [IsProper sX] (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (C : ProperCurve sX)
    (hsec : ∀ y : X, y ∉ closure ({C.point} : Set X) → ∃ σ : Γ(M, ⊤),
      y ∈ Stacks.Ample.nonvanishingLocus M σ ∧ C.point ∉ Stacks.Ample.nonvanishingLocus M σ)
    (r : ℕ) : ∀ {Z : Scheme} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (hZ : topologicalKrullDim Z = ((r + 1 : ℕ) : WithBot ℕ∞)), Good sX M C r i hZ.le := by
  induction r with
  | zero => exact fun i _ _ hZ => good_base sX M C i hZ
  | succ r ih =>
    intro Z i _ _ hZ
    obtain ⟨σ, hσ, hσC⟩ := hsec _ (genericPoint_notMem_closure sX C i r hZ)
    exact good_step sX M C r (fun i _ _ hZ => ih i hZ) i hZ σ hσ hσC

/-! ### Sections of a multiple of an ample divisor avoiding a curve -/

/-- `𝒪_X(mH) ≅ 𝒪_X(H)^{⊗ m}` for `m ≥ 1`. -/
private theorem nonempty_tensorPowModule_iso {X : Scheme} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {H : Divisor X} (hH : H.IsCartier) (m : ℕ) :
    haveI := hH.isInvertibleModule_divisorialSheaf
    Nonempty (Stacks.Ample.tensorPowModule X H.divisorialSheaf ((m + 1 : ℕ) : ℤ) ≅
      ((m + 1) • H).divisorialSheaf) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  induction m with
  | zero =>
    exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by norm_num) ≪≫
      Stacks.Ample.tensorPowModuleOneIso X H.divisorialSheaf ≪≫
        eqToIso (by rw [zero_add, one_nsmul])⟩
  | succ m ih =>
    obtain ⟨e⟩ := ih
    have hm := hH.nsmul (m + 1)
    exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; ring) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso X H.divisorialSheaf ((m + 1 : ℕ) : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X e
        (Stacks.Ample.tensorPowModuleOneIso X H.divisorialSheaf) ≪≫
      hm.divisorialSheafTensorIso hH ≪≫ eqToIso (by rw [← succ_nsmul])⟩

/-- A power of a section of `L^{⊗ n}` with the same nonvanishing locus, in every degree that
is a positive multiple of `n`. -/
private theorem exists_pow_section {X : Scheme} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℕ)
    (s : Γ(Stacks.Ample.tensorPowModule X L (n : ℤ), ⊤)) (m : ℕ) :
    ∀ q : ℕ, q = n * (m + 1) → ∃ u : Γ(Stacks.Ample.tensorPowModule X L (q : ℤ), ⊤),
      Stacks.AmpleTheory.powNonvanishingOpen X L q u =
        Stacks.AmpleTheory.powNonvanishingOpen X L n s := by
  induction m with
  | zero =>
    intro q hq
    have : q = n := by simpa using hq
    subst this
    exact ⟨s, rfl⟩
  | succ m ih =>
    intro q hq
    obtain ⟨u, hu⟩ := ih (n * (m + 1)) rfl
    obtain ⟨w, hw⟩ :=
      Stacks.SectionExtension.exists_powNonvanishingOpen_eq_inf L n (n * (m + 1)) s u
    have : q = n * (m + 1) + n := by rw [hq]; ring
    subst this
    exact ⟨w, by rw [hw, hu, inf_idem]⟩

private theorem exists_sections {k : Type u} [Field k] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] (H : X.Modules)
    [Stacks.Ample.IsInvertibleModule X H] (hamp : Stacks.Ample.IsAmple X H)
    (C : ProperCurve sX) :
    ∃ p : ℕ, 0 < p ∧
      ∀ y : X, y ∉ closure ({C.point} : Set X) →
        ∃ σ : Γ(Stacks.Ample.tensorPowModule X H (p : ℤ), ⊤),
          y ∈ Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule X H (p : ℤ)) σ ∧
            C.point ∉ Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule X H (p : ℤ)) σ := by
  classical
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  have hb := Stacks.SectionExtension.isBasisNonvanishing_of_isSectionRatio X H
    (Stacks.SectionExtension.isSectionRatio_of_isAmple H hamp) hamp
  let U : X.Opens := ⟨(closure ({C.point} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  have hCU : C.point ∉ (U : Set X) := fun h => h (subset_closure rfl)
  choose nf hnf sf hxs hsU using fun y : U => hb y U y.2
  have hcover : (U : Set X) ⊆ ⋃ y : U,
      (Stacks.AmpleTheory.powNonvanishingOpen X H (nf y) (sf y) : Set X) :=
    fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hxs _⟩
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact (U : Set X)).elim_finite_subcover
    _ (fun y => (Stacks.AmpleTheory.powNonvanishingOpen X H (nf y) (sf y)).2) hcover
  set P := ∏ y ∈ t, nf y
  have hPpos : 0 < P := Finset.prod_pos fun y _ => hnf y
  refine ⟨P, hPpos, fun z hz => ?_⟩
  obtain ⟨y, hyt, hzy⟩ := Set.mem_iUnion₂.mp (ht hz)
  have hdvd : nf y ∣ P := Finset.dvd_prod_of_mem _ hyt
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; omega
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  obtain ⟨u, hu⟩ := exists_pow_section H (nf y) (sf y) m P hc
  refine ⟨u, ?_, ?_⟩
  · rw [← Stacks.AmpleTheory.coe_powNonvanishingOpen, hu]
    exact hzy
  · rw [← Stacks.AmpleTheory.coe_powNonvanishingOpen, hu]
    exact fun h => hCU (hsU y h)

/-- **An ample complete-intersection cycle containing a curve.** On a projective variety `X` of
dimension `n + 2` over an infinite field `k`, with an ample invertible sheaf `H` and a curve
`C ⊆ X`, there are `p > 0` and an effective integral `1`-cycle `Z` such that
`(N · (H^{⊗ p})^{n+1}) = (N · C) + (N · Z)` for every invertible sheaf `N` on `X`. -/
@[mmp "lem_mmp_ample_cycle_contains_curve"]
public theorem exists_oneCycle_nonneg_intersectionNumber_cons_tensorPowModule_eq (k : Type u)
    [Field k] [Infinite k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    (n : ℕ) (hdim : topologicalKrullDim X = (n + 2 : ℕ)) (H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H] (hamp : Stacks.Ample.IsAmple X H)
    (C : ProperCurve sX) :
    ∃ p : ℕ, 0 < p ∧ ∃ Z : OneCycle ℤ sX, 0 ≤ Z ∧
      ∀ (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N],
        intersectionNumber k sX (𝟙 X) (n + 2) hdim.le
            (Fin.cons N fun _ => Stacks.Ample.tensorPowModule X H (p : ℤ)) =
          C.degree k N + OneCycle.degree ℤ sX N Z := by
  classical
  haveI : IsIntegral X := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := sX)
  obtain ⟨p, hp, hsec⟩ := exists_sections sX H hamp C
  obtain ⟨Γ, hΓ, hC, hN⟩ :=
    good_all sX (Stacks.Ample.tensorPowModule X H (p : ℤ)) C hsec (n + 1) (𝟙 X) hdim
  refine ⟨p, hp, Γ - Finsupp.single C 1, ?_, fun N _ => ?_⟩
  · intro D
    by_cases h : D = C
    · subst h; simpa using hC ⟨D.point, rfl⟩
    · simpa [Finsupp.single_apply, Ne.symm h] using hΓ D
  · have key : intersectionNumber k sX (𝟙 X) (n + 2) hdim.le
        (Fin.cons N fun _ => Stacks.Ample.tensorPowModule X H (p : ℤ)) =
          OneCycle.degree ℤ sX N Γ := by
      rw [← intersectionNumber_comp_perm k sX (𝟙 X) (n + 2) hdim.le _ (finRotate (n + 2))]
      have hfam : (fun j => (Fin.cons N fun _ => Stacks.Ample.tensorPowModule X H (p : ℤ) :
          Fin (n + 2) → X.Modules) (finRotate (n + 2) j)) =
          fam (Stacks.Ample.tensorPowModule X H (p : ℤ)) N (n + 1) := by
        funext j
        induction j using Fin.lastCases with
        | last => simp [fam, finRotate_last]
        | cast t =>
          have ht : (t : ℕ) ≠ n + 1 := by omega
          rw [finRotate_apply, Fin.coeSucc_eq_succ]
          simp [fam, ht]
      rw [intersectionNumber_congr_family k sX (𝟙 X) (n + 2) hdim.le hfam, hN]
    rw [key]
    conv_lhs => rw [show Γ = Finsupp.single C 1 + (Γ - Finsupp.single C 1) by abel]
    rw [map_add, OneCycle.degree_apply ℤ sX N (Finsupp.single C 1),
      Finsupp.sum_single_index (zero_mul _), one_mul, Int.cast_id]

/-- **An ample complete-intersection cycle containing a curve, for Cartier divisors.** On a
normal projective variety `X` of dimension `n + 2` over an infinite field `k`, with an ample
Cartier divisor `H` and a curve `C ⊆ X`, there are `p > 0` and an effective integral `1`-cycle
`Z` such that `(N · (pH)^{n+1}) = (N · C) + (N · Z)` for every Cartier divisor `N` on `X`: this
is `MMP.Mori.exists_oneCycle_nonneg_intersectionNumber_cons_tensorPowModule_eq` for `𝒪_X(H)`,
with `𝒪_X(pH) ≅ 𝒪_X(H)^{⊗ p}`. -/
theorem Divisor.IsAmple.exists_oneCycle_nonneg_intersectionNumberOn_nsmul_eq (k : Type u)
    [Field k] [Infinite k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] (n : ℕ)
    (hdim : topologicalKrullDim X = (n + 2 : ℕ)) {H : Divisor X} {hH : H.IsCartier}
    (hamp : H.IsAmple hH) (C : ProperCurve sX) :
    ∃ p : ℕ, 0 < p ∧ ∃ Z : OneCycle ℤ sX, 0 ≤ Z ∧
      ∀ (N : Divisor X) (hN : N.IsCartier),
        Divisor.intersectionNumberOn k sX (𝟙 X) (n + 2) hdim.le (Fin.cons N fun _ => p • H)
            (Fin.cases hN fun _ => hH.nsmul p) =
          N.degreeOn k sX C.ι C.dim_le hN +
            Z.sum fun D z => z * N.degreeOn k sX D.ι D.dim_le hN := by
  classical
  haveI := hH.isInvertibleModule_divisorialSheaf
  obtain ⟨p, hp, Z, hZ, h⟩ :=
    exists_oneCycle_nonneg_intersectionNumber_cons_tensorPowModule_eq k sX n hdim
      H.divisorialSheaf hamp C
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  obtain ⟨e⟩ := nonempty_tensorPowModule_iso hH m
  refine ⟨m + 1, hp, Z, hZ, fun N hN => ?_⟩
  haveI := hN.isInvertibleModule_divisorialSheaf
  have hB : ∀ j : Fin (n + 2),
      ((Fin.cons N fun _ => (m + 1) • H : Fin (n + 2) → Divisor X) j).IsCartier :=
    Fin.cases hN fun _ => hH.nsmul (m + 1)
  haveI := fun j => (hB j).isInvertibleModule_divisorialSheaf
  have h1 : Divisor.intersectionNumberOn k sX (𝟙 X) (n + 2) hdim.le
      (Fin.cons N fun _ => (m + 1) • H) (Fin.cases hN fun _ => hH.nsmul (m + 1)) =
        intersectionNumber k sX (𝟙 X) (n + 2) hdim.le
          (fun j => ((Fin.cons N fun _ => (m + 1) • H : Fin (n + 2) → Divisor X) j).divisorialSheaf) :=
    MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber k sX (𝟙 X) (n + 2) hdim.le _
  rw [h1, intersectionNumber_eq_of_forall_iso k sX (𝟙 X) (n + 2) hdim.le _
    (Fin.cons N.divisorialSheaf fun _ =>
      Stacks.Ample.tensorPowModule X H.divisorialSheaf ((m + 1 : ℕ) : ℤ))
    (fun j => by
      refine Fin.cases ?_ (fun t => ?_) j
      · exact ⟨Iso.refl _⟩
      · exact ⟨e.symm⟩), h N.divisorialSheaf,
    OneCycle.degree_apply]
  rfl

end MMP.Mori
