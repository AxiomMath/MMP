module
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary

/-!
# Positivity of top intersections and numerical discrepancies on composite resolutions

This file proves two results from Kollár–Mori, Chapters 3 and 4.

**Positivity of `(L · H^{d-1})`.** Let `X` be a projective variety of dimension `d = n + 1 ≥ 1`
over a field `k`, `L` a nef invertible sheaf on `X` which is not numerically trivial, and `H` an
ample invertible sheaf on `X`. Then `(L · H^{d-1}) > 0`. The proof is an induction on the
dimension of an integral closed subscheme `Z ⊆ X` containing a curve `C` with `deg_C L > 0`. For
`dim Z = 1` the curve is `Z` itself. For `dim Z = e + 1 ≥ 2`, ampleness of `H|_Z` gives an
effective Cartier divisor `Y` with `𝒪_Z(Y) ≅ H|_Z^{⊗ m}` containing `C`; cutting by `Y` and
summing over its top-dimensional components `Y_j` with their multiplicities `ℓ_j` gives
`m (L · H^e · Z) = ∑_j ℓ_j (L · H^{e-1} · Y_j)`, each term nonnegative by induction and the
term of a component containing `C` positive. For Cartier divisors `D`, `H` on a normal `X` this
is the statement for `𝒪_X(D)` and `𝒪_X(H)`.

**Numerical discrepancies on a composite resolution.** Let `X` be a normal surface over `k`,
`Δ` a `ℚ`-divisor on `X`, `f : Y ⟶ X` a resolution and `h : Y' ⟶ Y` a proper birational
morphism from a smooth surface. Let `a = ∑ᵢ aᵢ Eᵢ` solve the numerical pull-back equations of
`(X, Δ)` on `f`, with log pull-back `Θ = f⁻¹_* Δ - a`. Then `b = h⁻¹_* a + ∑_F a(F, Y, Θ) F`,
the sum over the finitely many `h`-exceptional curves `F`, solves the numerical pull-back
equations of `(X, Δ)` on `h ≫ f`: the divisor `K' + (h ≫ f)⁻¹_* Δ - b` is linearly equivalent
to `h^*(K_Y + Θ)`, which meets every `h`-exceptional curve trivially and meets `h⁻¹_* E` as
`K_Y + Θ` meets `E`.

## Main definitions

* `MMP.Mori.IsNumericallyTrivial`: an invertible sheaf of degree zero on every closed curve
  proper over `k`.

## Main results

* `MMP.Mori.intersectionNumber_cons_pos_of_isNef_of_isAmple`: `(L · H^{d-1}) > 0` for invertible
  sheaves.
* `MMP.Mori.Divisor.intersectionNumberOn_cons_pos_of_isNef_of_isAmple`: `(D · H^{d-1}) > 0` for
  Cartier divisors on a normal projective variety.
* `MMP.Mori.IsNumericalPullbackSolution.exists_isNumericalPullbackSolution_comp`: the
  numerical pull-back solution on `h ≫ f` with entries `aᵢ` at the transforms `h⁻¹_* Eᵢ` and
  the discrepancies `a(F, Y, Θ)` at the `h`-exceptional curves.

## Implementation notes

The intersection number `(L · H^{d-1})` is `AlgebraicGeometry.intersectionNumber` of the
family `(L, H, …, H)` of length `d` against the identity immersion of `X`. The dimension is
written `n + 1`, so that `d ≥ 1` is built in and `d - 1 = n`. A Cartier divisor is given by its
invertible sheaf; on the integral scheme `X` every invertible sheaf is `𝒪_X(D)` for a Cartier
divisor `D`. The form for Weil divisors that are Cartier, which needs `X` normal, goes through
`MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber`.

For the composite resolution the base field is assumed perfect; the source works over an
algebraically closed field of characteristic zero, and perfectness is what the construction of
discrepancies and the pull-back of differential forms along `h` use. The exceptional curves of
`h ≫ f` are described by `MMP.Mori.isSmoothResolution_comp_and_isExceptionalCurve_comp_iff`.
A vector of coefficients on the exceptional curves is a `ℚ`-divisor supported on them, and the
entry at an `h`-exceptional curve `F` is the discrepancy of `F` regarded as a divisor over `Y`
realized on `h` (`MMP.Mori.IsDiscrepancy`); discrepancies are unique, so this pins the entry.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  3.5, 4.5, 4.7, 4.15
* [Stacks Project, Tag 0BES](https://stacks.math.columbia.edu/tag/0BES)
* [Stacks Project, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-! ## Positivity of `(D · H^{d-1})` -/

namespace MMP.Mori

section Positivity

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open TopologicalSpace Order Opposite

section Helpers

attribute [local instance] twistedSheaf_isCoherent isCoherent_pushforward_of_isClosedImmersion
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent

/-- A closed embedding of an irreducible space of dimension at least one into an irreducible
space of dimension at most one is surjective. -/
private theorem range_eq_univ_of_isClosedEmbedding {C X : Type*} [TopologicalSpace C]
    [TopologicalSpace X] [IrreducibleSpace X] [IrreducibleSpace C] {f : C → X}
    (hf : Topology.IsClosedEmbedding f) (hX : topologicalKrullDim X ≤ 1)
    (hC : 1 ≤ topologicalKrullDim C) : Set.range f = Set.univ := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := one_le_krullDim_iff.mp hC
  let m := IrreducibleCloseds.map f hf.continuous
  have hm : StrictMono m :=
    (IrreducibleCloseds.map_mono hf.continuous).strictMono_of_injective
      (IrreducibleCloseds.map_injective_of_isInducing hf.isInducing)
  let R : IrreducibleCloseds X :=
    ⟨Set.range f, by simpa [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ C).image f hf.continuous.continuousOn,
      hf.isClosed_range⟩
  let U : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h1 : m b ≤ R := by
    change closure (f '' b) ⊆ Set.range f
    exact closure_minimal (Set.image_subset_range _ _) hf.isClosed_range
  have h2 : R < U := by
    refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun h => hne ?_
    exact congrArg (fun s : IrreducibleCloseds X => (s : Set X)) h
  let g : Fin 3 → IrreducibleCloseds X := ![m a, m b, U]
  have hg : StrictMono g := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · exact hm hab
    · exact lt_of_le_of_lt h1 h2
  let p : LTSeries (IrreducibleCloseds X) := ⟨2, g, fun i => hg Fin.castSucc_lt_succ⟩
  have := (LTSeries.length_le_krullDim p).trans hX
  norm_num [p] at this

/-- Two closed integral curves of `X`, one contained in the other, have the same image. -/
private theorem range_eq_of_range_subset {X C Z : Scheme.{u}} (c : C ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion c] [IsClosedImmersion i] [IsIntegral C] [IsIntegral Z]
    (hC : topologicalKrullDim C = 1) (hZ : topologicalKrullDim Z = 1)
    (hsub : Set.range c ⊆ Set.range i) : Set.range c = Set.range i := by
  refine le_antisymm hsub ?_
  have hirr : IrreducibleSpace (Set.range i) :=
    Subtype.irreducibleSpace (by
      simpa [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ Z).image i i.continuous.continuousOn)
  let f : C → Set.range i := Set.codRestrict c _ fun x => hsub ⟨x, rfl⟩
  have hfemb : Topology.IsEmbedding f :=
    c.isClosedEmbedding.isEmbedding.codRestrict _ _
  have hfcl : IsClosed (Set.range f) := by
    have : Set.range f = Subtype.val ⁻¹' Set.range c := by
      ext ⟨y, hy⟩
      simp [f, Set.mem_range, Subtype.ext_iff]
    rw [this]
    exact c.isClosedEmbedding.isClosed_range.preimage continuous_subtype_val
  have hrange := range_eq_univ_of_isClosedEmbedding ⟨hfemb, hfcl⟩
    (by rw [topologicalKrullDim_range_eq i, hZ]) (by rw [hC])
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, hx⟩ : (⟨i z, z, rfl⟩ : Set.range i) ∈ Set.range f := hrange ▸ Set.mem_univ _
  exact ⟨x, congrArg Subtype.val hx⟩

/-- The image of a closed curve under a closed immersion is not a point. -/
private theorem not_exists_range_eq_singleton {X C : Scheme.{u}} (φ : C ⟶ X)
    [IsClosedImmersion φ] (hC : topologicalKrullDim C = 1) : ¬ ∃ x : X, Set.range φ = {x} := by
  rintro ⟨x, hx⟩
  have : Subsingleton C := ⟨fun a b => φ.isEmbedding.injective <| by
    have ha : φ a ∈ Set.range φ := ⟨a, rfl⟩
    have hb : φ b ∈ Set.range φ := ⟨b, rfl⟩
    rw [hx] at ha hb
    exact ha.trans hb.symm⟩
  have h0 : topologicalKrullDim C ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
  rw [hC] at h0
  norm_num at h0

/-- Along a closed immersion of a proper curve, the degree is the degree along its
scheme-theoretic image. -/
private theorem degreeOn_eq_degreeOn_imageι {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] [LocallyOfFiniteType sX]
    {C : Scheme.{u}} (φ : C ⟶ X) [IsClosedImmersion φ] [IsIntegral C] [MMP.Mori.IsCurve k (φ ≫ sX)]
    [IsProper (φ ≫ sX)] (hd : topologicalKrullDim C ≤ 1) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    haveI : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
    MMP.Mori.degreeOn k sX φ hd M =
      MMP.Mori.degreeOn k sX φ.imageι (topologicalKrullDim_image_le_one sX φ) M := by
  have hnc := not_exists_range_eq_singleton φ
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sX))
  have : IsProper φ := IsProper.of_comp φ sX
  have : IsProper (φ.imageι ≫ sX) := isProper_imageι_comp φ sX
  have hdeg : degreeOver φ.toImage = 1 := by
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint C)
    rw [Scheme.Hom.toImage_imageι, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι, one_mul,
      residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h2.symm
  rw [degreeOn_eq_degreeOver_mul sX φ M hnc, hdeg]
  simp

/-- Two closed integral curves of a proper `k`-scheme with the same image carry the same degree. -/
private theorem degreeOn_eq_of_range_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] {C Z : Scheme.{u}} (c : C ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion c] [IsClosedImmersion i] [IsIntegral C] [IsIntegral Z]
    (hC : topologicalKrullDim C = 1) (hZ : topologicalKrullDim Z = 1)
    (hr : Set.range c = Set.range i) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX c hC.le M = MMP.Mori.degreeOn k sX i hZ.le M := by
  have : AlgebraicGeometry.IsCurve k (c ≫ sX) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := hC }
  have : AlgebraicGeometry.IsCurve k (i ≫ sX) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := hZ }
  have hker : c.ker = i.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hr]
  rw [degreeOn_eq_degreeOn_imageι sX c, degreeOn_eq_degreeOn_imageι sX i]
  exact degreeOn_subschemeι_congr hker _ _ _

/-! ### The family `(H, …, H, L)` -/

/-- The family `(H, …, H, L)` of length `d + 1`, with `L` in the last slot. -/
private def fam {X : Scheme.{u}} (L H : X.Modules) : (d : ℕ) → Fin (d + 1) → X.Modules
  | 0 => fun _ => L
  | d + 1 => Fin.cons H (fam L H d)

private instance fam_isInvertible {X : Scheme.{u}} (L H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H] :
    ∀ (d : ℕ) (j : Fin (d + 1)),
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (fam L H d j)
  | 0, _ => ‹_›
  | d + 1, j => by
    refine Fin.cases ?_ (fun t => ?_) j
    · exact (‹_› : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H)
    · exact fam_isInvertible L H d t

private theorem fam_apply {X : Scheme.{u}} (L H : X.Modules) :
    ∀ (d : ℕ) (j : Fin (d + 1)), fam L H d j = if j = Fin.last d then L else H
  | 0, j => by simp [fam, Fin.fin_one_eq_zero j]
  | d + 1, j => by
    refine Fin.cases ?_ (fun t => ?_) j
    · simp [fam, Fin.ext_iff]
    · simp [fam, fam_apply L H d t, Fin.succ_inj]

/-! ### A divisor in `|mH|` containing a closed subset -/

/-- **An effective Cartier divisor in a power of an ample module containing a given closed
subset.** On an integral scheme `W` with an ample invertible module `𝓜` and a closed subset
`T ≠ W`, some `𝓜^{⊗ n}` with `n ≥ 1` is `𝒪_W(D)` for an effective Cartier divisor `D` whose
support contains `T`: a section of `𝓜^{⊗ n}` with affine nonvanishing locus inside `W ∖ T`
([Stacks, Tag 09NV]) is regular, and its zero scheme is `D`. -/
private theorem exists_effectiveCartierDivisor_subset_supportSet {W : Scheme.{u}}
    [IsIntegral W] (M : W.Modules) [Stacks.Ample.IsInvertibleModule W M]
    (hM : Stacks.Ample.IsAmple W M) (T : Set W) (hT : IsClosed T) (hTne : T ≠ Set.univ) :
    ∃ (n : ℕ) (D : W.IdealSheafData), 1 ≤ n ∧
      Stacks.Divisors.IsEffectiveCartierDivisor D ∧ T ⊆ D.supportSet ∧
      Nonempty (Scheme.Modules.tensorPowerModules M (n : ℤ) ≅
        Stacks.Divisors.invertibleSheaf D) := by
  classical
  obtain ⟨x₀, hx₀T⟩ := (Set.ne_univ_iff_exists_notMem T).mp hTne
  obtain ⟨n, hn, s, -, hTs, hsub⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite M hM
      (Set.finite_singleton x₀) ⟨Tᶜ, hT.isOpen_compl⟩ (by simpa using hx₀T)
  have : SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  have hx₀ : x₀ ∈ Stacks.Ample.nonvanishingLocus
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) s :=
    (Stacks.AmpleTheory.coe_powNonvanishingOpen W M n s) ▸ hTs rfl
  have hne0 : s ≠ 0 := by
    intro h
    rw [h, Stacks.Ample.mem_nonvanishingLocus_iff] at hx₀
    exact hx₀ (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) s).eval (op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) s).eval (op ⊤) ≠ 0 := by
    rwa [hevaltop]
  have hreg : IsRegularSection W.sheaf.obj W.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule W M (n : ℤ)) s) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  refine ⟨n, zeroScheme W (Stacks.Ample.tensorPowModule W M (n : ℤ))
      ((Stacks.SheafOfModules.sectionsOfTop
        (Stacks.Ample.tensorPowModule W M (n : ℤ)) s).eval (op ⊤)),
    hn, (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection W _ _).2 hreg, ?_, ?_⟩
  · have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme
      (Stacks.Ample.tensorPowModule W M (n : ℤ)) _ hne0'
    have hloc : Stacks.Ample.nonvanishingLocus (Stacks.Ample.tensorPowModule W M (n : ℤ)) s =
        (zeroScheme W (Stacks.Ample.tensorPowModule W M (n : ℤ))
          ((Stacks.SheafOfModules.sectionsOfTop
            (Stacks.Ample.tensorPowModule W M (n : ℤ)) s).eval (op ⊤))).supportSetᶜ := by
      conv_lhs => rw [← hevaltop]
      rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval W _
        (Stacks.SheafOfModules.sectionsOfTop (Stacks.Ample.tensorPowModule W M (n : ℤ)) s)]
      exact hcompl
    intro t ht
    by_contra hnot
    have h1 : t ∈ Stacks.Ample.nonvanishingLocus
        (Stacks.Ample.tensorPowModule W M (n : ℤ)) s := by
      rwa [hloc]
    rw [← Stacks.AmpleTheory.coe_powNonvanishingOpen W M n s] at h1
    exact hsub h1 ht
  · obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme W _ _ hreg).exists
    exact ⟨(Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso W M (n : ℤ)).trans e.symm⟩

/-! ### The components of an effective Cartier divisor -/

/-- **An irreducible component of an effective Cartier divisor on an integral scheme of
dimension `d + 1` of finite type over `k` has dimension `d`.** At the generic point `x` of the
component, `dim Z = trdeg_k κ(x) + dim 𝒪_{Z,x}` ([Stacks, Tag 0A21]) and `dim 𝒪_{Z,x} = 1`
(Krull's height theorem), and the dimension of the reduced closure of `x` in `X` is
`trdeg_k κ(x)`. -/
private theorem topologicalKrullDim_vanishingIdeal_closure (k : Type u) [Field k]
    {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (D : Z.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (η : D.subscheme)
    (hη : ∃ T : irreducibleComponents D.subscheme, IsGenericPoint η (T : Set D.subscheme))
    {d : ℕ} (hdim : topologicalKrullDim Z = ((d + 1 : ℕ) : WithBot ℕ∞))
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure {i (D.subschemeι η)})).subscheme] :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure {i (D.subschemeι η)})).subscheme = (d : WithBot ℕ∞) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  set x := D.subschemeι η with hx
  set W' := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {i x}) with hW'
  have hg : W'.subschemeι (genericPoint W'.subscheme) = i x := by
    have h1 :=
      Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_subschemeι_genericPoint W'
    have h2 : (W'.support : Set X) = closure {i x} :=
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _).trans (Closeds.coe_closure _)
    rw [h2] at h1
    exact h1.eq (isGenericPoint_closure)
  have hW := topologicalKrullDim_eq_trdeg_residueField k W'.subscheme (W'.subschemeι ≫ sX)
    (genericPoint W'.subscheme) (genericPoint_spec W'.subscheme)
  have htW := trdeg_residueField_of_surjectiveOnStalks k sX W'.subschemeι
    (genericPoint W'.subscheme)
  have htZ := trdeg_residueField_of_surjectiveOnStalks k sX i x
  have hloc := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D hD η hη
  have hformula := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Z (i ≫ sX) x
  rw [← hx] at hloc
  rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Z (i ≫ sX) x, hdim,
    hloc] at hformula
  rw [hW, ← htW]
  rw [hg, htZ]
  refine (ENat.WithBot.add_one_cancel.mp ?_).symm
  simpa only [Nat.cast_add, Nat.cast_one] using hformula

/-- A top-dimensional integral subscheme of `D` has the dimension of `D`. -/
private theorem topologicalKrullDim_topDimIntegralSubscheme {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (D : Z.IdealSheafData) {e : ℕ}
    (hDdim : topologicalKrullDim D.subscheme = (e : WithBot ℕ∞))
    (W : TopDimIntegralSubscheme ((Scheme.Modules.pushforward (D.subschemeι ≫ i)).obj
      (Stacks.Ample.unitModule D.subscheme))) :
    topologicalKrullDim W.1.subscheme = (e : WithBot ℕ∞) := by
  rw [W.2.2.2, Stacks.Chow.supp_pushforwardStructureSheaf, topologicalKrullDim_range_eq, hDdim]

/-- **Every point of an effective Cartier divisor lies on a top-dimensional component.** For
`D ⊆ Z` effective Cartier, `Z` integral of dimension `d + 2`, and `y ∈ D`, the reduced closure
of the generic point of an irreducible component of `D` through `y` is a top-dimensional
integral subscheme of `D` containing `y`. -/
private theorem exists_topDimIntegralSubscheme_mem_range (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] {d : ℕ}
    (hZ : topologicalKrullDim Z = ((d + 1 + 1 : ℕ) : WithBot ℕ∞)) (D : Z.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDdim : topologicalKrullDim D.subscheme = ((d + 1 : ℕ) : WithBot ℕ∞)) (y : D.subscheme) :
    ∃ W : TopDimIntegralSubscheme ((Scheme.Modules.pushforward (D.subschemeι ≫ i)).obj
        (Stacks.Ample.unitModule D.subscheme)),
      i (D.subschemeι y) ∈ Set.range W.1.subschemeι := by
  obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := y))
    isClosed_irreducibleComponent
  set ξ : X := i (D.subschemeι η)
  set W' := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ξ})
  have hsupp : (W'.support : Set X) = closure {ξ} :=
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _).trans (Closeds.coe_closure _)
  have : IsReduced W'.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace W'.subscheme :=
    (W'.subschemeι.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (W'.range_subschemeι))).irreducibleSpace_iff.mpr
      (Subtype.irreducibleSpace (hsupp.symm ▸ isIrreducible_singleton.closure))
  have : IsIntegral W'.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  refine ⟨⟨W', inferInstance, ?_, ?_⟩, ?_⟩
  · rw [hsupp, Stacks.Chow.supp_pushforwardStructureSheaf]
    exact closure_minimal (Set.singleton_subset_iff.mpr ⟨η, rfl⟩)
      (D.subschemeι ≫ i).isClosedEmbedding.isClosed_range
  · rw [topologicalKrullDim_vanishingIdeal_closure k sX i D hD η
      ⟨⟨_, irreducibleComponent_mem_irreducibleComponents y⟩, hη⟩ hZ,
      Stacks.Chow.supp_pushforwardStructureSheaf, topologicalKrullDim_range_eq, hDdim]
  · have hyη : η ⤳ y := specializes_iff_mem_closure.mpr (hη.symm ▸ mem_irreducibleComponent)
    rw [W'.range_subschemeι, hsupp]
    exact specializes_iff_mem_closure.mp (hyη.map (i.continuous.comp D.subschemeι.continuous))

/-! ### The induction -/

/-- **Cutting by a divisor in `|nH|`.** For `D ⊆ Z` an effective Cartier divisor with
`𝒪_Z(D) ≅ H|_Z^{⊗ n}`, `n (H · ⋯ · H · L · Z) = (H · ⋯ · L · D)` ([Stacks, Tag 0BEU]). -/
private theorem intersectionNumber_cut (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] (L H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (d : ℕ) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : topologicalKrullDim Z = ((d + 1 + 1 : ℕ) : WithBot ℕ∞)) (n : ℕ) (D : Z.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDdim : topologicalKrullDim D.subscheme = ((d + 1 : ℕ) : WithBot ℕ∞))
    (e : Scheme.Modules.tensorPowerModules ((Scheme.Modules.pullback i).obj H) (n : ℤ) ≅
      Stacks.Divisors.invertibleSheaf D) :
    (n : ℤ) * intersectionNumber k sX i (d + 1 + 1) hZ.le (fam L H (d + 1)) =
      intersectionNumber k sX (D.subschemeι ≫ i) (d + 1) hDdim.le (fam L H d) := by
  set N : Fin (d + 1 + 1) → X.Modules :=
    Function.update (fam L H (d + 1)) 0
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        (fam L H (d + 1) 0) (n : ℤ)) with hN
  have : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q) :=
    isInvertible_update _ 0 _
  have hNiso : (Scheme.Modules.pullback i).obj (N 0) ≅
      (Stacks.Divisors.invertibleSheaf D : Z.Modules) :=
    eqToIso (congrArg (Scheme.Modules.pullback i).obj
        (Function.update_self (0 : Fin (d + 1 + 1)) _ (fam L H (d + 1)))) ≪≫
      Scheme.Modules.pullbackTensorPowerIso i H n ≪≫ e
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hD
  have hBEU := intersectionNumber_eq_of_isEffectiveCartierDivisor k sX i (d + 1) hZ.le N D
    hDdim.le hNiso
  have hmul := intersectionNumber_update_tensorPower k sX i (d + 1 + 1) hZ.le
    (fam L H (d + 1)) 0 n
  rw [← hmul, hBEU]
  exact intersectionNumber_congr_family k sX _ _ _
    (funext fun t => Function.update_of_ne (Fin.succ_ne_zero t) _ _)

/-- **Cut and decompose.** With `D` as in `intersectionNumber_cut`, `n (H · ⋯ · L · Z)` is the
multiplicity-weighted sum of `(H · ⋯ · L · Y)` over the top-dimensional components `Y` of `D`
([Stacks, Tag 0BES]). -/
private theorem intersectionNumber_cut_eq_finsum (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] (L H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (d : ℕ) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : topologicalKrullDim Z = ((d + 1 + 1 : ℕ) : WithBot ℕ∞)) (n : ℕ) (D : Z.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDdim : topologicalKrullDim D.subscheme = ((d + 1 : ℕ) : WithBot ℕ∞))
    (e : Scheme.Modules.tensorPowerModules ((Scheme.Modules.pullback i).obj H) (n : ℤ) ≅
      Stacks.Divisors.invertibleSheaf D) :
    (n : ℤ) * intersectionNumber k sX i (d + 1 + 1) hZ.le (fam L H (d + 1)) =
      ∑ᶠ W : TopDimIntegralSubscheme
          ((Scheme.Modules.pushforward (D.subschemeι ≫ i)).obj
            (Stacks.Ample.unitModule D.subscheme)),
        Stacks.Chow.sheafMultiplicity
            ((Scheme.Modules.pushforward (D.subschemeι ≫ i)).obj
              (Stacks.Ample.unitModule D.subscheme)) W.genericPt *
          intersectionNumber k sX W.1.subschemeι (d + 1)
            (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme _ hDdim W)
            (fam L H d) := by
  rw [intersectionNumber_cut k sX L H d i hZ n D hD hDdim e]
  exact intersectionNumber_eq_sum_topDimComponents k sX (D.subschemeι ≫ i) (d + 1) hDdim _

/-- The terms of the decomposition in `intersectionNumber_cut_eq_finsum` are nonnegative, given
the nonnegativity of the intersection numbers one dimension down. -/
private theorem intersectionNumber_cut_term_nonneg (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] (L H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H] (d : ℕ)
    (ih : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (hZ : topologicalKrullDim Z = ((d + 1 : ℕ) : WithBot ℕ∞)),
      0 ≤ intersectionNumber k sX i (d + 1) hZ.le (fam L H d) ∧
      ∀ {C : Scheme.{u}} (c : C ⟶ X) [IsClosedImmersion c] [IsIntegral C]
        (hC : topologicalKrullDim C = 1), Set.range c ⊆ Set.range i →
        0 < MMP.Mori.degreeOn k sX c hC.le L →
        0 < intersectionNumber k sX i (d + 1) hZ.le (fam L H d))
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (D : Z.IdealSheafData)
    (hDdim : topologicalKrullDim D.subscheme = ((d + 1 : ℕ) : WithBot ℕ∞))
    (W : TopDimIntegralSubscheme
      ((Scheme.Modules.pushforward (D.subschemeι ≫ i)).obj
        (Stacks.Ample.unitModule D.subscheme))) :
    0 ≤ Stacks.Chow.sheafMultiplicity
        ((Scheme.Modules.pushforward (D.subschemeι ≫ i)).obj
          (Stacks.Ample.unitModule D.subscheme)) W.genericPt *
      intersectionNumber k sX W.1.subschemeι (d + 1)
        (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme _ hDdim W)
        (fam L H d) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have := W.2.1
  exact mul_nonneg (sheafMultiplicity_genericPt_pos k sX _ W).le
    (ih W.1.subschemeι (topologicalKrullDim_topDimIntegralSubscheme i D hDdim W)).1

/-- A closed curve inside a closed subscheme of dimension at least two does not fill it. -/
private theorem preimage_range_ne_univ {X Z C : Scheme.{u}} (i : Z ⟶ X) (c : C ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion c] {d : ℕ}
    (hZ : topologicalKrullDim Z = ((d + 1 + 1 : ℕ) : WithBot ℕ∞))
    (hC : topologicalKrullDim C = 1) (hsub : Set.range c ⊆ Set.range i) :
    i ⁻¹' Set.range c ≠ Set.univ := fun hT => by
  have h1 := topologicalKrullDim_range_eq c
  rw [le_antisymm hsub fun _ ⟨z, hz⟩ => hz ▸ (hT ▸ Set.mem_univ z : z ∈ i ⁻¹' Set.range c),
    topologicalKrullDim_range_eq i, hZ, hC] at h1
  exact absurd (by exact_mod_cast h1 : d + 1 + 1 = 1) (by omega)

/-- **The inductive step, nonnegativity.** If the intersection numbers `(H^d · L · Y)` are
nonnegative, so is `(H^{d+1} · L · Z)` for `Z` integral of dimension `d + 2`. -/
private theorem intersectionNumber_fam_nonneg_succ (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] (L H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (hH : Stacks.Ample.IsAmple X H) (d : ℕ)
    (ih : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (hZ : topologicalKrullDim Z = ((d + 1 : ℕ) : WithBot ℕ∞)),
      0 ≤ intersectionNumber k sX i (d + 1) hZ.le (fam L H d) ∧
      ∀ {C : Scheme.{u}} (c : C ⟶ X) [IsClosedImmersion c] [IsIntegral C]
        (hC : topologicalKrullDim C = 1), Set.range c ⊆ Set.range i →
        0 < MMP.Mori.degreeOn k sX c hC.le L →
        0 < intersectionNumber k sX i (d + 1) hZ.le (fam L H d))
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hZ : topologicalKrullDim Z = ((d + 1 + 1 : ℕ) : WithBot ℕ∞)) :
    0 ≤ intersectionNumber k sX i (d + 1 + 1) hZ.le (fam L H (d + 1)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have hposdim : 0 < topologicalKrullDim Z := by
    rw [hZ]
    exact_mod_cast Nat.succ_pos _
  have hMample : Stacks.Ample.IsAmple Z ((Scheme.Modules.pullback i).obj H) :=
    Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding i H hH
      (Or.inl ⟨inferInstance, inferInstance⟩)
  obtain ⟨n, D, hn, hDc, hDne, ⟨e⟩⟩ :=
    exists_effectiveCartierDivisor_tensorPower_of_isAmple k (i ≫ sX) hposdim
      ((Scheme.Modules.pullback i).obj H)
      (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _ hMample)
  have := hDne
  have hDdim := topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k (i ≫ sX) D hDc hZ
  have h0 : 0 ≤ (n : ℤ) * intersectionNumber k sX i (d + 1 + 1) hZ.le (fam L H (d + 1)) := by
    rw [intersectionNumber_cut_eq_finsum k sX L H d i hZ n D hDc hDdim e]
    exact finsum_nonneg (intersectionNumber_cut_term_nonneg k sX L H d ih i D hDdim)
  exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using h0) (by exact_mod_cast hn)

/-- **The inductive step, positivity.** Under the induction hypothesis in dimension `d + 1`,
`(H^{d+1} · L · Z)` is positive for `Z` integral of dimension `d + 2` containing a closed curve
`C` with `deg_C L > 0`: cut `Z` by a divisor in `|nH|` containing `C`. -/
private theorem intersectionNumber_fam_pos_succ (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] (L H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (hH : Stacks.Ample.IsAmple X H) (d : ℕ)
    (ih : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (hZ : topologicalKrullDim Z = ((d + 1 : ℕ) : WithBot ℕ∞)),
      0 ≤ intersectionNumber k sX i (d + 1) hZ.le (fam L H d) ∧
      ∀ {C : Scheme.{u}} (c : C ⟶ X) [IsClosedImmersion c] [IsIntegral C]
        (hC : topologicalKrullDim C = 1), Set.range c ⊆ Set.range i →
        0 < MMP.Mori.degreeOn k sX c hC.le L →
        0 < intersectionNumber k sX i (d + 1) hZ.le (fam L H d))
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hZ : topologicalKrullDim Z = ((d + 1 + 1 : ℕ) : WithBot ℕ∞))
    {C : Scheme.{u}} (c : C ⟶ X) [IsClosedImmersion c] [IsIntegral C]
    (hC : topologicalKrullDim C = 1) (hsub : Set.range c ⊆ Set.range i)
    (hpos : 0 < MMP.Mori.degreeOn k sX c hC.le L) :
    0 < intersectionNumber k sX i (d + 1 + 1) hZ.le (fam L H (d + 1)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have hMample : Stacks.Ample.IsAmple Z ((Scheme.Modules.pullback i).obj H) :=
    Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding i H hH
      (Or.inl ⟨inferInstance, inferInstance⟩)
  set T : Set Z := i ⁻¹' Set.range c
  obtain ⟨n, D, hn, hDc, hTD, ⟨e⟩⟩ := exists_effectiveCartierDivisor_subset_supportSet _ hMample T
    (c.isClosedEmbedding.isClosed_range.preimage i.continuous)
    (preimage_range_ne_univ i c hZ hC hsub)
  obtain ⟨z, hz⟩ := hsub ⟨genericPoint C, rfl⟩
  have hzT : z ∈ T := ⟨genericPoint C, hz.symm⟩
  obtain ⟨y, hy⟩ : z ∈ Set.range D.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact (hTD hzT : _)
  have : Nonempty D.subscheme := ⟨y⟩
  have hDdim := topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k (i ≫ sX) D hDc hZ
  obtain ⟨W, hW⟩ := exists_topDimIntegralSubscheme_mem_range k sX i hZ D hDc hDdim y
  have hCsub : Set.range c ⊆ Set.range W.1.subschemeι := by
    rintro _ ⟨t, rfl⟩
    exact (((genericPoint_spec C).specializes (Set.mem_univ t)).map c.continuous).mem_closed
      W.1.subschemeι.isClosedEmbedding.isClosed_range (by rwa [hy, hz] at hW)
  have : Finite (TopDimIntegralSubscheme ((Scheme.Modules.pushforward (D.subschemeι ≫ i)).obj
      (Stacks.Ample.unitModule D.subscheme))) := finite_topDimIntegralSubscheme k sX _
  haveI := Fintype.ofFinite (TopDimIntegralSubscheme
    ((Scheme.Modules.pushforward (D.subschemeι ≫ i)).obj
      (Stacks.Ample.unitModule D.subscheme)))
  have := W.2.1
  have hWpos := mul_pos (sheafMultiplicity_genericPt_pos k sX _ W)
    ((ih W.1.subschemeι (topologicalKrullDim_topDimIntegralSubscheme i D hDdim W)).2
      c hC hCsub hpos)
  have hpos' : 0 < (n : ℤ) *
      intersectionNumber k sX i (d + 1 + 1) hZ.le (fam L H (d + 1)) := by
    rw [intersectionNumber_cut_eq_finsum k sX L H d i hZ n D hDc hDdim e,
      finsum_eq_sum_of_fintype]
    exact Finset.sum_pos' (fun W _ => intersectionNumber_cut_term_nonneg k sX L H d ih i D hDdim W)
      ⟨W, Finset.mem_univ _, hWpos⟩
  exact pos_of_mul_pos_right hpos' (by positivity)

/-- **The induction.** For `L` nef and `H` ample on `X` proper over `k`, and `Z ⊆ X` an
integral closed subscheme of dimension `d + 1`, the number `(H^d · L · Z)` is nonnegative, and
positive as soon as `Z` contains a closed curve `C` with `deg_C L > 0`. -/
private theorem intersectionNumber_fam_nonneg_and_pos (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] (L H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (hnef : MMP.Mori.IsNef k sX L) (hH : Stacks.Ample.IsAmple X H) :
    ∀ (d : ℕ) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (hZ : topologicalKrullDim Z = ((d + 1 : ℕ) : WithBot ℕ∞)),
      0 ≤ intersectionNumber k sX i (d + 1) hZ.le (fam L H d) ∧
      ∀ {C : Scheme.{u}} (c : C ⟶ X) [IsClosedImmersion c] [IsIntegral C]
        (hC : topologicalKrullDim C = 1), Set.range c ⊆ Set.range i →
        0 < MMP.Mori.degreeOn k sX c hC.le L →
        0 < intersectionNumber k sX i (d + 1) hZ.le (fam L H d) := by
  intro d
  induction d with
  | zero =>
    intro Z i _ _ hZ
    have hZ1 : topologicalKrullDim Z = 1 := by simpa using hZ
    have heq : intersectionNumber k sX i (0 + 1) hZ.le (fam L H 0) =
        MMP.Mori.degreeOn k sX i hZ1.le L :=
      intersectionNumber_one_eq_invertibleCurveDegree k sX i hZ1.le L
    rw [heq]
    refine ⟨hnef Z i hZ1, fun {C} c _ _ hC hsub hpos => ?_⟩
    rwa [← degreeOn_eq_of_range_eq sX c i hC hZ1 (range_eq_of_range_subset c i hC hZ1 hsub)]
  | succ d ih =>
    intro Z i _ _ hZ
    exact ⟨intersectionNumber_fam_nonneg_succ k sX L H hH d ih i hZ,
      fun c _ _ hC hsub hpos =>
        intersectionNumber_fam_pos_succ k sX L H hH d ih i hZ c hC hsub hpos⟩

/-! ### The statement -/

/-- A Cartier divisor that is not numerically trivial has nonzero degree on some closed curve
proper over `k`. -/
private theorem exists_degreeOn_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [MMP.Mori.IsProjectiveVariety k sX] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] {D : Divisor X} (hD : D.IsCartier)
    (hnt : ¬ (Divisor.toQDivisor D).IsNumericallyTrivial k sX) :
    ∃ (C : Scheme.{u}) (i : C ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral C)
      (_ : IsProper (i ≫ sX)) (hC : topologicalKrullDim C = 1),
      D.degreeOn k sX i hC.le hD ≠ 0 := by
  have hq := QDivisor.isQCartier_toQDivisor hD
  by_contra! h
  refine hnt ((QDivisor.isNumericallyTrivial_iff _).mpr ⟨hq, fun C i _ _ _ hC => ?_⟩)
  rw [QDivisor.intersectionNumber_toQDivisor k sX i hC.le D hD hq]
  exact_mod_cast h C i inferInstance inferInstance inferInstance hC

end Helpers

/-- An invertible sheaf `L` on a `k`-scheme `X` (structure morphism `sX`) is *numerically
trivial* if `deg_C L = 0` for every closed curve `C ⊆ X` proper over `k`, that is, every closed
immersion `i : C ⟶ X` from an integral scheme of dimension one with `i ≫ sX` proper. -/
def IsNumericallyTrivial (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : Prop :=
  ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
    (hC : topologicalKrullDim C = 1), degreeOn k sX i hC.le L = 0

/-- If the `ℚ`-divisor of a Cartier divisor `D` is not numerically trivial, then the invertible
sheaf `𝒪_X(D)` is not numerically trivial in the sense of `MMP.Mori.IsNumericallyTrivial`. -/
theorem Divisor.not_isNumericallyTrivial_divisorialSheaf {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [MMP.Mori.IsProjectiveVariety k sX] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] {D : Divisor X} (hD : D.IsCartier)
    (hnt : ¬ (Divisor.toQDivisor D).IsNumericallyTrivial k sX) :
    haveI := hD.isInvertibleModule_divisorialSheaf
    ¬ IsNumericallyTrivial k sX D.divisorialSheaf := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  intro h
  obtain ⟨C, c, _, _, _, hC, hne⟩ := exists_degreeOn_ne_zero (sX := sX) hD hnt
  exact hne (h C c hC)

attribute [local instance] isInvertible_finCons

/-- **Positivity of `(L · H^{d-1})`** (Kollár–Mori 3.5, Step 2). On a projective variety `X` of
dimension `n + 1` over `k`, a nef invertible sheaf `L` that is not numerically trivial and an
ample invertible sheaf `H` satisfy `(L · H^n) > 0`. -/
@[mmp "lem_km3a_nonvanishing_positive_top_intersection"]
public theorem intersectionNumber_cons_pos_of_isNef_of_isAmple (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] (n : ℕ)
    (hdim : topologicalKrullDim X = (n + 1 : ℕ)) (L H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (hnef : IsNef k sX L) (hnt : ¬ IsNumericallyTrivial k sX L)
    (hamp : Stacks.Ample.IsAmple X H) :
    0 < intersectionNumber k sX (𝟙 X) (n + 1) hdim.le (Fin.cons L fun _ => H) := by
  have : IsIntegral X := (inferInstance : AlgebraicGeometry.IsVariety k sX).toIsIntegral
  obtain ⟨C, c, _, _, _, hC, hne⟩ : ∃ (C : Scheme.{u}) (c : C ⟶ X) (_ : IsClosedImmersion c)
      (_ : IsIntegral C) (_ : IsProper (c ≫ sX)) (hC : topologicalKrullDim C = 1),
      degreeOn k sX c hC.le L ≠ 0 := by
    by_contra! h
    exact hnt fun C c _ _ _ hC => h C c inferInstance inferInstance inferInstance hC
  have hpos : 0 < degreeOn k sX c hC.le L := lt_of_le_of_ne (hnef C c hC) (Ne.symm hne)
  have key := (intersectionNumber_fam_nonneg_and_pos k sX L H hnef hamp n (𝟙 X) hdim).2 c hC
    (by simp) hpos
  refine lt_of_lt_of_eq key ?_
  rw [← intersectionNumber_comp_perm k sX (𝟙 X) (n + 1) hdim.le _ Fin.revPerm]
  refine intersectionNumber_congr_family k sX _ _ _ (funext fun j => ?_)
  rw [fam_apply]
  split_ifs with hj
  · obtain rfl : j = 0 := by simpa [Fin.rev_eq_iff] using hj
    rfl
  · obtain ⟨t, rfl⟩ : ∃ t : Fin n, t.succ = j :=
      Fin.exists_succ_eq.mpr (by simpa [Fin.rev_eq_iff] using hj)
    rfl

/-- **Positivity of `(D · H^{d-1})` for Cartier divisors.** On a normal projective variety `X` of
dimension `n + 1` over `k`, a nef Cartier divisor `D` that is not numerically trivial and an
ample Cartier divisor `H` satisfy `(D · H^n) > 0`: this is
`MMP.Mori.intersectionNumber_cons_pos_of_isNef_of_isAmple` for `𝒪_X(D)` and `𝒪_X(H)`. -/
theorem Divisor.intersectionNumberOn_cons_pos_of_isNef_of_isAmple (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] (n : ℕ) (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    (D H : Divisor X) (hD : D.IsCartier) (hH : H.IsCartier) (hnef : D.IsNef k sX)
    (hnt : ¬ (Divisor.toQDivisor D).IsNumericallyTrivial k sX) (hamp : H.IsAmple hH) :
    0 < Divisor.intersectionNumberOn k sX (𝟙 X) (n + 1) hdim.le (Fin.cons D fun _ => H)
      (Fin.cases hD fun _ => hH) := by
  have := hD.isInvertibleModule_divisorialSheaf
  have := hH.isInvertibleModule_divisorialSheaf
  have key := intersectionNumber_cons_pos_of_isNef_of_isAmple k sX n hdim _ _
    ((Divisor.isNef_iff k sX D hD).mp hnef)
    (Divisor.not_isNumericallyTrivial_divisorialSheaf hD hnt) hamp
  have hB : ∀ j : Fin (n + 1), ((Fin.cons D fun _ => H : Fin (n + 1) → Divisor X) j).IsCartier :=
    Fin.cases hD fun _ => hH
  have := fun j => (hB j).isInvertibleModule_divisorialSheaf
  change 0 < MMP.Mori.sheafIntersectionNumber k sX (𝟙 X) (n + 1) hdim.le
    fun j => ((Fin.cons D fun _ => H : Fin (n + 1) → Divisor X) j).divisorialSheaf
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine lt_of_lt_of_eq key (intersectionNumber_congr_family k sX _ _ _ (funext fun j => ?_))
  refine Fin.cases ?_ (fun t => ?_) j <;> rfl

end Positivity

end MMP.Mori

/-! ## Numerical discrepancies on a composite resolution -/

namespace MMP.Mori

open TopologicalSpace

/-- The source of a resolution of a normal variety is a smooth variety. -/
private theorem isSmoothVariety_of_isSmoothResolution {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    (hf : IsSmoothResolution sX f) : IsSmoothVariety k (f ≫ sX) := by
  have hv := (hf.isNormalVariety hX).1.1
  have : Smooth (f ≫ sX) := hf.isSmoothScheme.smooth
  exact ⟨⟩

/-- On the source of a resolution of a normal variety every `ℚ`-divisor `Θ` makes `(Y, Θ)` a
pair. -/
private theorem isPair_of_isSmoothResolution {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    [IsLocallyNoetherian Y] [IsNormal Y] (hf : IsSmoothResolution sX f) {K : Divisor Y} {n : ℕ}
    (hK : K.IsCanonicalDivisor (f ≫ sX) n) (Θ : QDivisor Y) : IsPair (f ≫ sX) Θ := by
  have := isSmoothVariety_of_isSmoothResolution hX hf
  have : CompactSpace Y := by
    have : QuasiCompact (f ≫ sX) := (hf.isNormalVariety hX).1.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  exact ⟨(hf.isNormalVariety hX).1, n, K, hK,
    MMP.Fourfold.isQCartier_of_isSmoothScheme hf.isSmoothScheme _⟩

/-- A proper birational morphism from a smooth surface has finitely many exceptional curves:
they are the one-dimensional irreducible components of `h⁻¹(S)` for a finite set `S`
(`MMP.Mori.exists_finite_isIso_and_isExceptionalCurve_iff`). -/
private theorem finite_setOf_isExceptionalCurve {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {Y' : Scheme.{u}} (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {f : Y ⟶ X} (hf : IsSmoothResolution sX f) {h : Y' ⟶ Y}
    (hh : IsSmoothResolution (f ≫ sX) h) :
    {F : MMP.Mori.PrimeDivisor Y' | IsExceptionalCurve h F.idealSheaf}.Finite := by
  have hY := hf.isNormalVariety hX
  have hdimY : topologicalKrullDim Y = 2 := hY.2.1.trans hdim
  obtain ⟨S, -, -, -, ⟨hT, -⟩, hiffS, -⟩ :=
    exists_finite_isIso_and_isExceptionalCurve_iff hY.1 hdimY hh
  have hv := (hh.isNormalVariety hY.1).1.1
  have : QuasiCompact (h ≫ f ≫ sX) := hv.toQuasiCompact
  have : LocallyOfFiniteType (h ≫ f ≫ sX) := hv.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (h ≫ f ≫ sX)
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace (h ≫ f ≫ sX)
  have : IsNoetherian Y' := ⟨⟩
  refine ((MMP.Intersection.finite_setOf_maximal_isIrreducible_subset hT).preimage
    (f := fun F : MMP.Mori.PrimeDivisor Y' => (F.idealSheaf.support : Set Y')) ?_).subset
    fun F hF => ((hiffS _).1 hF).2
  intro F _ G _ hFG
  apply PrimeDivisor.ext_idealSheaf
  have := F.integral
  have := G.integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme F.idealSheaf _ rfl,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme G.idealSheaf _ rfl]
  exact congrArg _ (Closeds.ext hFG)

/-- The transform `h⁻¹_* E` of a prime divisor is the prime divisor `C` as soon as the ideal
sheaf of `C` is that of the birational transform of `E`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_idealSheaf_eq {Y : Scheme.{u}}
    {Y' : Scheme.{u}}
    {h : Y' ⟶ Y} {E : MMP.Mori.PrimeDivisor Y} {C : MMP.Mori.PrimeDivisor Y'}
    (hC : C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support) :
    inverseTransformPrimeDivisor h E = some C := by
  refine inverseTransformPrimeDivisor_eq_some_iff.2 ⟨?_, hC⟩
  by_contra hne
  obtain ⟨z⟩ : Nonempty C.idealSheaf.subscheme := C.integral.nonempty
  have hz : C.idealSheaf.subschemeι z ∈ (C.idealSheaf.support : Set Y') := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hz' : (C.idealSheaf.support : Set Y').Nonempty := ⟨_, hz⟩
  rw [hC, support_inverseTransformIdeal] at hz'
  obtain ⟨y, hy⟩ := hz'
  have hempty : (E.support ∩ (biregularLocus h : Set Y)) = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
  have hempty' : h.base ⁻¹' ((E.idealSheaf.support : Set Y) ∩ biregularLocus h) = ∅ := by
    change h.base ⁻¹' (E.support ∩ (biregularLocus h : Set Y)) = ∅
    rw [hempty, Set.preimage_empty]
  have : (inverseTransform h E.idealSheaf.support : Set Y') = ∅ := by
    show closure (h.base ⁻¹' ((E.idealSheaf.support : Set Y) ∩ biregularLocus h)) = ∅
    rw [hempty', closure_empty]
  rw [this] at hy
  exact hy

open Classical in
/-- The coefficient of `h⁻¹_* a` at a prime divisor `P` of `Y'`. -/
private theorem inverseTransformDivisor_apply {Y : Scheme.{u}} {Y' : Scheme.{u}} (h : Y' ⟶ Y)
    (a : QDivisor Y)
    (P : MMP.Mori.PrimeDivisor Y') :
    inverseTransformDivisor h a P =
      ∑ E ∈ a.support, if inverseTransformPrimeDivisor h E = some P then a E else 0 := by
  conv_lhs => rw [← Finsupp.sum_single a]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [inverseTransformDivisor_single]
  cases inverseTransformPrimeDivisor h E with
  | none => simp
  | some C => simp [Finsupp.single_apply]

/-- The coefficient of `h⁻¹_* a` at the transform `h⁻¹_* E` of an `f`-exceptional curve is
`a E`, when `a` is supported on `f`-exceptional curves. -/
private theorem inverseTransformDivisor_apply_of_idealSheaf_eq {X Y Y' : Scheme.{u}}
    {f : Y ⟶ X} {h : Y' ⟶ Y} {a : QDivisor Y}
    (hinj : ∀ E E' : Y.IdealSheafData, IsExceptionalCurve f E → IsExceptionalCurve f E' →
      inverseTransformIdeal h E.support = inverseTransformIdeal h E'.support → E = E')
    (ha : ∀ E ∈ a.support, IsExceptionalCurve f E.idealSheaf)
    {E : MMP.Mori.PrimeDivisor Y} {C : MMP.Mori.PrimeDivisor Y'}
    (hE : IsExceptionalCurve f E.idealSheaf)
    (hC : C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support) :
    inverseTransformDivisor h a C = a E := by
  classical
  rw [inverseTransformDivisor_apply]
  have key : ∀ E' ∈ a.support, (if inverseTransformPrimeDivisor h E' = some C then a E' else 0) =
      if E' = E then a E' else 0 := by
    intro E' hE'
    by_cases hEE : E' = E
    · subst hEE
      rw [if_pos (inverseTransformPrimeDivisor_eq_some_of_idealSheaf_eq hC), if_pos rfl]
    · rw [if_neg hEE, if_neg]
      intro hs
      have h2 := (inverseTransformPrimeDivisor_eq_some_iff.1 hs).2
      exact hEE (PrimeDivisor.ext_idealSheaf (hinj _ _ (ha E' hE') hE (h2.symm.trans hC)))
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  by_cases hm : E ∈ a.support
  · rw [if_pos hm]
  · rw [if_neg hm, Finsupp.notMem_support_iff.1 hm]

/-- The coefficient of `h⁻¹_* a` at an `h`-exceptional curve vanishes, when `a` is supported on
`f`-exceptional curves. -/
private theorem inverseTransformDivisor_apply_of_isExceptionalCurve {X Y Y' : Scheme.{u}}
    {f : Y ⟶ X} {h : Y' ⟶ Y} {a : QDivisor Y}
    (htr : ∀ E : Y.IdealSheafData, IsExceptionalCurve f E →
      ¬ IsExceptionalCurve h (inverseTransformIdeal h E.support))
    (ha : ∀ E ∈ a.support, IsExceptionalCurve f E.idealSheaf)
    {F : MMP.Mori.PrimeDivisor Y'} (hF : IsExceptionalCurve h F.idealSheaf) :
    inverseTransformDivisor h a F = 0 := by
  classical
  rw [inverseTransformDivisor_apply]
  refine Finset.sum_eq_zero fun E hE => if_neg fun hs => ?_
  rw [(inverseTransformPrimeDivisor_eq_some_iff.1 hs).2] at hF
  exact htr _ (ha E hE) hF

/-- `h⁻¹_* a` is supported on `(h ≫ f)`-exceptional curves, when `a` is supported on
`f`-exceptional curves. -/
private theorem isExceptionalCurve_of_mem_support_inverseTransformDivisor {X Y Y' : Scheme.{u}}
    {f : Y ⟶ X} {h : Y' ⟶ Y} {a : QDivisor Y}
    (htr : ∀ E : Y.IdealSheafData, IsExceptionalCurve f E →
      IsExceptionalCurve (h ≫ f) (inverseTransformIdeal h E.support))
    (ha : ∀ E ∈ a.support, IsExceptionalCurve f E.idealSheaf)
    {P : MMP.Mori.PrimeDivisor Y'} (hP : P ∈ (inverseTransformDivisor h a).support) :
    IsExceptionalCurve (h ≫ f) P.idealSheaf := by
  classical
  rw [Finsupp.mem_support_iff, inverseTransformDivisor_apply] at hP
  obtain ⟨E, hE, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
  have hs : inverseTransformPrimeDivisor h E = some P := by
    by_contra hs
    exact hne (if_neg hs)
  rw [(inverseTransformPrimeDivisor_eq_some_iff.1 hs).2]
  exact htr _ (ha E hE)

/-- An exceptional curve of a resolution of a normal surface is proper over `k`: it lies over one
of the finitely many closed points over which the resolution is not an isomorphism. -/
private theorem isProper_of_isExceptionalCurve {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {Z : Scheme.{u}} {g : Z ⟶ X}
    (hg : IsSmoothResolution sX g) {C : Z.IdealSheafData} (hC : IsExceptionalCurve g C) :
    IsProper (C.subschemeι ≫ g ≫ sX) := by
  obtain ⟨S, -, hS, -, -, hiff, -⟩ := exists_finite_isIso_and_isExceptionalCurve_iff hX hdim hg
  obtain ⟨hcur, hmax⟩ := (hiff C).1 hC
  obtain ⟨x, hx⟩ := hC.2
  have := hcur.1
  have : IsProper g := hg.isProper
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hrange : Set.range (C.subschemeι ≫ g) = {x} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι, hx]
  obtain ⟨z, hz⟩ := hmax.1.1.nonempty
  have hxS : x ∈ S := by
    have h1 : g.base z ∈ g.base '' (C.support : Set Z) := Set.mem_image_of_mem _ hz
    rw [hx] at h1
    rw [← Set.mem_singleton_iff.1 h1]
    exact hmax.1.2 hz
  have := isProper_comp_of_range_subset_singleton sX (C.subschemeι ≫ g) (hS x hxS)
    hrange.subset
  simpa only [Category.assoc] using this

/-- On a resolution of a normal surface every `ℚ`-divisor has an intersection number with every
exceptional curve. -/
private theorem exists_isIntersectionNumber {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {Z : Scheme.{u}} {g : Z ⟶ X} [QuasiCompact (g ≫ sX)]
    [IsLocallyNoetherian Z] [IsNormal Z] (hg : IsSmoothResolution sX g) {C : Z.IdealSheafData}
    (hC : IsExceptionalCurve g C) (D : QDivisor Z) :
    ∃ x : ℚ, IsIntersectionNumber (g ≫ sX) D C x :=
  ⟨_, isProper_of_isExceptionalCurve hX hdim hg hC, hC.1.2.le,
    MMP.Fourfold.isQCartier_of_isSmoothScheme hg.isSmoothScheme D, rfl⟩

/-- **The numerical equations from one intersection number.** On a resolution of a normal
surface, if `((A - b) · C) = 0` for an exceptional curve `C`, then `∑ᵢ bᵢ (Cᵢ · C) = (A · C)`. -/
private theorem numerical_equations_of_isIntersectionNumber_sub {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {Z : Scheme.{u}} {g : Z ⟶ X} [QuasiCompact (g ≫ sX)]
    [IsLocallyNoetherian Z] [IsNormal Z] (hg : IsSmoothResolution sX g) {A b : QDivisor Z}
    {C : MMP.Mori.PrimeDivisor Z} (hC : IsExceptionalCurve g C.idealSheaf)
    (hN : IsIntersectionNumber (g ≫ sX) (A - b) C.idealSheaf 0) :
    ∃ (c : MMP.Mori.PrimeDivisor Z → ℚ) (e : ℚ),
      (∀ Ci ∈ b.support,
        IsIntersectionNumber (g ≫ sX) (Finsupp.single Ci 1) C.idealSheaf (c Ci)) ∧
      IsIntersectionNumber (g ≫ sX) A C.idealSheaf e ∧ ∑ Ci ∈ b.support, b Ci * c Ci = e := by
  classical
  choose c hc using fun Ci : MMP.Mori.PrimeDivisor Z =>
    exists_isIntersectionNumber hX hdim hg hC (Finsupp.single Ci 1)
  have hsum := isIntersectionNumber_sum b.support (MMP.Flips.isIntersectionNumber_zero hN)
    fun Ci _ => (hc Ci).smul (b Ci) (MMP.Fourfold.isQCartier_of_isSmoothScheme hg.isSmoothScheme _)
  have hA := MMP.Flips.isIntersectionNumber_add hN hsum
  have hb : ∑ Ci ∈ b.support, b Ci • (Finsupp.single Ci 1 : QDivisor Z) = b := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.sum_single b
  rw [hb, sub_add_cancel, zero_add] at hA
  exact ⟨c, _, fun Ci _ => hc Ci, hA, rfl⟩

/-- **`((K_Y + Θ) · E) = 0`** for the log pull-back `Θ = f⁻¹_* Δ - a` and every `f`-exceptional
curve `E`: this is the numerical pull-back equation of `a` at `E`, by linearity. -/
private theorem isIntersectionNumber_logPullback_eq_zero {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    (ha : IsNumericalPullbackSolution sX f K Δ a) {E : MMP.Mori.PrimeDivisor Y}
    (hE : IsExceptionalCurve f E.idealSheaf) :
    IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor K + logPullback f Δ a) E.idealSheaf 0 := by
  classical
  obtain ⟨c, e, hc, he, hsum⟩ := ha.2.2.2 E hE
  have hs := isIntersectionNumber_sum a.support (MMP.Flips.isIntersectionNumber_zero he)
    fun Ci hCi => (hc Ci hCi).smul (-a Ci)
      (MMP.Fourfold.isQCartier_of_isSmoothScheme ha.1.isSmoothScheme _)
  have h := MMP.Flips.isIntersectionNumber_add he hs
  have hb : ∑ Ci ∈ a.support, (-a Ci) • (Finsupp.single Ci 1 : QDivisor Y) = -a := by
    simp only [neg_smul, Finset.sum_neg_distrib, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact congrArg Neg.neg (Finsupp.sum_single a)
  have hv : e + ∑ Ci ∈ a.support, -a Ci * c Ci = 0 := by
    simp only [neg_mul, Finset.sum_neg_distrib, hsum, add_neg_cancel]
  rw [hb, hv] at h
  rw [logPullback, sub_eq_add_neg, ← add_assoc]
  exact h

/-- A curve in a variety `W` over `k` is a curve over `k`. -/
private theorem isCurve_subschemeι_comp {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} (hW : MMP.Mori.IsVariety k sW) {C : W.IdealSheafData}
    (hC : IsCurveIn C) : AlgebraicGeometry.IsCurve k (C.subschemeι ≫ sW) := by
  have := hC.1
  have : LocallyOfFiniteType sW := hW.toLocallyOfFiniteType
  have : IsSeparated sW := hW.toIsSeparated
  have : QuasiCompact sW := hW.toQuasiCompact
  have : AlgebraicGeometry.IsVariety k (C.subschemeι ≫ sW) := {}
  exact { topologicalKrullDim_eq_one := hC.2 }

/-- **`(h^* L · F) = 0` for an `h`-exceptional curve `F`**, `h` contracting `F` to a point
(`MMP.Mori.intersectionNumber_pullback_eq_zero`). -/
private theorem isIntersectionNumber_pullback_of_isExceptionalCurve {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {Y' : Scheme.{u}}
    {f : Y ⟶ X} {h : Y' ⟶ Y} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    [QuasiCompact ((h ≫ f) ≫ sX)] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (hh : IsSmoothResolution (f ≫ sX) h) {L : QDivisor Y}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ L.supp}
    {L' : QDivisor Y'} (hpb : L.IsPullback h hLB L') {F : Y'.IdealSheafData}
    (hF : IsExceptionalCurve h F) : IsIntersectionNumber ((h ≫ f) ≫ sX) L' F 0 := by
  obtain ⟨hcomp, -, -, hiff⟩ :=
    isSmoothResolution_comp_and_isExceptionalCurve_comp_iff hX hdim hf hh
  have hp := isProper_of_isExceptionalCurve hX hdim hcomp ((hiff F).2 (Or.inr hF))
  have hY := hf.isNormalVariety hX
  have hY' := hh.isNormalVariety hY.1
  have : MMP.Mori.IsVariety k (f ≫ sX) := hY.1.1
  have : MMP.Mori.IsVariety k ((h ≫ f) ≫ sX) := hY'.1.1
  have := isCurve_subschemeι_comp (sW := (h ≫ f) ≫ sX) hY'.1.1 hF.1
  obtain ⟨x, hx⟩ := hF.2
  have hpt : ∃ w : Y, Set.range (F.subschemeι ≫ h) = {w} := ⟨x, by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι, hx]⟩
  exact ⟨hp, hF.1.2.le, hpb.isQCartier hL,
    MMP.Mori.intersectionNumber_pullback_eq_zero k ((h ≫ f) ≫ sX) (f ≫ sX) h
      (Category.assoc h f sX).symm
      F.subschemeι hL hpb hpt⟩

/-- An `f`-exceptional curve on the smooth surface `Y` is a prime divisor. -/
private theorem exists_primeDivisor_idealSheaf_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {f : Y ⟶ X} (hf : IsSmoothResolution sX f)
    {E : Y.IdealSheafData} (hE : IsExceptionalCurve f E) :
    ∃ P : MMP.Mori.PrimeDivisor Y, P.idealSheaf = E := by
  have hY := hf.isNormalVariety hX
  have hv := hY.1.1
  have : IsIntegral Y := hv.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hv.toLocallyOfFiniteType
  have := hE.1.1
  have hcl : closure ({E.subschemeι (genericPoint E.subscheme)} : Set Y) =
      (E.support : Set Y) := by
    have h1 := (genericPoint_spec E.subscheme).image E.subschemeι.continuous
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
      E.support.isClosed.closure_eq] at h1
    exact h1
  have hd : topologicalKrullDim (E.support : Set Y) = 1 := by
    rw [← topologicalKrullDim_subscheme_eq]
    exact hE.1.2
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sX)
    (E.subschemeι (genericPoint E.subscheme))
  rw [hcl, hd, hY.2.1, hdim] at h
  refine ⟨⟨E, hE.1.1, ?_⟩, rfl⟩
  rw [MMP.Flips.codimension_closureSingleton]
  generalize Order.coheight (E.subschemeι (genericPoint E.subscheme)) = c at h ⊢
  induction c using ENat.recTopCoe with
  | top => exact absurd h (by decide)
  | coe c =>
    have h' : ((1 + c : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) :=
      WithBot.coe_injective (by push_cast; exact h)
    have : c = 1 := by have := Nat.cast_injective h'; omega
    subst this
    rfl

/-- On a surface the generic point of a prime divisor is not a closed point. -/
private theorem not_isClosed_genericPoint {k : Type u} [Field k] {W : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) [IsIntegral W]
    [LocallyOfFiniteType sW] (hdim : topologicalKrullDim W = 2) (Γ : MMP.Mori.PrimeDivisor W) :
    ¬ IsClosed ({Γ.genericPoint} : Set W) := fun hcl => by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sW Γ.genericPoint
  rw [hcl.closure_eq, Γ.coheight_genericPoint, hdim] at h
  have h0 := topologicalKrullDim_zero_of_discreteTopology ({Γ.genericPoint} : Set W)
  have h1 := add_le_add h0 (le_refl ((1 : ℕ∞) : WithBot ℕ∞))
  rw [h] at h1
  exact absurd h1 (by decide)

/-- On a surface a prime divisor is a curve. -/
private theorem isCurveIn_idealSheaf {k : Type u} [Field k] {W : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) [IsIntegral W]
    [LocallyOfFiniteType sW] (hdim : topologicalKrullDim W = 2) (Γ : MMP.Mori.PrimeDivisor W) :
    IsCurveIn Γ.idealSheaf := by
  refine ⟨Γ.integral, ?_⟩
  rw [topologicalKrullDim_subscheme_eq]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sW Γ.genericPoint
  rw [Γ.coheight_genericPoint, hdim, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  change topologicalKrullDim (Γ.support : Set W) = 1
  generalize topologicalKrullDim (Γ.support : Set W) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by decide)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have h' : ((d + 1 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) :=
        WithBot.coe_injective (by push_cast; exact h)
      have : d = 1 := by have := Nat.cast_injective h'; omega
      subst this
      rfl

/-- The generic point of a prime divisor of a normal surface lies in the biregular locus of a
resolution: the resolution is an isomorphism away from finitely many closed points. -/
private theorem genericPoint_mem_biregularLocus {k : Type u} [Field k] {W Z : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)}
    (hW : IsNormalVariety k sW) (hdim : topologicalKrullDim W = 2) {g : Z ⟶ W}
    (hg : IsSmoothResolution sW g) (Γ : MMP.Mori.PrimeDivisor W) :
    Γ.genericPoint ∈ biregularLocus g := by
  obtain ⟨S, -, hS, ⟨hSo, hiso⟩, -⟩ := exists_finite_isIso_and_isExceptionalCurve_iff hW hdim hg
  have : IsIntegral W := hW.1.toIsIntegral
  have : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  refine le_biregularLocus (V := ⟨Sᶜ, hSo⟩) hiso ?_
  intro hΓ
  exact not_isClosed_genericPoint sW hdim Γ (hS _ hΓ)

/-- A resolution `g` of a normal surface maps the generic point of a prime divisor that is not a
`g`-exceptional curve into its biregular locus. -/
private theorem map_genericPoint_mem_biregularLocus {k : Type u} [Field k] {W Z : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)}
    (hW : IsNormalVariety k sW) (hdim : topologicalKrullDim W = 2) {g : Z ⟶ W}
    (hg : IsSmoothResolution sW g) (F : MMP.Mori.PrimeDivisor Z)
    (hF : ¬ IsExceptionalCurve g F.idealSheaf) :
    g F.genericPoint ∈ biregularLocus g := by
  obtain ⟨S, -, hS, ⟨hSo, hiso⟩, -⟩ := exists_finite_isIso_and_isExceptionalCurve_iff hW hdim hg
  refine le_biregularLocus (V := ⟨Sᶜ, hSo⟩) hiso ?_
  intro hy
  apply hF
  obtain ⟨hZv, hdimZ, -⟩ := hg.isNormalVariety hW
  have : IsIntegral Z := hZv.1.toIsIntegral
  have : LocallyOfFiniteType (g ≫ sW) := hZv.1.toLocallyOfFiniteType
  have hcl : IsClosed ({g F.genericPoint} : Set W) := hS _ hy
  have hmem := MMP.Flips.primeDivisor_genericPoint_mem_support F
  refine ⟨isCurveIn_idealSheaf (g ≫ sW) (hdimZ.trans hdim) F, g F.genericPoint, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ closure ({F.genericPoint} : Set Z) := by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hz
    have hsp : F.genericPoint ⤳ z := specializes_iff_mem_closure.mpr hz'
    have h2 := specializes_iff_mem_closure.mp (hsp.map g.continuous)
    rw [hcl.closure_eq] at h2
    exact h2
  · rintro _ rfl
    exact ⟨F.genericPoint, hmem, rfl⟩

/-- The transform `g⁻¹_* Δ` has coefficient zero at a `g`-exceptional curve: no prime divisor of
`X` has its generic point at the closed image point. -/
private theorem inverseTransformDivisor_apply_eq_zero_of_isExceptionalCurve {k : Type u}
    [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {Z : Scheme.{u}}
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2) {g : Z ⟶ X}
    (hg : IsSmoothResolution sX g) (Δ : QDivisor X) {F : MMP.Mori.PrimeDivisor Z}
    (hF : IsExceptionalCurve g F.idealSheaf) : inverseTransformDivisor g Δ F = 0 := by
  classical
  rw [inverseTransformDivisor_apply]
  refine Finset.sum_eq_zero fun E _ => if_neg fun hs => ?_
  obtain ⟨hη, -⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hs
  obtain ⟨S, -, hS, -, -, hiff, -⟩ := exists_finite_isIso_and_isExceptionalCurve_iff hX hdim hg
  have hmem := MMP.Flips.primeDivisor_genericPoint_mem_support F
  have hS' : g F.genericPoint ∈ S := ((hiff _).1 hF).2.1.2 hmem
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  exact not_isClosed_genericPoint sX hdim E (hη ▸ hS _ hS')

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {Z W : Scheme.{u}}
    (sW : W ⟶ Spec (.of k)) [IsIntegral W] [LocallyOfFiniteType sW] {d : ℕ}
    (hd : topologicalKrullDim W = d) (g : Z ⟶ W) [IsIntegral Z] [IsDominant g]
    (hg : IsBirationalMorphism g) {m : ℤ} {τ : RationalPluriForms sW d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sW g τ ≠ 0 := by
  let := functionFieldAlgebra sW
  let := functionFieldAlgebra (g ≫ sW)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sW g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sW g hg.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sW) hd)
  have hpull : pullbackRationalPluriForms sW g τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap W.functionField Z.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- The transform of `Δ` along `h ≫ f` at a prime divisor `F` of `Y'` is the transform along `f`
at the prime divisor `D₀` of `Y` whose generic point is `h(η_F)`. -/
private theorem inverseTransformDivisor_comp_apply_of_map_genericPoint {k : Type u} [Field k]
    {X Y Y' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {f : Y ⟶ X} {h : Y' ⟶ Y}
    (hf : IsSmoothResolution sX f) (hcomp : IsSmoothResolution sX (h ≫ f)) (Δ : QDivisor X)
    {F : MMP.Mori.PrimeDivisor Y'} {D₀ : MMP.Mori.PrimeDivisor Y}
    (hη : h F.genericPoint = D₀.genericPoint) :
    inverseTransformDivisor (h ≫ f) Δ F = inverseTransformDivisor f Δ D₀ := by
  classical
  rw [inverseTransformDivisor_apply, inverseTransformDivisor_apply]
  refine Finset.sum_congr rfl fun E _ => if_congr ⟨fun hs => ?_, fun hs => ?_⟩ rfl rfl
  · obtain ⟨hη', -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hs
    rw [Scheme.Hom.comp_apply, hη] at hη'
    exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      hη' (hη' ▸ genericPoint_mem_biregularLocus hX hdim hf E)
  · obtain ⟨hη', -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hs
    have hη'' : (h ≫ f) F.genericPoint = E.genericPoint := by
      rw [Scheme.Hom.comp_apply, hη, hη']
    exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      hη'' (hη'' ▸ genericPoint_mem_biregularLocus hX hdim hcomp E)

/-- If `b` is supported on `(h ≫ f)`-exceptional curves and agrees with `a` on the transforms of
the `f`-exceptional curves, then the entry of `b` at the transform `F` of a prime divisor `D₀`
of `Y`, with `F` not `h`-exceptional, is that of `a` at `D₀`. -/
private theorem apply_eq_of_inverseTransformPrimeDivisor_eq_some {k : Type u} [Field k]
    {X Y Y' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {f : Y ⟶ X} {h : Y' ⟶ Y}
    (hf : IsSmoothResolution sX f) (hh : IsSmoothResolution (f ≫ sX) h) {a : QDivisor Y}
    (ha : ∀ E ∈ a.support, IsExceptionalCurve f E.idealSheaf) {b : QDivisor Y'}
    (hbsupp : ∀ P ∈ b.support, IsExceptionalCurve (h ≫ f) P.idealSheaf)
    (hbE : ∀ (E : MMP.Mori.PrimeDivisor Y) (C : MMP.Mori.PrimeDivisor Y'),
      IsExceptionalCurve f E.idealSheaf →
        C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support → b C = a E)
    {F : MMP.Mori.PrimeDivisor Y'} (hF : ¬IsExceptionalCurve h F.idealSheaf)
    {D₀ : MMP.Mori.PrimeDivisor Y} (hη : h F.genericPoint = D₀.genericPoint)
    (hD₀ : inverseTransformPrimeDivisor h D₀ = some F) : b F = a D₀ := by
  obtain ⟨-, -, -, hiff⟩ := isSmoothResolution_comp_and_isExceptionalCurve_comp_iff hX hdim hf hh
  have hFC : F.idealSheaf = inverseTransformIdeal h D₀.idealSheaf.support :=
    (inverseTransformPrimeDivisor_eq_some_iff.1 hD₀).2
  by_cases hE : IsExceptionalCurve f D₀.idealSheaf
  · exact hbE D₀ F hE hFC
  have ha0 : a D₀ = 0 := by
    by_contra hne
    exact hE (ha D₀ (Finsupp.mem_support_iff.2 hne))
  rw [ha0]
  by_contra hne
  rcases (hiff _).1 (hbsupp F (Finsupp.mem_support_iff.2 hne)) with ⟨E, hEx, hFE⟩ | hFh
  · obtain ⟨Ep, rfl⟩ := exists_primeDivisor_idealSheaf_eq hX hdim hf hEx
    obtain ⟨hη', -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        (inverseTransformPrimeDivisor_eq_some_of_idealSheaf_eq hFE)
    have : Ep = D₀ := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hη'.symm.trans hη)
    exact hE (this ▸ hEx)
  · exact hF hFh

/-- The discrepancy over `(Y, Θ)` of a prime divisor `F` of `Y'` with `h(η_F)` in the biregular
locus of `h` is `-coeff_{D₀} Θ`, for `D₀` the prime divisor of `Y` with generic point `h(η_F)`. -/
private theorem discrepancy_eq_neg_coeff_of_mem_biregularLocus {k : Type u} [Field k]
    [PerfectField k] {Y Y' : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} {h : Y' ⟶ Y}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sY]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [IsDominant h]
    {nK : ℕ} (hnY : topologicalKrullDim Y = nK) {K : Divisor Y} {Θ : QDivisor Y}
    {hY' : IsNormalVariety k (h ≫ sY)} {hbir : IsBirationalMorphism h}
    {F : MMP.Mori.PrimeDivisor Y'} {D₀ : MMP.Mori.PrimeDivisor Y}
    (hV : h F.genericPoint ∈ biregularLocus h) (hη : h F.genericPoint = D₀.genericPoint) {q : ℚ}
    (hq : IsDiscrepancy sY nK K Θ ⟨Y', h, hY', hbir, F⟩ q) : q = -Θ.coeff D₀ := by
  obtain ⟨-, -, m, hm, -, U, hU, τ, hτ, hτa⟩ := hq
  have : IsIso (h.stalkMap F.genericPoint) :=
    MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus h hV
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hnY
  have e1 : (DivisorOver.ordPullback (⟨Y', h, hY', hbir, F⟩ : DivisorOver k sY) τ)
      = D₀.ordForm τ :=
    MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso h
      hbir.functionFieldMap_bijective hd F D₀ hη τ
  have hU' : h F.genericPoint ∈ U := hU
  have e2 := hτ.2 D₀ ⟨D₀.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support D₀, hη ▸ hU'⟩
  rw [e1] at hτa
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm0
  linear_combination hτa + e2

/-- `(h ≫ f)⁻¹_* Δ - b` is the crepant boundary on `Y'` of `(Y, Θ)`, for `Θ = f⁻¹_* Δ - a`. -/
private theorem isCrepantBoundary_inverseTransformDivisor_sub {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [PerfectField k] {Y' : Scheme.{u}} {f : Y ⟶ X}
    {h : Y' ⟶ Y}
    [QuasiCompact (f ≫ sX)] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Y'] [IsNormal Y']
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (hh : IsSmoothResolution (f ≫ sX) h)
    {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    (ha : IsNumericalPullbackSolution sX f K Δ a)
    {b : QDivisor Y'}
    (hbsupp : ∀ P ∈ b.support, IsExceptionalCurve (h ≫ f) P.idealSheaf)
    (hbE : ∀ (E : MMP.Mori.PrimeDivisor Y) (C : MMP.Mori.PrimeDivisor Y'),
      IsExceptionalCurve f E.idealSheaf →
        C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support → b C = a E)
    (hbF : ∀ F : MMP.Mori.PrimeDivisor Y', IsExceptionalCurve h F.idealSheaf →
        ∃ n : ℕ, IsDiscrepancy (f ≫ sX) n K (logPullback f Δ a)
          ⟨Y', h, (hh.isNormalVariety (hf.isNormalVariety hX).1).1, hh.isBirationalMorphism, F⟩
          (b F))
    {nK : ℕ} (hK : K.IsCanonicalDivisor (f ≫ sX) nK) :
    IsCrepantBoundary (f ≫ sX) nK K (logPullback f Δ a) h
      (hh.isNormalVariety (hf.isNormalVariety hX).1).1 hh.isBirationalMorphism
      (inverseTransformDivisor (h ≫ f) Δ - b) := by
  classical
  obtain ⟨hcomp, -, -, hiff⟩ :=
    isSmoothResolution_comp_and_isExceptionalCurve_comp_iff hX hdim hf hh
  have hY := hf.isNormalVariety hX
  have hY' := hh.isNormalVariety hY.1
  have hP : IsPair (f ≫ sX) (logPullback f Δ a) := isPair_of_isSmoothResolution hX hf hK _
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.1.toLocallyOfFiniteType
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsIntegral Y' := hY'.1.1.toIsIntegral
  have : IsDominant h := hh.isBirationalMorphism.isDominant
  have hnY : topologicalKrullDim Y = nK := hK.topologicalKrullDim_eq
  intro F
  obtain ⟨q, hq⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    ⟨Y', h, hY'.1, hh.isBirationalMorphism, F⟩
  suffices hqF : q = -(inverseTransformDivisor (h ≫ f) Δ - b).coeff F by rwa [← hqF]
  by_cases hF : IsExceptionalCurve h F.idealSheaf
  · -- an `h`-exceptional curve: the entry of `b` is the discrepancy
    obtain ⟨n₁, hb₁⟩ := hbF F hF
    obtain rfl : n₁ = nK := by exact_mod_cast hb₁.2.1.topologicalKrullDim_eq.symm.trans hnY
    have h0 := inverseTransformDivisor_apply_eq_zero_of_isExceptionalCurve hX hdim hcomp Δ
      ((hiff _).2 (Or.inr hF))
    rw [IsDiscrepancy.eq hq hb₁]
    change b F = -(inverseTransformDivisor (h ≫ f) Δ F - b F)
    rw [h0]
    ring
  · -- otherwise `F` is the transform of the prime divisor `D₀` through `h(η_F)`
    have hV := map_genericPoint_mem_biregularLocus hY.1 (hY.2.1.trans hdim) hh F hF
    have hco : Order.coheight (h F.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus h hV]
      exact F.coheight_genericPoint
    set D₀ : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
    have hη : h F.genericPoint = D₀.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    have hD₀ : inverseTransformPrimeDivisor h D₀ = some F :=
      MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη hV
    rw [discrepancy_eq_neg_coeff_of_mem_biregularLocus hnY hV hη hq]
    change -(inverseTransformDivisor f Δ - a) D₀ =
      -(inverseTransformDivisor (h ≫ f) Δ F - b F)
    rw [Finsupp.sub_apply, inverseTransformDivisor_comp_apply_of_map_genericPoint hX hdim hf hcomp
      Δ hη, apply_eq_of_inverseTransformPrimeDivisor_eq_some hX hdim hf hh ha.2.2.1 hbsupp hbE hF
      hη hD₀]

/-- **`m(K' + h⁻¹_* Θ - ∑ a(F, Y, Θ) F)` is the pull-back of `m(K_Y + Θ)`**, for a suitable
canonical divisor `K''` of `Y'` in place of `K'`: the discrepancies `a(F, Y, Θ)` are the orders
along the `h`-exceptional `F` of the pulled-back local generators of `𝒪_Y(m(K_Y + Θ))`, and off
the `h`-exceptional curves `h` is an isomorphism at the generic points. -/
private theorem exists_isPullback_logPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [PerfectField k] {Y' : Scheme.{u}} {f : Y ⟶ X}
    {h : Y' ⟶ Y}
    [QuasiCompact (f ≫ sX)] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [QuasiCompact ((h ≫ f) ≫ sX)] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (hh : IsSmoothResolution (f ≫ sX) h)
    {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    (ha : IsNumericalPullbackSolution sX f K Δ a)
    {b : QDivisor Y'}
    (hbsupp : ∀ P ∈ b.support, IsExceptionalCurve (h ≫ f) P.idealSheaf)
    (hbE : ∀ (E : MMP.Mori.PrimeDivisor Y) (C : MMP.Mori.PrimeDivisor Y'),
      IsExceptionalCurve f E.idealSheaf →
        C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support → b C = a E)
    (hbF : ∀ F : MMP.Mori.PrimeDivisor Y', IsExceptionalCurve h F.idealSheaf →
        ∃ n : ℕ, IsDiscrepancy (f ≫ sX) n K (logPullback f Δ a)
          ⟨Y', h, (hh.isNormalVariety (hf.isNormalVariety hX).1).1, hh.isBirationalMorphism, F⟩
          (b F)) :
    ∃ (K'' : Divisor Y') (n : ℕ) (_ : K''.IsCanonicalDivisor ((h ≫ f) ≫ sX) n)
      (hLB : ∀ Z : irreducibleComponents Y',
        h (componentGenericPoint Y' Z) ∉ (Divisor.toQDivisor K + logPullback f Δ a).supp),
      (Divisor.toQDivisor K + logPullback f Δ a).IsPullback h hLB
        (Divisor.toQDivisor K'' + (inverseTransformDivisor (h ≫ f) Δ - b)) := by
  classical
  have hY := hf.isNormalVariety hX
  have hY' := hh.isNormalVariety hY.1
  obtain ⟨nK, hK⟩ := ha.2.1
  have hP : IsPair (f ≫ sX) (logPullback f Δ a) := isPair_of_isSmoothResolution hX hf hK _
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.1.toLocallyOfFiniteType
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsIntegral Y' := hY'.1.1.toIsIntegral
  have : LocallyOfFiniteType (h ≫ f ≫ sX) := hY'.1.1.toLocallyOfFiniteType
  have : CompactSpace Y' := by
    have : QuasiCompact (h ≫ f ≫ sX) := hY'.1.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (h ≫ f ≫ sX)
  have hbir := hh.isBirationalMorphism
  have : IsDominant h := hbir.isDominant
  have hnY : topologicalKrullDim Y = nK := hK.topologicalKrullDim_eq
  -- `K = div ω` and `K'' = div (h^* ω)`
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hY.1 hK
  have hdivω : divisorOfForm ω = K := by
    ext Γ
    exact hωK Γ
  set K'' := divisorOfForm (pullbackRationalPluriForms (f ≫ sX) h ω) with hK''_def
  have hK'' : K''.IsCanonicalDivisor (h ≫ f ≫ sX) nK := by
    have : MMP.Mori.IsVariety k (h ≫ f ≫ sX) := hY'.1.1
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (h ≫ f ≫ sX)
      hh.isSmoothScheme (n := nK) (hY'.2.1.trans hnY)
    have hl := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY'.1 hK₀
      (pullbackRationalPluriForms_ne_zero (f ≫ sX) hnY h hbir hω0)
    rw [one_smul] at hl
    exact hK₀.of_linearlyEquivalent hl
  obtain ⟨-, -, hB, hpb⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hP h hY'.1 hbir hK
    hK'' (Or.inl ⟨ω, hω0, hdivω, rfl⟩)
    (isCrepantBoundary_inverseTransformDivisor_sub hX hdim hf hh ha hbsupp hbE hbF hK)
  refine ⟨K'', nK, ?_, hB, hpb⟩
  rw [Category.assoc]
  exact hK''

/-- A morphism hits every point of its biregular locus. -/
private theorem biregularLocus_subset_range {Z W : Scheme.{u}} (g : Z ⟶ W) :
    (biregularLocus g : Set W) ⊆ Set.range g.base := by
  intro y hy
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  obtain ⟨x, hx⟩ := (Scheme.Hom.homeomorph (g ∣_ biregularLocus g)).surjective ⟨y, hy⟩
  exact ⟨x.1, by rw [← morphismRestrict_base_coe]; exact congrArg Subtype.val hx⟩

/-- A proper morphism maps the transform `g⁻¹_* T` of an irreducible closed set `T` meeting the
biregular locus onto `T`. -/
private theorem image_inverseTransform {Z W : Scheme.{u}} (g : Z ⟶ W) [IsProper g]
    {T : Closeds W} (hT : IsIrreducible (T : Set W))
    (hne : ((T : Set W) ∩ biregularLocus g).Nonempty) :
    g.base '' (inverseTransform g T : Set Z) = T := by
  change g.base '' closure (g.base ⁻¹' ((T : Set W) ∩ biregularLocus g)) = T
  rw [← IsClosedMap.closure_image_eq_of_continuous g.isClosedMap g.continuous,
    Set.image_preimage_eq_inter_range,
    Set.inter_eq_left.2 (Set.inter_subset_right.trans (biregularLocus_subset_range g))]
  obtain ⟨x, hx⟩ := QuasiSober.sober hT T.isClosed
  refine le_antisymm (closure_minimal Set.inter_subset_left T.isClosed) ?_
  have hxU : x ∈ (biregularLocus g : Set W) :=
    (hx.mem_open_set_iff (biregularLocus g).isOpen).2 hne
  rw [← hx.def]
  exact closure_mono (Set.singleton_subset_iff.2 ⟨subset_closure rfl, hxU⟩)

/-- The transform `h⁻¹_* E` of a prime divisor `E`, when it is a prime divisor, meets the
preimage of the biregular locus. -/
private theorem exists_mem_support_preimage_biregularLocus {Y Y' : Scheme.{u}} {h : Y' ⟶ Y}
    {E : MMP.Mori.PrimeDivisor Y} {C : MMP.Mori.PrimeDivisor Y'}
    (hC : C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support) :
    ((E.idealSheaf.support : Set Y) ∩ biregularLocus h).Nonempty := by
  by_contra hne
  have := inverseTransformPrimeDivisor_eq_some_of_idealSheaf_eq hC
  exact hne (inverseTransformPrimeDivisor_eq_some_iff.1 this).1

/-- The proper morphism `h` maps the transform `C = h⁻¹_* E` onto `E`, so the scheme-theoretic
image of `C` is `E`. -/
private theorem ker_subschemeι_comp_eq {Y Y' : Scheme.{u}} {h : Y' ⟶ Y}
    {E : MMP.Mori.PrimeDivisor Y} {C : MMP.Mori.PrimeDivisor Y'} [IsProper h]
    (hC : C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support) :
    (C.idealSheaf.subschemeι ≫ h).ker = E.idealSheaf := by
  have := C.integral
  have := E.integral
  have hirr : IsIrreducible (E.idealSheaf.support : Set Y) := by
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      E.idealSheaf.subschemeι.continuous.continuousOn
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E.idealSheaf _ rfl]
  congr 1
  refine Closeds.ext ?_
  rw [Closeds.coe_closure, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι, hC, support_inverseTransformIdeal,
    image_inverseTransform h hirr (exists_mem_support_preimage_biregularLocus hC),
    E.idealSheaf.support.isClosed.closure_eq]

/-- `h` maps the transform `C = h⁻¹_* E` birationally onto `E`: the degree of `C` over its image
is one, since `h` is a local isomorphism at the generic point of `C`. -/
private theorem degreeOver_toImage_subschemeι_comp_eq_one {Y Y' : Scheme.{u}} {h : Y' ⟶ Y}
    {E : MMP.Mori.PrimeDivisor Y} {C : MMP.Mori.PrimeDivisor Y'} [IsProper h]
    [IsIntegral C.idealSheaf.subscheme]
    (hC : C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support) :
    degreeOver (C.idealSheaf.subschemeι ≫ h).toImage = 1 := by
  set i := C.idealSheaf.subschemeι
  set ξ := genericPoint C.idealSheaf.subscheme
  have hgen : IsGenericPoint (i ξ) (C.idealSheaf.support : Set Y') := by
    have h1 := (genericPoint_spec C.idealSheaf.subscheme).image i.continuous
    rwa [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
      C.idealSheaf.support.isClosed.closure_eq] at h1
  have hU : h (i ξ) ∈ biregularLocus h := by
    refine (hgen.mem_open_set_iff (h ⁻¹ᵁ biregularLocus h).isOpen).2 ?_
    obtain ⟨y, hyE, hyU⟩ := exists_mem_support_preimage_biregularLocus hC
    obtain ⟨x, rfl⟩ := biregularLocus_subset_range h hyU
    refine ⟨x, ?_, hyU⟩
    rw [hC, support_inverseTransformIdeal]
    exact preimage_subset_inverseTransform h _ ⟨hyE, hyU⟩
  have := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus h hU
  have h2 := residueDegree_comp (i ≫ h).toImage (i ≫ h).imageι ξ
  rw [Scheme.Hom.toImage_imageι, residueDegree_comp,
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion i,
    residueDegree_eq_one_of_isIso_stalkMap h,
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (i ≫ h).imageι, one_mul,
    residueDegree_genericPoint_eq_degreeOver] at h2
  simpa using h2.symm

/-- The intersection number along a closed subscheme depends only on its ideal sheaf. -/
private theorem intersectionNumber_subschemeι_congr {k : Type u} [Field k] {Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)}
    [QuasiCompact sZ] [IsLocallyNoetherian Z] [IsNormal Z] {I J : Z.IdealSheafData} (hIJ : I = J)
    [IsProper (I.subschemeι ≫ sZ)] [IsProper (J.subschemeι ≫ sZ)]
    (hI : topologicalKrullDim I.subscheme ≤ 1) (hJ : topologicalKrullDim J.subscheme ≤ 1)
    (D : QDivisor Z) (hD : D.IsQCartier) :
    D.intersectionNumber k sZ I.subschemeι hI hD =
      D.intersectionNumber k sZ J.subschemeι hJ hD := by
  subst hIJ
  rfl

/-- **`(h^* L · h⁻¹_* E) = (L · E)`** for an `f`-exceptional curve `E`: `h` maps the strict
transform `h⁻¹_* E` birationally onto `E`, so the projection formula
(`MMP.Mori.intersectionNumber_pullback_eq_degreeOver_mul`) holds with degree `1`. -/
private theorem isIntersectionNumber_pullback_inverseTransform {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {Y' : Scheme.{u}}
    {f : Y ⟶ X} {h : Y' ⟶ Y} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    [QuasiCompact ((h ≫ f) ≫ sX)] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (hh : IsSmoothResolution (f ≫ sX) h) {L : QDivisor Y}
    (hL : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ L.supp}
    {L' : QDivisor Y'} (hpb : L.IsPullback h hLB L') {E : MMP.Mori.PrimeDivisor Y}
    (hE : IsExceptionalCurve f E.idealSheaf) {C : MMP.Mori.PrimeDivisor Y'}
    (hC : C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support) {x : ℚ}
    (hx : IsIntersectionNumber (f ≫ sX) L E.idealSheaf x) :
    IsIntersectionNumber ((h ≫ f) ≫ sX) L' C.idealSheaf x := by
  obtain ⟨hcomp, -, -, hiff⟩ :=
    isSmoothResolution_comp_and_isExceptionalCurve_comp_iff hX hdim hf hh
  have hCex : IsExceptionalCurve (h ≫ f) C.idealSheaf := (hiff _).2 (Or.inl ⟨E.idealSheaf, hE, hC⟩)
  have hp := isProper_of_isExceptionalCurve hX hdim hcomp hCex
  have hY := hf.isNormalVariety hX
  have hY' := hh.isNormalVariety hY.1
  have : MMP.Mori.IsVariety k (f ≫ sX) := hY.1.1
  have : MMP.Mori.IsVariety k ((h ≫ f) ≫ sX) := hY'.1.1
  have : IsProper h := hh.isProper
  have := hCex.1.1
  have := isCurve_subschemeι_comp (sW := (h ≫ f) ≫ sX) hY'.1.1 hCex.1
  obtain ⟨hpE, hdE, hLE, rfl⟩ := hx
  have hEc := isCurve_subschemeι_comp hY.1.1 hE.1
  have hker := ker_subschemeι_comp_eq hC
  have hcurve : AlgebraicGeometry.IsCurve k
      ((C.idealSheaf.subschemeι ≫ h).imageι ≫ f ≫ sX) := by
    change AlgebraicGeometry.IsCurve k ((C.idealSheaf.subschemeι ≫ h).ker.subschemeι ≫ f ≫ sX)
    rw [hker]
    exact hEc
  refine ⟨hp, hCex.1.2.le, hpb.isQCartier hL, ?_⟩
  rw [intersectionNumber_pullback_eq_degreeOver_mul k ((h ≫ f) ≫ sX) (f ≫ sX) h
    (Category.assoc h f sX).symm C.idealSheaf.subschemeι hL hpb hcurve,
    degreeOver_toImage_subschemeι_comp_eq_one hC, Nat.cast_one, one_mul]
  have : IsProper ((C.idealSheaf.subschemeι ≫ h).ker.subschemeι ≫ f ≫ sX) := by
    rw [hker]
    exact hpE
  exact intersectionNumber_subschemeι_congr hker _ _ _ _

/-- **The numerical pull-back equations on `h ≫ f`.** If `b` agrees with `a` on the transforms
of the `f`-exceptional curves and carries the discrepancies `a(F, Y, Θ)` of the log pull-back
`Θ = f⁻¹_* Δ - a` on the `h`-exceptional curves, then `(K' + (h ≫ f)⁻¹_* Δ - b) · C = 0` for
every `(h ≫ f)`-exceptional curve `C`: the divisor `K' + h⁻¹_* Θ - ∑ a(F, Y, Θ) F` is
`ℚ`-linearly equivalent to `h^*(K_Y + Θ)`, which is trivial on the `h`-exceptional curves and
meets `h⁻¹_* E_j` as `K_Y + Θ` meets `E_j`, that is, trivially by the equations for `a`. -/
private theorem numerical_equations_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [PerfectField k] {Y' : Scheme.{u}} {f : Y ⟶ X}
    {h : Y' ⟶ Y}
    [QuasiCompact (f ≫ sX)] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [QuasiCompact ((h ≫ f) ≫ sX)] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (hh : IsSmoothResolution (f ≫ sX) h)
    {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    (ha : IsNumericalPullbackSolution sX f K Δ a)
    {K' : Divisor Y'} (hK' : ∃ n : ℕ, K'.IsCanonicalDivisor ((h ≫ f) ≫ sX) n)
    {b : QDivisor Y'}
    (hbsupp : ∀ P ∈ b.support, IsExceptionalCurve (h ≫ f) P.idealSheaf)
    (hbE : ∀ (E : MMP.Mori.PrimeDivisor Y) (C : MMP.Mori.PrimeDivisor Y'),
      IsExceptionalCurve f E.idealSheaf →
        C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support → b C = a E)
    (hbF : ∀ F : MMP.Mori.PrimeDivisor Y', IsExceptionalCurve h F.idealSheaf →
        ∃ n : ℕ, IsDiscrepancy (f ≫ sX) n K (logPullback f Δ a)
          ⟨Y', h, (hh.isNormalVariety (hf.isNormalVariety hX).1).1, hh.isBirationalMorphism, F⟩
          (b F))
    (Cj : MMP.Mori.PrimeDivisor Y') (hCj : IsExceptionalCurve (h ≫ f) Cj.idealSheaf) :
    ∃ (c : MMP.Mori.PrimeDivisor Y' → ℚ) (e : ℚ),
      (∀ Ci ∈ b.support,
        IsIntersectionNumber ((h ≫ f) ≫ sX) (Finsupp.single Ci 1) Cj.idealSheaf (c Ci)) ∧
      IsIntersectionNumber ((h ≫ f) ≫ sX)
        (Divisor.toQDivisor K' + inverseTransformDivisor (h ≫ f) Δ) Cj.idealSheaf e ∧
      ∑ Ci ∈ b.support, b Ci * c Ci = e := by
  obtain ⟨hcomp, -, -, hiff⟩ :=
    isSmoothResolution_comp_and_isExceptionalCurve_comp_iff hX hdim hf hh
  have hL : (Divisor.toQDivisor K + logPullback f Δ a).IsQCartier :=
    MMP.Fourfold.isQCartier_of_isSmoothScheme hf.isSmoothScheme _
  obtain ⟨K'', n'', hK'', hLB, hpb⟩ :=
    exists_isPullback_logPullback hX hdim hf hh ha hbsupp hbE hbF
  have hN'' : IsIntersectionNumber ((h ≫ f) ≫ sX)
      (Divisor.toQDivisor K'' + (inverseTransformDivisor (h ≫ f) Δ - b)) Cj.idealSheaf 0 := by
    rcases (hiff _).1 hCj with ⟨E, hE, hCE⟩ | hF
    · obtain ⟨Ep, rfl⟩ := exists_primeDivisor_idealSheaf_eq hX hdim hf hE
      exact isIntersectionNumber_pullback_inverseTransform hX hdim hf hh hL hpb hE hCE
        (isIntersectionNumber_logPullback_eq_zero ha hE)
    · exact isIntersectionNumber_pullback_of_isExceptionalCurve hX hdim hf hh hL hpb hF
  obtain ⟨n', hK'⟩ := hK'
  have hv := (hcomp.isNormalVariety hX).1.1
  have : IsIntegral Y' := hv.toIsIntegral
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace ((h ≫ f) ≫ sX)
  have hn : n'' = n' := by
    have h1 := hK''.topologicalKrullDim_eq
    have h2 := hK'.topologicalKrullDim_eq
    exact_mod_cast h1.symm.trans h2
  subst hn
  have hN := MMP.Flips.isIntersectionNumber_add_of_linearlyEquivalent
    (MMP.Flips.linearlyEquivalent_of_isCanonicalDivisor hcomp.isSmoothScheme hK'' hK') hN''
  rw [← add_sub_assoc] at hN
  exact numerical_equations_of_isIntersectionNumber_sub hX hdim hcomp hCj hN

variable {k : Type u} [Field k] {X Y Y' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- **Numerical discrepancies on a composite resolution** (implicit in KM 4.5, 4.7, 4.15). Let
`f : Y ⟶ X` be a resolution of a normal surface `X`, `h : Y' ⟶ Y` a proper birational morphism
from a smooth surface, and `a` a solution of the numerical pull-back equations of `(X, Δ)` on `f`
for the canonical divisor `K` of `Y`. For any canonical divisor `K'` of `Y'` there is a solution
`b` of the numerical pull-back equations of `(X, Δ)` on `h ≫ f` whose entry at the transform
`h⁻¹_* E` of an `f`-exceptional curve `E` is `a E`, and whose entry at an `h`-exceptional curve
`F` is the discrepancy `a(F, Y, Θ)` of the log pull-back `Θ = logPullback f Δ a`. -/
@[mmp "lem_km4a_numerical_discrepancy_composite"]
public theorem IsNumericalPullbackSolution.exists_isNumericalPullbackSolution_comp
    [PerfectField k] {f : Y ⟶ X} {h : Y' ⟶ Y}
    [QuasiCompact (f ≫ sX)] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [QuasiCompact ((h ≫ f) ≫ sX)] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsSmoothResolution sX f) (hh : IsSmoothResolution (f ≫ sX) h)
    {K : Divisor Y} {Δ : QDivisor X} {a : QDivisor Y}
    (ha : IsNumericalPullbackSolution sX f K Δ a)
    {K' : Divisor Y'} (hK' : ∃ n : ℕ, K'.IsCanonicalDivisor ((h ≫ f) ≫ sX) n) :
    ∃ b : QDivisor Y', IsNumericalPullbackSolution sX (h ≫ f) K' Δ b ∧
      (∀ (E : PrimeDivisor Y) (C : PrimeDivisor Y'), IsExceptionalCurve f E.idealSheaf →
        C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support → b C = a E) ∧
      ∀ F : PrimeDivisor Y', IsExceptionalCurve h F.idealSheaf →
        ∃ n : ℕ, IsDiscrepancy (f ≫ sX) n K (logPullback f Δ a)
          ⟨Y', h, (hh.isNormalVariety (hf.isNormalVariety hX).1).1, hh.isBirationalMorphism, F⟩
          (b F) := by
  classical
  obtain ⟨hcomp, htr, hinj, hiff⟩ :=
    isSmoothResolution_comp_and_isExceptionalCurve_comp_iff hX hdim hf hh
  have hfin := finite_setOf_isExceptionalCurve hX hdim hf hh
  obtain ⟨nK, hK⟩ := ha.2.1
  have hP := isPair_of_isSmoothResolution hX hf hK (logPullback f Δ a)
  have hdisc : ∀ F : MMP.Mori.PrimeDivisor Y', ∃ q : ℚ, IsDiscrepancy (f ≫ sX) nK K
      (logPullback f Δ a)
      ⟨Y', h, (hh.isNormalVariety (hf.isNormalVariety hX).1).1, hh.isBirationalMorphism, F⟩ q :=
    fun F => MMP.Positivity.IsPair.exists_isDiscrepancy hP hK _
  choose q hq using hdisc
  let d : QDivisor Y' := ∑ F ∈ hfin.toFinset, Finsupp.single F (q F)
  have hd : ∀ P, d P = if IsExceptionalCurve h P.idealSheaf then q P else 0 := by
    intro P
    simp only [d, Finsupp.finset_sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    simp
  have haE := ha.2.2.1
  let b : QDivisor Y' := inverseTransformDivisor h a + d
  have hbE : ∀ (E : MMP.Mori.PrimeDivisor Y) (C : MMP.Mori.PrimeDivisor Y'),
      IsExceptionalCurve f E.idealSheaf →
        C.idealSheaf = inverseTransformIdeal h E.idealSheaf.support → b C = a E := by
    intro E C hE hC
    have hnot : ¬ IsExceptionalCurve h C.idealSheaf := hC ▸ (htr _ hE).2
    simp only [b, Finsupp.add_apply, hd, hnot, if_false, add_zero]
    exact inverseTransformDivisor_apply_of_idealSheaf_eq hinj haE hE hC
  have hbF : ∀ F : MMP.Mori.PrimeDivisor Y', IsExceptionalCurve h F.idealSheaf →
      ∃ n : ℕ, IsDiscrepancy (f ≫ sX) n K (logPullback f Δ a)
        ⟨Y', h, (hh.isNormalVariety (hf.isNormalVariety hX).1).1, hh.isBirationalMorphism, F⟩
        (b F) := by
    intro F hF
    refine ⟨nK, ?_⟩
    simp only [b, Finsupp.add_apply, hd, hF, if_true,
      inverseTransformDivisor_apply_of_isExceptionalCurve (fun E hE => (htr E hE).2) haE hF,
      zero_add]
    exact hq F
  have hbsupp : ∀ P ∈ b.support, IsExceptionalCurve (h ≫ f) P.idealSheaf := by
    intro P hP
    rw [Finsupp.mem_support_iff] at hP
    by_cases hPh : IsExceptionalCurve h P.idealSheaf
    · exact (hiff _).2 (Or.inr hPh)
    · have : inverseTransformDivisor h a P ≠ 0 := by
        simpa [b, hd, hPh] using hP
      exact isExceptionalCurve_of_mem_support_inverseTransformDivisor (fun E hE => (htr E hE).1) haE
        (Finsupp.mem_support_iff.2 this)
  refine ⟨b, ⟨hcomp, hK',
    hbsupp, fun Cj hCj => numerical_equations_comp hX hdim hf hh ha hK' hbsupp hbE hbF Cj hCj⟩,
    hbE, hbF⟩

end MMP.Mori

end
