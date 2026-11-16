module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyRestrictOpen
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Weights outside the weighted bad set are unchanged by a flip

Let `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` be a small terminal flip move of a prepared chain, written as a
threefold step diagram `Y⁻ → Z ← Y⁺` with both maps small, with common biregular locus `U ⊆ Z`
and bad loci `W^± = Y^± ∖ (f^±)⁻¹(U)`, and let `𝒜₀` be its weighted bad set. For every
normalized divisorial valuation `v` of `ℂ(Y⁻)` exceptional over `Y⁻` and not in `𝒜₀`, the
weights agree: `w_v(Y⁻, Θ⁻) = w_v(Y⁺, Θ⁺)`, where on `Y⁺` the valuation `v` is read as the
valuation `v⁺` of `ℂ(Y⁺)` with the same restriction to `ℂ(Z)`.

If the centre `c_{Y⁻}(v)` lies in `W⁻`, both weights vanish since `v ∉ 𝒜₀`. Otherwise the centre
meets `U⁻ = (f⁻)⁻¹(U)`, and so does the centre of `v⁺` meet `U⁺ = (f⁺)⁻¹(U)` (both centres lie
over the centre of `v` on `Z`). Over `U` both `f^±` are isomorphisms, and the isomorphism
`U⁻ ≅ U⁺` carries `Θ⁻|_{U⁻}` to `Θ⁺|_{U⁺}` because `Θ⁺` is the strict transform of `Θ⁻`. Log
discrepancies are local at the centre (`MMP.Fourfold.isValuationLogDiscrepancy_restrict_iff`)
and preserved by isomorphisms of pairs, so `a(v; Y⁻, Θ⁻) = a(v⁺; Y⁺, Θ⁺)` and the weights agree.

## Main results

* `MMP.Mori.exists_pullbackRationalPluriForms_eq`: along a morphism inducing an isomorphism of
  function fields, every rational top form is a pull-back.
* `MMP.Fourfold.StabilizedTail.PreparedChain.eq_of_isValuationWeight_of_notMem_flipBadSet`:
  outside the weighted bad set `MMP.Fourfold.StabilizedTail.PreparedChain.flipBadSet` of a flip
  move, the weights of a valuation on the source and on the target agree.

## Implementation notes

Weights are the relation `MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight` at the
admissible scale of the prepared chain; that relation contains that the valuation is a normalized
divisorial valuation exceptional over the model. The statement therefore says that any weight
`w` of `v` on `Y⁻` and any weight `w'` of `v⁺` on `Y⁺` are equal.

The source compares the two log discrepancies through the graph divisor of the step diagram: their
difference is `v(H) ≥ 0`, and it vanishes exactly when the centre is not in `W⁻`. Only the
vanishing is needed here, and it is proved directly: over the common biregular locus the two
pairs are isomorphic.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4], the index of a terminal chain
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

namespace MMP.Mori

/-- **Rational top forms descend along a birational morphism.** If `f : X ⟶ Z` induces an
isomorphism of function fields, every rational top form on `X` is the pull-back `f^* τ` of a
rational top form `τ` on `Z`. -/
theorem exists_pullbackRationalPluriForms_eq {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sZ] (f : X ⟶ Z) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {n : ℕ}
    (hd : letI := functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
    (ω : RationalPluriForms (f ≫ sZ) n 1) :
    ∃ τ : RationalPluriForms sZ n 1, pullbackRationalPluriForms sZ f τ = ω := by
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sZ f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1).repr ω ())
  refine ⟨g • ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1 (), ?_⟩
  change pullbackForms (K := Z.functionField) (K' := X.functionField) 1 _ = ω
  rw [pullbackForms_eq hω₀, pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  change functionFieldMap f g • _ = ω
  rw [hg]
  exact basis_unit_repr_smul _ ω

end MMP.Mori

namespace MMP.Fourfold

/-! ### Divisors over a variety seen over a birational model -/

section CompProper

variable {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']

/-- A divisor `(W, h, E)` over `X`, with `h` proper, seen over `X'` through a proper birational
morphism `g : X ⟶ X'` over `ℂ`: the divisor `(W, g ∘ h, E)`. -/
private noncomputable def compProper {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) : DivisorOver ℂ sX' where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by
    rw [Category.assoc, hs]
    exact D.isNormalVariety
  isBirationalMorphism := by
    haveI := D.isIntegral
    haveI := hD
    exact isBirationalMorphism_comp_of_isBirational g D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  E := D.E

/-- The divisor `(W, g ∘ h, E)` has the valuation `ord_E` read on `k(X')` through `g`. -/
private theorem valuation_compProper {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    (g : X ⟶ X') [IsProper g] (hg : IsBirationalMorphism g) (hs : g ≫ sX' = sX)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) :
    haveI := hg.isDominant
    (compProper g hg hs D hD).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := hg.isDominant
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ g) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

end CompProper

/-! ### Transport of log discrepancies along an isomorphism -/

section Iso

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- Under an isomorphism `f : Y ⟶ X`, every prime divisor `Γ` of `X` is the image of a prime
divisor `P` of `Y`: `f(η_P) = η_Γ`. -/
private theorem exists_primeDivisor_map_genericPoint_eq (f : Y ⟶ X) [IsIso f]
    (Γ : MMP.Mori.PrimeDivisor X) :
    ∃ P : MMP.Mori.PrimeDivisor Y, f P.genericPoint = Γ.genericPoint := by
  set x : Y := (inv f) Γ.genericPoint
  have hx : f x = Γ.genericPoint := by
    simp only [x]
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Γ.coheight_genericPoint] at h
    exact_mod_cast h.symm
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco,
    (congrArg f (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco)).trans hx⟩

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields. -/
private theorem pullbackRationalPluriForms_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower ℂ X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg ℂ Y.functionField).toNat = d := by
    rwa [← trdeg_functionField_eq_of_bijective sX f hf]
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- The only irreducible component of an irreducible space is the whole space. -/
private theorem mem_irreducibleComponent {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 :=
  (Set.eq_univ_of_univ_subset
    (W.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _))).symm ▸ Set.mem_univ t

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent
    (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Log discrepancies are preserved by isomorphisms of pairs.** Let `f : Y ⟶ X` be an
isomorphism carrying the boundary `B_Y` of `Y` to the boundary `B` of `X`, and let `X` have a
canonical divisor of dimension `n`. Then a log discrepancy `a` of a proper divisor `(W, g, E)`
over `(Y, B_Y)` is the log discrepancy of `(W, f ∘ g, E)` over `(X, B)`. -/
private theorem isLogDiscrepancy_compIso [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    (f : Y ⟶ X) [IsIso f] {n : ℕ} {K₀ : Divisor X} (hK₀ : K₀.IsCanonicalDivisor sX n)
    {B : QDivisor X} {BY : QDivisor Y}
    (hB : ∀ (P : MMP.Mori.PrimeDivisor Y) (Γ : MMP.Mori.PrimeDivisor X),
      f P.genericPoint = Γ.genericPoint → BY.coeff P = B.coeff Γ)
    {D : DivisorOver ℂ (f ≫ sX)} (hD : IsProper D.f) {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy (f ≫ sX) n (QDivisor.toRDivisor BY) D a) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      (compProper f (isBirationalMorphism_of_isIso f) rfl D hD) a := by
  obtain ⟨hYv, -, ω, hω0, -, m, r, C, C', hCc, hsum, hpb, rfl⟩ := h
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI := hD
  have hs : inv f ≫ f ≫ sX = sX := by simp
  have hXv : IsNormalVariety ℂ sX := by
    refine ⟨(isVariety_iff ℂ sX).2 ⟨inferInstance, ?_, ?_, ?_⟩, inferInstance⟩
    · haveI := hYv.1.toIsSeparated
      rw [← hs]
      infer_instance
    · haveI := hYv.1.toLocallyOfFiniteType
      rw [← hs]
      infer_instance
    · haveI := hYv.1.toQuasiCompact
      rw [← hs]
      infer_instance
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have hn : topologicalKrullDim X = n := hK₀.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := (isBirationalMorphism_of_isIso f).functionFieldMap_bijective
  obtain ⟨τ, rfl⟩ := exists_pullbackRationalPluriForms_eq f hbij hd ω
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    apply hω0
    let := functionFieldAlgebra sX
    let := functionFieldAlgebra (f ≫ sX)
    let := functionFieldMapAlgebra f
    have := isScalarTower_functionFieldMap sX f
    obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
    rw [pullbackForms_eq hω₀, pullbackFormsAlong, LinearEquiv.map_zero]
    simp
  have hKτ : (divisorOfForm τ).IsCanonicalDivisor sX n := by
    refine hK₀.of_linearlyEquivalent ?_
    simpa only [one_smul] using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hK₀ hτ0
  have hL : ∀ i, ∃ L : Divisor X, L.IsCartier ∧
      L.IsPullback f (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f L) (C i) := by
    intro i
    obtain ⟨L, hLpb⟩ := (hCc i).exists_isPullback (f := inv f)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (inv f) (C i))
    have hLc : L.IsCartier := hLpb.isCartier (hCc i)
    obtain ⟨L₂, hL₂⟩ := hLc.exists_isPullback (f := f)
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp f L)
    refine ⟨L, hLc, ?_⟩
    convert hL₂ using 1
    refine Finsupp.ext fun P => ?_
    obtain ⟨Γ, hΓ⟩ := exists_primeDivisor_map_genericPoint_eq (inv f) P
    have hP : f P.genericPoint = Γ.genericPoint := by
      rw [← hΓ, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    exact (MMP.Positivity.coeff_eq_of_isPullback Γ P hΓ (hCc i) hLpb).symm.trans
      (MMP.Positivity.coeff_eq_of_isPullback P Γ hP hLc hL₂).symm
  choose L hLc hLpb using hL
  refine ⟨hXv, (inferInstance : IsProper (D.f ≫ f)), τ, hτ0,
    ⟨_, hKτ, fun Γ => coeff_divisorOfForm τ Γ⟩, m, r, L, C', hLc,
    fun Γ => ?_, fun i => ?_, ?_⟩
  · obtain ⟨P, hP⟩ := exists_primeDivisor_map_genericPoint_eq f Γ
    have hord := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hbij hd P Γ hP τ
    have hc : ∀ i, (C i).coeff P = (L i).coeff Γ := fun i =>
      MMP.Positivity.coeff_eq_of_isPullback P Γ hP (hLc i) (hLpb i)
    simpa only [QDivisor.coeff_toRDivisor, hord, hB P Γ hP, hc] using hsum P
  · obtain ⟨hC, hCpb⟩ := hpb i
    exact ⟨_, isPullback_comp (hLpb i) hCpb
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ f) (L i))⟩
  · have hcomp := pullbackRationalPluriForms_comp f D.f hbij
      D.isBirationalMorphism.functionFieldMap_bijective hd τ
    change 1 + (D.E.ordForm (pullbackRationalPluriForms (f ≫ sX) D.f
        (pullbackRationalPluriForms sX f τ)) : ℝ) - _ =
      1 + (D.E.ordForm (pullbackRationalPluriForms sX (D.f ≫ f) τ) : ℝ) - _
    rw [hcomp]
    rfl

end Iso

/-! ### Points and prime divisors over a biregular open -/

section Biregular

variable {X Y : Scheme.{0}}

/-- A morphism is injective over an open `V` over which it is an isomorphism. -/
private theorem eq_of_map_eq_of_isBiregular {f : X ⟶ Y} {V : Y.Opens} (hV : IsBiregular f V)
    {x y : X} (hx : f x ∈ V) (hxy : f x = f y) : x = y := by
  have : IsIso (f ∣_ V) := hV
  have h (z : X) (hz : f z ∈ V) : ((f ∣_ V) ≫ V.ι) ⟨z, hz⟩ = f z := by
    rw [morphismRestrict_ι]
    rfl
  exact congrArg Subtype.val (((f ∣_ V) ≫ V.ι).isOpenEmbedding.injective
    ((h x hx).trans (hxy.trans (h y (hxy ▸ hx)).symm)))

/-- A morphism preserves the coheight of points over an open over which it is an isomorphism. -/
private theorem coheight_map_of_isBiregular {f : X ⟶ Y} {V : Y.Opens} (hV : IsBiregular f V)
    {x : X} (hx : f x ∈ V) : Order.coheight (f x) = Order.coheight x := by
  have : IsIso (f ∣_ V) := hV
  let q : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  have h1 : Order.coheight (((f ∣_ V) ≫ V.ι) q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ ((f ∣_ V) ≫ V.ι).isOpenEmbedding
  have h2 : Order.coheight ((f ⁻¹ᵁ V).ι q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ (f ⁻¹ᵁ V).ι.isOpenEmbedding
  have h3 : ((f ∣_ V) ≫ V.ι) q = f x := by
    rw [morphismRestrict_ι]
    rfl
  rw [← h3, h1, ← h2]
  rfl

/-- The image of the generic point of a prime divisor `P` under a morphism which is an
isomorphism over an open `V ∋ f(η_P)` is the generic point of a prime divisor. -/
private theorem exists_primeDivisor_genericPoint_eq_map {f : X ⟶ Y} {V : Y.Opens}
    (hV : IsBiregular f V) {P : MMP.Mori.PrimeDivisor X} (hP : f P.genericPoint ∈ V) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, f P.genericPoint = Q.genericPoint := by
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [coheight_map_of_isBiregular hV hP, P.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩

/-- The coefficient of `g⁻¹_* B` at `P` is that of `B` at `Q` when `g(η_P) = η_Q` lies in the
biregular locus of `g`. -/
private theorem inverseTransformDivisor_apply_of_map_genericPoint {R : Type*} [AddCommMonoid R]
    {g : X ⟶ Y} {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hPQ : g P.genericPoint = Q.genericPoint) (hV : g P.genericPoint ∈ biregularLocus g)
    (B : DivisorWithCoeffs R Y) : inverseTransformDivisor g B P = B Q :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hPQ hV)
    (fun _ hQ' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hQ').1.symm.trans hPQ)) B

/-- The coefficient of `f_* B` at `Q` is that of `B` at `P` when `P` is the only prime divisor
with `f(η_P) = η_Q`. -/
private theorem transformDivisor_apply_of_map_genericPoint [IsReduced X]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {R : Type*} [AddCommMonoid R] {f : X ⟶ Y}
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hPQ : f P.genericPoint = Q.genericPoint)
    (hinj : ∀ E : MMP.Mori.PrimeDivisor X, f E.genericPoint = Q.genericPoint → E = P)
    (B : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (X := X) f.toRationalMap B Q = B P :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hPQ)
    (fun E hE => hinj E ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E Q).mp
      hE)) B

/-- Over the common biregular locus `U` of `f⁻ : X⁻ ⟶ Z ⟵ X⁺ : f⁺`, the strict transform
`(f⁺)⁻¹_* f⁻_* D` has at `P⁺` the coefficient of `D` at `P⁻`, when `f⁻(η_{P⁻}) = f⁺(η_{P⁺}) ∈ U`.
-/
private theorem flipTransform_apply_of_mem_commonBiregularLocus {Xm Xp Z : Scheme.{0}}
    [IsReduced Xm] [IsSeparated (Z ↘ Limits.terminal Scheme)] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    {Pm : MMP.Mori.PrimeDivisor Xm} {Pp : MMP.Mori.PrimeDivisor Xp}
    (h : fm Pm.genericPoint = fp Pp.genericPoint)
    (hU : fp Pp.genericPoint ∈ commonBiregularLocus fm fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Xm) : flipTransform fm fp D Pp = D Pm := by
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_genericPoint_eq_map
    (isBiregular_commonBiregularLocus_right fm fp) hU
  have hVp : fp Pp.genericPoint ∈ biregularLocus fp :=
    le_biregularLocus (isBiregular_commonBiregularLocus_right fm fp) hU
  change inverseTransformDivisor fp (RationalMap.transformDivisor (X := Xm) fm.toRationalMap D) Pp
    = D Pm
  rw [inverseTransformDivisor_apply_of_map_genericPoint hQ hVp]
  refine transformDivisor_apply_of_map_genericPoint (h.trans hQ) (fun E hE => ?_) D
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  refine eq_of_map_eq_of_isBiregular (isBiregular_commonBiregularLocus_left fm fp) ?_
    (hE.trans (h.trans hQ).symm)
  rw [hE, ← hQ]
  exact hU

/-- The coefficient of the restriction `B|_U = ι⁻¹_* B` at a prime divisor `W` of `U` is that of
`B` at the prime divisor of `X` with the same generic point. -/
private theorem inverseTransformDivisor_ι_apply {R : Type*} [AddCommMonoid R] (U : X.Opens)
    (B : DivisorWithCoeffs R X) {W : MMP.Mori.PrimeDivisor U.toScheme} {Q : MMP.Mori.PrimeDivisor X}
    (hWQ : U.ι W.genericPoint = Q.genericPoint) : inverseTransformDivisor U.ι B W = B Q := by
  have hiso : IsIso (U.ι ∣_ U) := by
    have : Surjective (U.ι ∣_ U) := by
      refine ⟨fun y => ?_⟩
      let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
      refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
      have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
      rw [morphismRestrict_ι] at this
      exact this.symm
    exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)
  exact inverseTransformDivisor_apply_of_map_genericPoint hWQ
    (le_biregularLocus hiso (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩)) B

/-- Every prime divisor `W` of an open subscheme `U ⊆ X` has the generic point of a prime
divisor of `X`. -/
private theorem exists_primeDivisor_ι_genericPoint (U : X.Opens)
    (W : MMP.Mori.PrimeDivisor U.toScheme) :
    ∃ Q : MMP.Mori.PrimeDivisor X, U.ι W.genericPoint = Q.genericPoint := by
  have hco : Order.coheight (U.ι W.genericPoint) = 1 := by
    rw [Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding, W.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩

end Biregular

/-! ### Valuations of function fields -/

section Valuations

/-- Pulling a valuation back along a composite: `ξ ∘ (a ≫ b)^* = (ξ ∘ a^*) ∘ b^*`. -/
private theorem comap_functionFieldMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)]
    (ξ : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    ξ.comap (functionFieldMap (a ≫ b)) =
      (ξ.comap (functionFieldMap a)).comap (functionFieldMap b) := by
  ext t
  simp only [Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- Pulling valuations back along a surjective ring homomorphism is injective. -/
private theorem comap_injective_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Surjective f) :
    Function.Injective fun ξ : Valuation S (WithZero (Multiplicative ℤ)) => ξ.comap f := by
  intro ξ ξ' h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congrArg (fun ν : Valuation R (WithZero (Multiplicative ℤ)) => ν y) h

/-- Every valuation of `k(X)` is read on `k(U) = k(X)` for a nonempty open `U ⊆ X`. -/
private theorem exists_comap_functionFieldMap_ι_eq {X : Scheme.{0}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))) :
    haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
    ∃ ξU : Valuation U.toScheme.functionField (WithZero (Multiplicative ℤ)),
      ξU.comap (functionFieldMap U.ι) = ξ := by
  haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
  have hbij := functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
    ⟨_, Set.mem_univ (Classical.arbitrary U)⟩
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) hbij
  refine ⟨ξ.comap e.symm.toRingHom, ?_⟩
  ext t
  simp only [Valuation.comap_apply]
  change ξ (e.symm (e t)) = ξ t
  rw [RingEquiv.symm_apply_apply]

end Valuations

/-! ### Comparison of log discrepancies over the common biregular locus -/

section Comparison

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
  [CompactSpace Xm] [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [CompactSpace Xp]
  [IsIntegral Z]

/-- **Log discrepancies over the common biregular locus.** Let `f⁻ : X⁻ ⟶ Z ⟵ X⁺ : f⁺` be proper
birational morphisms over `ℂ` to a normal variety, with common biregular locus `U`, and let
`(X^±, B^±)` be pairs such that `B⁺` and `B⁻` have the same coefficient at prime divisors with
the same generic point over `U`. If the centre of a normal divisorial valuation `v` of `k(X⁻)` is
not contained in the bad locus `W⁻ = X⁻ ∖ (f⁻)⁻¹(U)`, and `v⁺` is the valuation of `k(X⁺)` with
the same restriction to `k(Z)`, then `a(v; X⁻, B⁻) = a(v⁺; X⁺, B⁺)`. -/
private theorem eq_of_isValuationLogDiscrepancy {sXm : Xm ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ)
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsProper fm] [IsProper fp]
    (hbm : IsBirationalMorphism fm) (hbp : IsBirationalMorphism fp)
    (hm : fm ≫ sZ = sXm) (hp : fp ≫ sZ = sXp)
    {Bm : QDivisor Xm} {Bp : QDivisor Xp} (hBm : IsPair sXm Bm)
    (hBp : IsPair sXp Bp)
    (hB : ∀ (Pm : MMP.Mori.PrimeDivisor Xm) (Pp : MMP.Mori.PrimeDivisor Xp),
      fm Pm.genericPoint = fp Pp.genericPoint →
        fp Pp.genericPoint ∈ commonBiregularLocus fm fp → Bp.coeff Pp = Bm.coeff Pm)
    {v : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hv' : haveI := hbm.isDominant
      haveI := hbp.isDominant
      v'.comap (functionFieldMap fp) = v.comap (functionFieldMap fm))
    {Zc : IrreducibleCloseds Xm} (hZc : MMP.Intersection.IsCentre ℂ sXm v Zc)
    (hZU : ¬ (Zc : Set Xm) ⊆ badLocusMinus fm fp)
    {a a' : ℝ} (ha : IsValuationLogDiscrepancy sXm Bm v a)
    (ha' : IsValuationLogDiscrepancy sXp Bp v' a') : a = a' := by
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hXm := hBm.isPair.1
  set Uc := commonBiregularLocus fm fp
  obtain ⟨n, D, hDp, hDv, hl⟩ := ha
  obtain ⟨n', D', hD'p, hD'v, hl'⟩ := ha'
  -- the centre of `v` meets `(f⁻)⁻¹(U)`, so `f⁻` maps the generic point of the centre into `U`
  have hη : fm (D.f D.E.genericPoint) ∈ Uc := by
    obtain ⟨D₀, -, hv₀, rfl⟩ := hZc
    have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXm (hDv.trans hv₀)
    rw [Set.not_subset] at hZU
    obtain ⟨y, hy, hyW⟩ := hZU
    have hyU : y ∈ fm ⁻¹ᵁ Uc := by simpa [badLocusMinus] using hyW
    rw [D₀.center_eq_closure_genericPoint, ← hc] at hy
    exact (specializes_iff_mem_closure.mpr hy).mem_open (fm ⁻¹ᵁ Uc).isOpen hyU
  -- the centres of `v` and `v⁺` lie over the same point of `Z`
  have hη' : fp (D'.f D'.E.genericPoint) = fm (D.f D.E.genericPoint) :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hZ
      (D := compProper fp hbp hp D' hD'p) (D' := compProper fm hbm hm D hDp) (by
        rw [valuation_compProper, valuation_compProper, hDv, hD'v, hv'])
  have hη'U : fp (D'.f D'.E.genericPoint) ∈ Uc := hη' ▸ hη
  set Um : Xm.Opens := fm ⁻¹ᵁ Uc
  set Up : Xp.Opens := fp ⁻¹ᵁ Uc
  haveI : Nonempty Um := ⟨⟨_, hη⟩⟩
  haveI : Nonempty Up := ⟨⟨_, hη'U⟩⟩
  haveI := Opens.isDominant_ι (Um.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty Um›))
  haveI := Opens.isDominant_ι (Up.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty Up›))
  haveI : IsNoetherian Xp := {}
  haveI : CompactSpace Up := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  obtain ⟨vU, hvU⟩ := exists_comap_functionFieldMap_ι_eq Um v
  obtain ⟨vU', hvU'⟩ := exists_comap_functionFieldMap_ι_eq Up v'
  have hmemc : D.f D.E.genericPoint ∈ (D.center : Set Xm) := by
    rw [D.center_eq_closure_genericPoint]
    exact subset_closure rfl
  have hmemc' : D'.f D'.E.genericPoint ∈ (D'.center : Set Xp) := by
    rw [D'.center_eq_closure_genericPoint]
    exact subset_closure rfl
  have hUm := (isValuationLogDiscrepancy_restrict_iff sXm hBm ⟨D, hDp, hDv.symm⟩
    ⟨D, hDp, hDv.symm, rfl⟩ Um ⟨_, hη, hmemc⟩ hvU a).2 ⟨n, D, hDp, hDv, hl⟩
  have hUp := (isValuationLogDiscrepancy_restrict_iff sXp hBp ⟨D', hD'p, hD'v.symm⟩
    ⟨D', hD'p, hD'v.symm, rfl⟩ Up ⟨_, hη'U, hmemc'⟩ hvU' a').2 ⟨n', D', hD'p, hD'v, hl'⟩
  -- the isomorphism `φ : U⁻ ≅ U⁺` over `U`
  haveI : IsIso (fm ∣_ Uc) := isBiregular_commonBiregularLocus_left fm fp
  haveI : IsIso (fp ∣_ Uc) := isBiregular_commonBiregularLocus_right fm fp
  let φ : Um.toScheme ⟶ Up.toScheme := (fm ∣_ Uc) ≫ inv (fp ∣_ Uc)
  have hφ : φ ≫ (fp ∣_ Uc) = fm ∣_ Uc := by simp [φ]
  have hφι : φ ≫ Up.ι ≫ fp = Um.ι ≫ fm := by
    rw [← morphismRestrict_ι fp Uc, ← Category.assoc, hφ, morphismRestrict_ι]
  have hs : φ ≫ Up.ι ≫ sXp = Um.ι ≫ sXm := by
    rw [← hp, ← hm, ← Category.assoc Up.ι, ← Category.assoc φ, ← Category.assoc Um.ι, hφι]
  rw [← hs] at hUm
  obtain ⟨nU, DU, hDUp, hDUv, hlU⟩ := hUm
  obtain ⟨np, Dp, -, hDpv, hlp⟩ := hUp
  obtain ⟨-, -, -, -, ⟨Kp, hKp, -⟩, -⟩ := id hlp
  have hn : np = nU := by
    have h1 := hKp.topologicalKrullDim_eq
    have h2 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hlU
    rw [← IsHomeomorph.topologicalKrullDim_eq _ φ.homeomorph.isHomeomorph, h2] at h1
    exact_mod_cast h1.symm
  subst hn
  have hBφ : ∀ (P : MMP.Mori.PrimeDivisor Um.toScheme) (Γ : MMP.Mori.PrimeDivisor Up.toScheme),
      φ P.genericPoint = Γ.genericPoint →
        (inverseTransformDivisor Um.ι Bm).coeff P = (inverseTransformDivisor Up.ι Bp).coeff Γ := by
    intro P Γ hPΓ
    obtain ⟨Pm, hPm⟩ := exists_primeDivisor_ι_genericPoint Um P
    obtain ⟨Pp, hPp⟩ := exists_primeDivisor_ι_genericPoint Up Γ
    change inverseTransformDivisor Um.ι Bm P = inverseTransformDivisor Up.ι Bp Γ
    rw [inverseTransformDivisor_ι_apply Um Bm hPm, inverseTransformDivisor_ι_apply Up Bp hPp]
    have heq : fm Pm.genericPoint = fp Pp.genericPoint := by
      rw [← hPm, ← hPp, ← hPΓ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        ← Scheme.Hom.comp_apply, ← hφι]
    have hmem : fp Pp.genericPoint ∈ Uc := by
      rw [← hPp]
      exact Γ.genericPoint.2
    exact (hB Pm Pp heq hmem).symm
  have hiso := isLogDiscrepancy_compIso φ hKp hBφ hDUp hlU
  refine MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hiso hlp ?_
  rw [valuation_compProper, hDUv, hDpv]
  have hsurj : Function.Surjective (functionFieldMap (Up.ι ≫ fp)) := by
    intro t
    obtain ⟨s, rfl⟩ := (functionFieldMap_bijective_of_isOpenImmersion Up.ι ⊤
      ⟨_, Set.mem_univ (Classical.arbitrary Up)⟩).2 t
    obtain ⟨r, rfl⟩ := hbp.functionFieldMap_bijective.2 s
    exact ⟨r, (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply Up.ι fp r).symm⟩
  apply comap_injective_of_surjective hsurj
  change (vU.comap (functionFieldMap φ)).comap (functionFieldMap (Up.ι ≫ fp)) =
    vU'.comap (functionFieldMap (Up.ι ≫ fp))
  rw [← comap_functionFieldMap_comp φ (Up.ι ≫ fp), comap_functionFieldMap_comp Up.ι fp, hvU', hv',
    MMP.Positivity.DivisorOver.functionFieldMap_congr hφι, comap_functionFieldMap_comp Um.ι fm, hvU]

end Comparison

/-! ### Flips of a terminal chain -/

section Chain

/-- A normal complex variety is separated. -/
private theorem isSeparated_toTerminal_of_isNormalVariety {X : Scheme.{0}}
    {s : X ⟶ Spec (.of ℂ)} (h : IsNormalVariety ℂ s) :
    IsSeparated (X ↘ Limits.terminal Scheme) := by
  have := h.1
  rw [show (X ↘ Limits.terminal Scheme) = s ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- Precomposing with an isomorphism does not shrink the biregular locus. -/
private theorem biregularLocus_le_biregularLocus_comp {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus f ≤ biregularLocus (φ ≫ f) :=
  sSup_le fun V hV => le_biregularLocus (by
    have : IsIso (f ∣_ V) := hV
    change IsIso ((φ ≫ f) ∣_ V)
    rw [morphismRestrict_comp]
    have h2 : IsIso (φ ∣_ (f ⁻¹ᵁ V)) := by infer_instance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 this)

/-- Precomposing with an isomorphism does not change the biregular locus. -/
private theorem biregularLocus_comp_of_isIso {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus (φ ≫ f) = biregularLocus f := by
  refine le_antisymm ?_ (biregularLocus_le_biregularLocus_comp φ f)
  have := biregularLocus_le_biregularLocus_comp (inv φ) (φ ≫ f)
  rwa [IsIso.inv_hom_id_assoc] at this

/-- **The comparison across one flip of a bridge.** For the `k`-th flip
`(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})` of the `i`-th bridge of a terminal chain, a normal
divisorial valuation `v` of `k(V_k)` whose centre is not contained in the bad locus has the same
log discrepancy as the corresponding valuation of `k(V_{k+1})`. -/
private theorem eq_of_isValuationLogDiscrepancy_flip {T : StabilizedTail}
    (C : StabilizedTail.TerminalChain T) (i : ℕ) (k : Fin (C.bridge i).P.m)
    {v : Valuation (C.model ⟨i, some k⟩).functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation ((C.bridge i).P.Y k).functionField (WithZero (Multiplicative ℤ))}
    (hv' : haveI := C.isIntegral_flipBase i k
      haveI := C.isDominant_flipSourceMap i k
      haveI := ((C.bridge i).P.isThreefoldStepDiagram k k.2).isSmallMorphism_plus
        |>.isBirationalMorphism.isDominant
      v'.comap (functionFieldMap ((C.bridge i).P.gp k)) =
        v.comap (functionFieldMap ((C.bridge i).P.g k)))
    {Zc : IrreducibleCloseds (C.model ⟨i, some k⟩)}
    (hZc : MMP.Intersection.IsCentre ℂ (C.modelStructure ⟨i, some k⟩) v Zc)
    (hZU : ¬ (Zc : Set (C.model ⟨i, some k⟩)) ⊆
      ((badLocusMinus ((C.bridge i).P.g k) ((C.bridge i).P.gp k) :
        Set (modelSeq (C.junction i).Y (C.bridge i).P.Y k)) : Set (C.model ⟨i, some k⟩)))
    {a a' : ℝ}
    (ha : IsValuationLogDiscrepancy (C.modelStructure ⟨i, some k⟩)
      (C.modelBoundary ⟨i, some k⟩) v a)
    (ha' : IsValuationLogDiscrepancy ((C.bridge i).P.sY k) ((C.bridge i).P.ΘY k) v' a') :
    a = a' := by
  have hD := (C.bridge i).P.isThreefoldStepDiagram k k.2
  haveI := C.isIntegral_flipBase i k
  haveI : IsProper ((C.bridge i).P.g k) :=
    isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper ((C.bridge i).P.gp k) :=
    isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_plus
  haveI : CompactSpace (C.model ⟨i, some k⟩) :=
    inferInstanceAs (CompactSpace (modelSeq (C.junction i).Y (C.bridge i).P.Y k))
  haveI := isSeparated_toTerminal_of_isNormalVariety hD.isNormalVariety_target
  obtain ⟨nm, hKm⟩ := hD.isCanonicalDivisor
  obtain ⟨np, hKp⟩ := hD.isCanonicalDivisor_plus
  have hBm : IsPair (C.modelStructure ⟨i, some k⟩) (C.modelBoundary ⟨i, some k⟩) :=
    ⟨inferInstance, inferInstance, ⟨hD.isNormalVariety_minus, nm, _, hKm, hD.isQCartier_minus⟩,
      hD.nonneg⟩
  have hΘ := (C.bridge i).P.ΘY_eq k k.2
  have hBp : IsPair ((C.bridge i).P.sY k) ((C.bridge i).P.ΘY k) := by
    refine ⟨inferInstance, inferInstance, ⟨hD.isNormalVariety_plus, np, _, hKp, ?_⟩, ?_⟩
    · rw [hΘ]
      exact hD.isQCartier_plus
    · intro P
      rw [hΘ]
      exact DivisorWithCoeffs.mapPrimeDivisors_nonneg _
        (DivisorWithCoeffs.mapPrimeDivisors_nonneg _ hD.nonneg) P
  refine eq_of_isValuationLogDiscrepancy hD.isNormalVariety_target hD.isBirationalMorphism_minus
    hD.isSmallMorphism_plus.isBirationalMorphism hD.comp_eq_minus hD.comp_eq_plus hBm hBp
    (fun Pm Pp h hU => ?_) hv' hZc hZU ha ha'
  rw [hΘ]
  exact flipTransform_apply_of_mem_commonBiregularLocus h hU _

/-- Along an equality `a = b` of indices, the identification `V_a = V_b` of models of a programme
is compatible with the morphisms `π_a`, `π_b` to the base. -/
private theorem eqToHom_comp_modelMap {V Z : Scheme.{0}} {Y : ℕ → Scheme.{0}} (π : V ⟶ Z)
    (πY : ∀ k, Y k ⟶ Z) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (modelSeq V Y) h) ≫ modelMap π πY b = modelMap π πY a := by
  subst h
  simp

/-- At the end `V_M ≅ W` of a programme, identified with `V_{k+1}`, the boundary `Θ_{k+1}`
corresponds to the boundary `B` of `W` when `Θ_M = e⁻¹_* B`. -/
private theorem coeff_eq_of_boundary_eq {V W : Scheme.{0}} {Y : ℕ → Scheme.{0}}
    {Θ : QDivisor V} {ΘY : ∀ k, QDivisor (Y k)} (B : QDivisor W) {M k : ℕ} (hM : M = k + 1)
    (e : modelSeq V Y M ≅ W) (hb : divisorSeq Θ ΘY M = inverseTransformDivisor e.hom B)
    (P : MMP.Mori.PrimeDivisor W) (Γ : MMP.Mori.PrimeDivisor (Y k))
    (h : (e.inv ≫ eqToHom (congrArg (modelSeq V Y) hM)) P.genericPoint = Γ.genericPoint) :
    B.coeff P = (ΘY k).coeff Γ := by
  subst hM
  simp only [eqToHom_refl, Category.comp_id] at h
  have hΓ : e.hom Γ.genericPoint = P.genericPoint := by
    rw [← h, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  change _ = divisorSeq Θ ΘY (k + 1) Γ
  rw [hb, inverseTransformDivisor_apply_of_map_genericPoint hΓ
    (le_biregularLocus (V := ⊤) (inferInstance : IsIso (e.hom ∣_ ⊤)) trivial)]
  rfl

/-- **The comparison across a flip of a bridge, on the model reached by the flip.** As
`eq_of_isValuationLogDiscrepancy_flip`, with the target
the model `C.flipTargetOf i k d` of the terminal chain: `V_{k+1}` itself, or the next junction
`Y_{i+1} ≅ V_{m_i}` at the end of the bridge. -/
private theorem eq_of_isValuationLogDiscrepancy_flipTargetOf {T : StabilizedTail}
    (C : StabilizedTail.TerminalChain T) (i : ℕ) (k : Fin (C.bridge i).P.m)
    (d : Decidable (k.1 + 1 < (C.bridge i).P.m))
    {v : Valuation (C.model ⟨i, some k⟩).functionField (WithZero (Multiplicative ℤ))}
    {v' : Valuation (C.model (C.flipTargetOf i k d)).functionField (WithZero (Multiplicative ℤ))}
    (hv' : haveI := C.isIntegral_flipBase i k
      haveI := C.isDominant_flipSourceMap i k
      haveI := C.isDominant_flipTargetMapOf i k d
      v'.comap (functionFieldMap (C.flipTargetMapOf i k d)) =
        v.comap (functionFieldMap ((C.bridge i).P.g k)))
    {Zc : IrreducibleCloseds (C.model ⟨i, some k⟩)}
    (hZc : MMP.Intersection.IsCentre ℂ (C.modelStructure ⟨i, some k⟩) v Zc)
    (hZU : ¬ (Zc : Set (C.model ⟨i, some k⟩)) ⊆
      ((badLocusMinus ((C.bridge i).P.g k) (C.flipTargetMapOf i k d) :
        Set (modelSeq (C.junction i).Y (C.bridge i).P.Y k)) : Set (C.model ⟨i, some k⟩)))
    {a a' : ℝ}
    (ha : IsValuationLogDiscrepancy (C.modelStructure ⟨i, some k⟩)
      (C.modelBoundary ⟨i, some k⟩) v a)
    (ha' : IsValuationLogDiscrepancy (C.modelStructure (C.flipTargetOf i k d))
      (C.modelBoundary (C.flipTargetOf i k d)) v' a') :
    a = a' := by
  cases d with
  | isTrue h => exact eq_of_isValuationLogDiscrepancy_flip C i k hv' hZc hZU ha ha'
  | isFalse h =>
    have hD := (C.bridge i).P.isThreefoldStepDiagram k k.2
    haveI := C.isIntegral_flipBase i k
    haveI := C.isDominant_flipSourceMap i k
    haveI := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
    have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
    let ψ : (C.junction (i + 1)).Y ≅ (C.bridge i).P.Y k := (C.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)
    haveI : IsIso ψ.hom := ψ.isIso_hom
    revert v' hZU
    change ∀ v' : Valuation (C.junction (i + 1)).Y.functionField (WithZero (Multiplicative ℤ)),
      v'.comap (functionFieldMap (ψ.hom ≫ (C.bridge i).P.gp k)) =
        v.comap (functionFieldMap ((C.bridge i).P.g k)) →
      ¬ (Zc : Set (C.model ⟨i, some k⟩)) ⊆
        ((badLocusMinus ((C.bridge i).P.g k) (ψ.hom ≫ (C.bridge i).P.gp k) :
          Set (modelSeq (C.junction i).Y (C.bridge i).P.Y k)) : Set (C.model ⟨i, some k⟩)) →
      IsValuationLogDiscrepancy ((C.junction (i + 1)).p ≫ T.sX (i + 1))
        (C.junction (i + 1)).Θ v' a' → a = a'
    intro v' hv' hZU ha'
    -- the bad locus does not see the identification `e`
    have hZU' : ¬ (Zc : Set (C.model ⟨i, some k⟩)) ⊆
        ((badLocusMinus ((C.bridge i).P.g k) ((C.bridge i).P.gp k) :
          Set (modelSeq (C.junction i).Y (C.bridge i).P.Y k)) : Set (C.model ⟨i, some k⟩)) := by
      have e1 : badLocusMinus ((C.bridge i).P.g k) (ψ.hom ≫ (C.bridge i).P.gp k) =
          badLocusMinus ((C.bridge i).P.g k) ((C.bridge i).P.gp k) := by
        simp only [badLocusMinus, commonBiregularLocus, biregularLocus_comp_of_isIso]
      rwa [e1] at hZU
    -- the valuation on `V_{k+1}`
    have hv'' : (v'.comap (functionFieldMap ψ.hom)).comap
        (functionFieldMap ((C.bridge i).P.gp k)) =
        v.comap (functionFieldMap ((C.bridge i).P.g k)) := by
      rwa [← comap_functionFieldMap_comp]
    -- the structure morphisms agree
    have hstr : ψ.hom ≫ (C.bridge i).P.sY k = (C.junction (i + 1)).p ≫ T.sX (i + 1) := by
      rw [← hD.comp_eq_plus, ← (C.bridge i).P.comp_eq_base k k.2, ← Category.assoc _ _ (T.sZ i),
        ← (C.bridge i).P.πY_eq k k.2]
      change ((C.bridge i).e.inv ≫
          eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) hmk)) ≫
        modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY (k.1 + 1) ≫ T.sZ i = _
      rw [Category.assoc, ← Category.assoc (eqToHom _), eqToHom_comp_modelMap _ _ hmk,
        (C.bridge i).modelMap_eq]
      simp [(T.isThreefoldStepDiagram i).comp_eq_plus]
    rw [← hstr] at ha'
    obtain ⟨n, D, hDp, hDv, hl⟩ := ha'
    obtain ⟨np, hKp⟩ := hD.isCanonicalDivisor_plus
    have hn : np = n := by
      have h1 := hKp.topologicalKrullDim_eq
      have h2 := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hl
      rw [hD.dim_plus] at h1
      rw [(C.junction (i + 1)).dim_eq] at h2
      exact_mod_cast h1.symm.trans h2
    subst hn
    have hiso := isLogDiscrepancy_compIso ψ.hom hKp (B := (C.bridge i).P.ΘY k)
      (fun P Γ h => coeff_eq_of_boundary_eq _ hmk (C.bridge i).e (C.bridge i).boundary_eq P Γ h)
      hDp hl
    refine eq_of_isValuationLogDiscrepancy_flip C i k hv'' hZc hZU' ha
      ⟨np, _, (inferInstance : IsProper (D.f ≫ ψ.hom)), ?_, hiso⟩
    rw [valuation_compProper, hDv]

end Chain

namespace StabilizedTail.PreparedChain

/-- For a small terminal flip move `μ` of a prepared chain, a normalized divisorial valuation `v`
of `ℂ(Y⁻)` outside the weighted bad set `Q.flipBadSet μ` has the same weight on `Y⁻` as the
corresponding valuation `v'` of `ℂ(Y⁺)` (the one with the same restriction to `ℂ(Z)`) has on
`Y⁺`. -/
@[mmp "lem_mmp_indexd_flip_weights_outside"]
public theorem eq_of_isValuationWeight_of_notMem_flipBadSet {T : StabilizedTail}
    (Q : PreparedChain T) (μ : Q.FlipMove)
    {v : Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ))}
    (hv : v ∉ Q.flipBadSet μ)
    {v' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ))}
    (hv' : v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap))
    {w w' : ℕ} (hw : Q.chain.IsValuationWeight Q.scale μ.source.1 v w)
    (hw' : Q.chain.IsValuationWeight Q.scale μ.target.1 v' w') : w = w' := by
  by_cases hc : ∃ Z : IrreducibleCloseds (Q.chain.model μ.source.1),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure μ.source.1) v Z ∧
        (Z : Set (Q.chain.model μ.source.1)) ⊆ μ.badLocusSource
  · -- the centre lies in `W⁻`: both weights vanish, as `v` is not in the weighted bad set
    have : ¬ 0 < w + w' := fun h => hv ⟨hc, v', hv', w, w', hw, hw', h⟩
    omega
  -- the centre is not in `W⁻`: the log discrepancies agree
  obtain ⟨Dv, hDvp, hDvv, -⟩ := hw.1
  have hZc : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure μ.source.1) v Dv.center :=
    ⟨Dv, hDvp, hDvv, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hw.2
  obtain ⟨a', ha', rfl⟩ := hw'.2
  rw [eq_of_isValuationLogDiscrepancy_flipTargetOf Q.chain μ.1.1 μ.1.2 inferInstance hv' hZc
    (fun h => hc ⟨_, hZc, h⟩) ha ha']

end StabilizedTail.PreparedChain

end MMP.Fourfold
