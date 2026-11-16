module
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ClosedPointBound

/-!
# Normalizations of a divisor and of its transform under a flip

Let `φ : X ⟶ Z` be a small contraction of a threefold `X` over a field `k`, and `φ⁺ : X⁺ ⟶ Z` a
flip of `φ` with respect to an `ℝ`-Cartier divisor `E`, with birational map `g : X ⤏ X⁺`. Let
`S ⊆ X` be a prime divisor and `S⁺ = g_* S`. If no flipped curve is contained in `S⁺`, then `S⁺`
is finite over `T = φ(S)`, so `(S⁺)^ν` is the normalization of `T`, and the dominant map
`S^ν ⟶ T` lifts to a morphism `ψ : S^ν ⟶ (S⁺)^ν` of normalizations agreeing with `g` on a dense
open subset of `S^ν`.

## Main results

* `MMP.Flips.exists_normalization_hom_of_forall_isFlippedCurveOf_not_subset`

## Implementation notes

"`ψ` agrees with `g` on a dense open subset" is: for some representative `g₀` of `g`, there is
a dense open `U ⊆ S^ν` mapped by `ν : S^ν ⟶ X` into the domain of `g₀`, on which
`ν⁺ ∘ ψ = g₀ ∘ ν`. The normalizations are `MMP.Fourfold.primeDivisorNormalization`. Flips are
taken with respect to `ℝ`-Cartier divisors (`MMP.Flips.IsFlip`), which contains the case of a
`ℚ`-Cartier divisor.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.13.3
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold

namespace MMP.Flips

/-- The normalization `S^ν ⟶ S` of a prime divisor `S` of a scheme locally of finite type over
a field is finite (a scheme of finite type over a field is Nagata). -/
private theorem isFinite_normalization_subscheme (k : Type u) [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (S : Mori.PrimeDivisor X) :
    haveI := S.integral
    IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
  haveI := S.integral
  Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k (S.idealSheaf.subschemeι ≫ s))
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)

/-- A proper morphism of Jacobson schemes whose fibres over closed points have dimension at most
`0` is finite. -/
private theorem isFinite_of_isProper_of_topologicalKrullDim_fiber_le {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [JacobsonSpace X] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed {y} → topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    IsFinite f := by
  have : LocallyQuasiFinite f := by
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    refine top_le_iff.mp fun x _ => ?_
    rw [Scheme.Hom.mem_quasiFiniteLocus]
    have h0 := fiberDimensionAt_le_of_isClosed_singleton_target f h x
    exact ((quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x).mpr
      (le_antisymm (by simpa using h0) (topologicalKrullDimAt_nonneg _))).2
  exact .of_isProper_of_locallyQuasiFinite f

/-- The irreducible closed subset `closure {x}` of a point. -/
private def ptClosure {X : Type*} [TopologicalSpace X] (x : X) : IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- A nontrivial specialization `a ⤳ b` in a `T₀` space gives `closure {b} < closure {a}`. -/
private theorem ptClosure_lt {X : Type*} [TopologicalSpace X] [T0Space X] {a b : X} (h : a ⤳ b)
    (hne : a ≠ b) : ptClosure b < ptClosure a := by
  refine lt_of_le_of_ne h.closure_subset fun heq => hne ?_
  exact (inseparable_iff_closure_eq.mpr
    (congrArg (fun T : IrreducibleCloseds X => (T : Set X)) heq)).eq.symm

/-- A `T₀` space with a nontrivial specialization `a ⤳ b` has dimension at least `1`. -/
private theorem one_le_topologicalKrullDim_of_specializes {X : Type*} [TopologicalSpace X]
    [T0Space X] {a b : X} (h : a ⤳ b) (hne : a ≠ b) : 1 ≤ topologicalKrullDim X :=
  Order.one_le_krullDim_iff.mpr ⟨_, _, ptClosure_lt h hne⟩

/-- Let `F` be a closed subset of a quasi-sober `T₀` space containing no chain `c ⤳ a ⤳ b` of
two nontrivial specializations, and `P` a closed subset containing no maximal irreducible subset
of `F` of positive dimension. Then there is no nontrivial specialization `a ⤳ b` inside `F` with
`a ∈ P`. -/
private theorem eq_of_specializes_of_forall_maximal_not_subset {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] {F P : Set X} (hF : IsClosed F)
    (hF2 : ∀ ⦃a b c : X⦄, a ∈ F → b ∈ F → c ∈ F → a ⤳ b → c ⤳ a → a = b ∨ c = a)
    (hS : ∀ C : Set X, Maximal (fun S : Set X => IsIrreducible S ∧ S ⊆ F) C →
      0 < topologicalKrullDim C → ¬ C ⊆ P) (hP : IsClosed P)
    {a b : X} (ha : a ∈ F) (hb : b ∈ F) (haP : a ∈ P) (h : a ⤳ b) : a = b := by
  by_contra hne
  have hmax : Maximal (fun S : Set X => IsIrreducible S ∧ S ⊆ F) (closure {a}) := by
    refine ⟨⟨isIrreducible_singleton.closure, hF.closure_subset_iff.mpr (by simpa using ha)⟩,
      fun T hT hle => ?_⟩
    have hTc := hT.1.closure
    set c := hTc.genericPoint
    have hgen := hTc.isGenericPoint_genericPoint isClosed_closure
    have hca : c ⤳ a := hgen.specializes (subset_closure (hle (subset_closure rfl)))
    have hcF : c ∈ F := hF.closure_subset_iff.mpr hT.2 hgen.mem
    by_cases hc : c = a
    · rw [← hc, hgen.def]
      exact subset_closure
    · exact ((hF2 ha hb hcF h hca).elim hne hc).elim
  refine hS _ hmax ?_ (hP.closure_subset_iff.mpr (by simpa using haP))
  exact lt_of_lt_of_le (by decide) (one_le_topologicalKrullDim_of_specializes
    ((subtype_specializes_iff (⟨a, subset_closure rfl⟩ : closure ({a} : Set X))
      ⟨b, specializes_iff_mem_closure.mp h⟩).mpr h) (fun e => hne (congrArg Subtype.val e)))

/-- An order of Krull dimension at most `3` has no element of coheight at least `2` lying above
a chain `W₀ < W₁`. -/
private theorem not_lt_lt_of_two_le_coheight {T : Type*} [Preorder T]
    (hdim : Order.krullDim T ≤ 3) {W W₀ W₁ : T}
    (hW : 2 ≤ Order.coheight W) (h₀ : W₀ < W₁) (h₁ : W₁ < W) : False := by
  have hh : 2 ≤ Order.height W := by
    let p : LTSeries T := ⟨2, ![W₀, W₁, W], fun i => by
      fin_cases i
      · exact h₀
      · exact h₁⟩
    exact_mod_cast Order.length_le_height (p := p) (x := W) le_rfl
  have : Nonempty T := ⟨W⟩
  have h4 : ((4 : ℕ∞) : WithBot ℕ∞) ≤ Order.krullDim T := by
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_trans (by
      calc (4 : ℕ∞) = 2 + 2 := by norm_num
        _ ≤ _ := add_le_add hh hW) (le_ciSup (OrderTop.bddAbove _) W))
  exact absurd (h4.trans hdim) (by decide)

/-- The fibres of the flip `φ' : X⁺ ⟶ Z` of a threefold over closed points contain no chain
`c ⤳ a ⤳ b` of two nontrivial specializations. -/
private theorem eq_or_eq_of_specializes_of_mem_fiber
    (k : Type u) [Field k] {X X' Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    (E : Mori.RDivisor X) (φ : X ⟶ Z) (φ' : X' ⟶ Z) (g : X.RationalMap X')
    (hflip : IsFlip k sX sZ sX' E φ φ' g) (hdim : topologicalKrullDim X = 3)
    (z : Z) (hz : IsClosed {z}) ⦃a b c : X'⦄ (hc : φ' c = z)
    (hab : a ⤳ b) (hca : c ⤳ a) : a = b ∨ c = a := by
  obtain ⟨V, W, hV, -, hVW, hiso⟩ := hflip.isSmall.exists_isIso
  have hdimX' : topologicalKrullDim X' = 3 :=
    hflip.isSmall.dim_eq.trans (hflip.isSmall_source.dim_eq.symm.trans hdim)
  by_cases hcV : c ∈ (V : Set X')
  · by_contra! hne
    have haV : a ∈ (V : Set X') := hca.mem_closed V.isClosed hcV
    have hW := Mori.le_closedsCodimension_iff.mp hV (ptClosure c)
      (V.isClosed.closure_subset_iff.mpr (by simpa using hcV))
    exact not_lt_lt_of_two_le_coheight hdimX'.le hW (ptClosure_lt hab hne.1)
      (ptClosure_lt hca hne.2)
  · right
    have : LocallyOfFiniteType sX' := hflip.isNormalVariety_flip.1.toLocallyOfFiniteType
    have : JacobsonSpace X' := LocallyOfFiniteType.jacobsonSpace sX'
    have hinj : ∀ x : X', x ∉ (V : Set X') → φ' x = z → x = c := by
      intro x hxV hx
      let f := φ'.resLE W.compl V.compl hVW
      have key : ∀ y : Scheme.Opens.toScheme (X := X') V.compl,
          Scheme.Opens.ι (X := Z) W.compl (f y) = φ' y.val := fun y => by
        rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]
        rfl
      have h1 : f ⟨x, hxV⟩ = f ⟨c, hcV⟩ :=
        (Scheme.Opens.ι (X := Z) W.compl).isOpenEmbedding.injective
          ((key ⟨x, hxV⟩).trans (hx.trans (hc.symm.trans (key ⟨c, hcV⟩).symm)))
      exact congrArg Subtype.val (f.isOpenEmbedding.injective h1)
    have hcl : IsClosed ({c} : Set X') := by
      refine isClosed_singleton_of_isLocallyClosed_singleton ⟨(V : Set X')ᶜ, φ' ⁻¹' {z},
        V.isClosed.isOpen_compl, hz.preimage φ'.continuous, ?_⟩
      ext x
      refine ⟨?_, fun ⟨hxV, hx⟩ => hinj x hxV hx⟩
      rintro rfl
      exact ⟨hcV, hc⟩
    exact (Set.mem_singleton_iff.mp (hca.mem_closed hcl (Set.mem_singleton c))).symm

/-- If no flipped curve lies in `S⁺`, every fibre of `S⁺ ⟶ X⁺ ⟶ Z` over a closed point has
dimension at most `0`. -/
private theorem topologicalKrullDim_fiber_subschemeι_comp_le
    (k : Type u) [Field k] {X X' Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    (E : Mori.RDivisor X) (φ : X ⟶ Z) (φ' : X' ⟶ Z) (g : X.RationalMap X')
    (hflip : IsFlip k sX sZ sX' E φ φ' g) (hdim : topologicalKrullDim X = 3)
    (Sp : Mori.PrimeDivisor X')
    (hS : ∀ C : Set X', IsFlippedCurveOf k sX sZ sX' E φ φ' g C → ¬ C ⊆ Sp.support) :
    ∀ z : Z, IsClosed {z} →
      topologicalKrullDim ((Sp.idealSheaf.subschemeι ≫ φ').fiber z) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  intro z hz
  set ι := Sp.idealSheaf.subschemeι
  have hfib : ∀ p : (ι ≫ φ').fiber z, φ' (ι ((ι ≫ φ').fiberι z p)) = z := fun p =>
    ((ι ≫ φ').fiberHomeo z p).2
  have hP : ∀ x, ι x ∈ Sp.support := fun x =>
    (Sp.idealSheaf.range_subschemeι ▸ Set.mem_range_self (f := ι) x :
      ι x ∈ (Sp.idealSheaf.support : Set X'))
  have key : ∀ ⦃p q : (ι ≫ φ').fiber z⦄, p ⤳ q → p = q := by
    intro p q hpq
    have h2 := (hpq.map ((ι ≫ φ').fiberι z).continuous).map ι.continuous
    have := eq_of_specializes_of_forall_maximal_not_subset (F := φ' ⁻¹' {z}) (P := Sp.support)
      (hz.preimage φ'.continuous)
      (fun _ _ _ _ _ hc hab hca =>
        eq_or_eq_of_specializes_of_mem_fiber k sX sX' sZ E φ φ' g hflip hdim z hz hc hab hca)
      (fun C hC hCd hCP => hS C ⟨hflip, hflip.isNormalVariety_flip.1,
        hflip.isNormalVariety_target.1, hflip.isSmall.comp_eq, hflip.isProper, z, hz, hC, hCd⟩
        hCP)
      Sp.idealSheaf.support.isClosed (hfib p) (hfib q) (hP _) h2
    exact ((ι ≫ φ').fiberι z).isEmbedding.injective (ι.isEmbedding.injective this)
  have := topologicalKrullDim_le_of_specializes_imp_eq (f := fun _ => PUnit.unit.{1})
    (Y := PUnit.{1}) continuous_const (fun a b hab _ => key hab)
  exact this.trans (by simpa using topologicalKrullDim_zero_of_discreteTopology PUnit.{1})

/-- If no flipped curve lies in `S⁺`, then `(S⁺)^ν ⟶ X⁺ ⟶ Z` is finite. -/
private theorem isFinite_primeDivisorNormalization_comp
    (k : Type u) [Field k] {X X' Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    (E : Mori.RDivisor X) (φ : X ⟶ Z) (φ' : X' ⟶ Z) (g : X.RationalMap X')
    (hflip : IsFlip k sX sZ sX' E φ φ' g) (hdim : topologicalKrullDim X = 3)
    (Sp : Mori.PrimeDivisor X')
    (hS : ∀ C : Set X', IsFlippedCurveOf k sX sZ sX' E φ φ' g C → ¬ C ⊆ Sp.support) :
    IsFinite (primeDivisorNormalization Sp ≫ φ') := by
  have : IsProper φ' := hflip.isProper
  have : LocallyOfFiniteType sZ := hflip.isNormalVariety_target.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hflip.isNormalVariety_flip.1.toLocallyOfFiniteType
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  have : JacobsonSpace Sp.idealSheaf.subscheme :=
    LocallyOfFiniteType.jacobsonSpace (Sp.idealSheaf.subschemeι ≫ sX')
  have := isFinite_normalization_subscheme k sX' Sp
  have := isFinite_of_isProper_of_topologicalKrullDim_fiber_le (Sp.idealSheaf.subschemeι ≫ φ')
    (topologicalKrullDim_fiber_subschemeι_comp_le k sX sX' sZ E φ φ' g hflip hdim Sp hS)
  rw [primeDivisorNormalization, Category.assoc]
  infer_instance

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_terminal_of_isSeparated {k : Type u} [Field k] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (.of k)) [IsSeparated s] : IsSeparated (Y ↘ ⊤_ Scheme) := by
  rw [show (Y ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- The normalization `S^ν ⟶ S ⊆ Y` of a prime divisor maps the generic point of `S^ν` to the
generic point of `S`. -/
private theorem primeDivisorNormalization_genericPoint {Y : Scheme.{u}} (P : Mori.PrimeDivisor Y)
    [IsIntegral (primeDivisorNormalizationScheme P)] :
    primeDivisorNormalization P (genericPoint (primeDivisorNormalizationScheme P)) =
      P.genericPoint := by
  have := P.integral
  have h := IsBirational.genericPoint_eq (Scheme.normalization P.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U))
    (Scheme.isBirational_normalization _ _)
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg P.idealSheaf.subschemeι h)

/-- Universal property of the normalization of a prime divisor `P` (Stacks, Tag 035Q): a morphism
from a normal scheme into `P` sending generic points to the generic point lifts through
`P^ν ⟶ P`. -/
private theorem exists_lift_primeDivisorNormalization {Y W : Scheme.{u}} (P : Mori.PrimeDivisor Y)
    (f : W ⟶ P.idealSheaf.subscheme) [IsNormal W]
    (hgen : ∀ η : genericPoints W, f η.1 ∈ genericPoints P.idealSheaf.subscheme) :
    ∃ ψ : W ⟶ primeDivisorNormalizationScheme P,
      ψ ≫ primeDivisorNormalization P = f ≫ P.idealSheaf.subschemeι := by
  have := P.integral
  obtain ⟨ψ, hψ, -⟩ := Scheme.existsUnique_lift_normalization
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) f hgen
  exact ⟨ψ, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ P.idealSheaf.subschemeι) hψ)⟩

/-- A finite morphism `π : P ⟶ N` onto a normal integral scheme with a section over an open
`U` containing the generic point has a section over all of `N` extending it. -/
private theorem exists_section_of_isFinite {N P : Scheme.{u}} [IsIntegral N] [IsNormal N]
    (π : P ⟶ N) [IsFinite π] (U : N.Opens) (hU : genericPoint N ∈ U) (t : U.toScheme ⟶ P)
    (ht : t ≫ π = U.ι) : ∃ s : N ⟶ P, s ≫ π = 𝟙 N ∧ U.ι ≫ s = t := by
  have hNfin : ∀ V : N.Opens, IsCompact (V : Set N) → (irreducibleComponents V).Finite :=
    fun V _ => finite_irreducibleComponents_opens_of_irreducibleSpace V
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U.isOpen.dense ⟨_, hU⟩⟩
  have hgenU : U.ι (genericPoint U.toScheme) = genericPoint N := genericPoint_eq_of_isDominant U.ι
  have := Scheme.quasiCompactFromGenericPointResidueFields N hNfin
  have := Scheme.quasiSeparatedFromGenericPointResidueFields N
  let f := Scheme.fromGenericPointResidueFields N
  have hrangef : Set.range f ⊆ Set.range U.ι := by
    rw [Scheme.range_fromGenericPointResidueFields, Scheme.Opens.range_ι,
      genericPoints_eq_singleton, Set.singleton_subset_iff]
    exact hU
  let ιg := IsOpenImmersion.lift U.ι f hrangef
  have hιg : ιg ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant ιg := by
    obtain ⟨p, hp⟩ : genericPoint N ∈ Set.range f := by
      rw [Scheme.range_fromGenericPointResidueFields, genericPoints_eq_singleton]
      rfl
    have hp' : ιg p = genericPoint U.toScheme := by
      apply U.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hιg, hp, hgenU]
    refine ⟨dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)⟩
    rw [← (genericPoint_spec U.toScheme).def, ← hp']
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨p, rfl⟩)
  have H : f = (ιg ≫ t) ≫ π := by rw [Category.assoc, ht, hιg]
  have := Scheme.isIso_normalization_of_isNormal N hNfin
  let s : N ⟶ P := inv (Scheme.normalization N hNfin) ≫ Scheme.Hom.normalizationDesc f _ π H
  have hs : s ≫ π = 𝟙 N := by
    simp only [s, Category.assoc, Scheme.Hom.normalizationDesc_comp]
    exact IsIso.inv_hom_id _
  refine ⟨s, hs, ext_of_isDominant_of_isSeparated π ?_ ιg ?_⟩
  · rw [Category.assoc, hs, ht, Category.comp_id]
  · have hf_inv : f ≫ inv (Scheme.normalization N hNfin) = Scheme.Hom.toNormalization f := by
      rw [IsIso.comp_inv_eq]
      exact (Scheme.Hom.toNormalization_fromNormalization f).symm
    rw [← Category.assoc, hιg]
    simp only [s, ← Category.assoc, hf_inv]
    rw [Scheme.Hom.toNormalization_normalizationDesc]

/-- A representative `g₀` of the birational map `g` of a flip lies over `Z`. -/
private theorem hom_comp_eq_ι_comp_of_isFlip
    (k : Type u) [Field k] {X X' Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    (E : Mori.RDivisor X) (φ : X ⟶ Z) (φ' : X' ⟶ Z) (g : X.RationalMap X')
    (hflip : IsFlip k sX sZ sX' E φ φ' g) {g₀ : X.PartialMap X'} (hg₀ : g₀.toRationalMap = g) :
    g₀.hom ≫ φ' = g₀.domain.ι ≫ φ := by
  have : IsSeparated sX' := hflip.isNormalVariety_flip.1.toIsSeparated
  have : IsSeparated sZ := hflip.isNormalVariety_target.1.toIsSeparated
  have := isSeparated_terminal_of_isSeparated sX'
  have := isSeparated_terminal_of_isSeparated sZ
  have h : (g₀.compHom φ').toRationalMap = φ.toPartialMap.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg₀]
    exact hflip.isModificationOf.2
  rwa [Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)] at h

/-- If `g_* S = S⁺` and a morphism `u : W ⟶ X⁺` from a reduced scheme has range in `g_* S`, then
the ideal sheaf of `S⁺` is contained in the kernel of `u`. -/
private theorem ker_subschemeι_le_ker_of_range_subset {X X' W : Scheme.{u}} [IsReduced W]
    {g : X.RationalMap X'} {S : Mori.PrimeDivisor X} {Sp : Mori.PrimeDivisor X'}
    (hSp : Mori.RationalMap.transformPrimeDivisor g S = some Sp) (u : W ⟶ X')
    (hrange : Set.range u ⊆ (Mori.RationalMap.transform g S.idealSheaf.support : Set X')) :
    Sp.idealSheaf.subschemeι.ker ≤ u.ker := by
  have hu : u.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range u)) := by
    rw [← Scheme.IdealSheafData.map_bot u, ← Scheme.nilradical_eq_bot (X := W),
      ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
    congr 2
    rw [TopologicalSpace.Closeds.coe_top, Set.image_univ]
  rw [Scheme.IdealSheafData.ker_subschemeι, hu,
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hSp).2,
    Mori.RationalMap.transformIdeal]
  exact Scheme.IdealSheafData.vanishingIdeal_antimono
    (TopologicalSpace.Closeds.closure_le.mpr hrange)

/-- A morphism `f : W ⟶ P` from an integral scheme into a prime divisor `P`, sending the generic
point of `W` to the generic point of `P`, sends generic points to generic points. -/
private theorem mem_genericPoints_of_subschemeι_genericPoint {Y W : Scheme.{u}} [IsIntegral W]
    (P : Mori.PrimeDivisor Y) (f : W ⟶ P.idealSheaf.subscheme)
    (h : P.idealSheaf.subschemeι (f (genericPoint W)) = P.genericPoint) :
    ∀ η : genericPoints W, f η.1 ∈ genericPoints P.idealSheaf.subscheme := by
  have := P.integral
  rintro ⟨η, hη⟩
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hη
  subst hη
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff]
  exact P.idealSheaf.subschemeι.isEmbedding.injective h

/-- Let `g₀` be a representative of `g` defined at the generic point of `S`, with `g_* S = S⁺`. On
an integral normal open `U ⊆ S^ν` mapped into the domain of `g₀` and containing the generic point,
the morphism `g₀ ∘ ν : U ⟶ X⁺` lifts through `ν⁺ : (S⁺)^ν ⟶ X⁺`. -/
private theorem exists_lift_resLE_comp {X X' : Scheme.{u}} [IsReduced X]
    [IsSeparated (X' ↘ ⊤_ Scheme)]
    {g : X.RationalMap X'} {S : Mori.PrimeDivisor X} {Sp : Mori.PrimeDivisor X'}
    (hSp : Mori.RationalMap.transformPrimeDivisor g S = some Sp) {g₀ : X.PartialMap X'}
    (hg₀ : g₀.toRationalMap = g) (hη : S.genericPoint ∈ g₀.domain)
    (U : (primeDivisorNormalizationScheme S).Opens) [IsIntegral U.toScheme] [IsNormal U.toScheme]
    (hU : U ≤ primeDivisorNormalization S ⁻¹ᵁ g₀.domain)
    (hgen : primeDivisorNormalization S (U.ι (genericPoint U.toScheme)) = S.genericPoint) :
    ∃ ψU : U.toScheme ⟶ primeDivisorNormalizationScheme Sp,
      ψU ≫ primeDivisorNormalization Sp =
        (primeDivisorNormalization S).resLE g₀.domain U hU ≫ g₀.hom := by
  have : IsReduced U.toScheme := isReduced_of_isIntegral _
  have hres : ∀ x : U.toScheme, g₀.domain.ι ((primeDivisorNormalization S).resLE g₀.domain U hU x) =
      primeDivisorNormalization S (U.ι x) := fun x => by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
  let u : U.toScheme ⟶ X' := (primeDivisorNormalization S).resLE g₀.domain U hU ≫ g₀.hom
  have hrange : Set.range u ⊆ (Mori.RationalMap.transform g S.idealSheaf.support : Set X') := by
    rintro _ ⟨x, rfl⟩
    refine Mori.RationalMap.image_subset_transform g₀ hg₀ S.idealSheaf.support
      ⟨(primeDivisorNormalization S).resLE g₀.domain U hU x, ?_, rfl⟩
    have h1 := range_primeDivisorNormalization_subset S ⟨U.ι x, rfl⟩
    rwa [← hres] at h1
  let u' : U.toScheme ⟶ Sp.idealSheaf.subscheme := IsClosedImmersion.lift
    Sp.idealSheaf.subschemeι u (ker_subschemeι_le_ker_of_range_subset hSp u hrange)
  have hu' : u' ≫ Sp.idealSheaf.subschemeι = u := IsClosedImmersion.lift_fac _ _ _
  have hpt : (primeDivisorNormalization S).resLE g₀.domain U hU (genericPoint U.toScheme) =
      ⟨S.genericPoint, hη⟩ := Subtype.ext ((hres _).trans hgen)
  obtain ⟨ψU, hψU⟩ := exists_lift_primeDivisorNormalization Sp u'
    (mem_genericPoints_of_subschemeι_genericPoint Sp u' (by
      rw [← Scheme.Hom.comp_apply, hu']
      change g₀.hom ((primeDivisorNormalization S).resLE g₀.domain U hU _) = _
      rw [hpt, ← genericPoint_eq_of_transformPrimeDivisor_eq_some hSp g₀ hg₀ hη]))
  exact ⟨ψU, hψU.trans hu'⟩

/-- Let `p : P ⟶ Y` be finite and `N` normal integral. A morphism `U ⟶ P` over `Y` from an open
`U ⊆ N` containing the generic point extends to a morphism `N ⟶ P`. -/
private theorem exists_extend_of_isFinite {N P Y : Scheme.{u}} [IsIntegral N] [IsNormal N]
    (p : P ⟶ Y) [IsFinite p] (q : N ⟶ Y) (U : N.Opens) (hU : genericPoint N ∈ U)
    (ψU : U.toScheme ⟶ P) (h : ψU ≫ p = U.ι ≫ q) : ∃ ψ : N ⟶ P, U.ι ≫ ψ = ψU := by
  obtain ⟨s, -, hs⟩ := exists_section_of_isFinite (Limits.pullback.snd p q) U hU
    (Limits.pullback.lift ψU U.ι h) (Limits.pullback.lift_snd _ _ _)
  exact ⟨s ≫ Limits.pullback.fst _ _, by rw [reassoc_of% hs, Limits.pullback.lift_fst]⟩

/-- Let `φ : X ⟶ Z` be a small contraction of a threefold `X` over `k`, `φ⁺ : X⁺ ⟶ Z` a flip of
`φ` with respect to `E`, with birational map `g : X ⤏ X⁺`, `S` a prime divisor of `X` and
`S⁺ = g_* S`. If no flipped curve lies in `S⁺`, there is a morphism `ψ : S^ν ⟶ (S⁺)^ν` of
normalizations which agrees with `g` on a dense open subset of `S^ν`. -/
@[mmp "lem_fa4_normalization_morphism_no_flipped_curve"]
public theorem exists_normalization_hom_of_forall_isFlippedCurveOf_not_subset
    (k : Type u) [Field k] {X X' Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sX' : X' ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    (E : Mori.RDivisor X) (φ : X ⟶ Z) (φ' : X' ⟶ Z) (g : X.RationalMap X')
    (hflip : IsFlip k sX sZ sX' E φ φ' g) (hdim : topologicalKrullDim X = 3)
    (S : Mori.PrimeDivisor X) (Sp : Mori.PrimeDivisor X')
    (hSp : Mori.RationalMap.transformPrimeDivisor g S = some Sp)
    (hS : ∀ C : Set X', IsFlippedCurveOf k sX sZ sX' E φ φ' g C → ¬ C ⊆ Sp.support) :
    ∃ ψ : primeDivisorNormalizationScheme S ⟶ primeDivisorNormalizationScheme Sp,
      ∃ g₀ : X.PartialMap X', g₀.toRationalMap = g ∧
        ∃ U : (primeDivisorNormalizationScheme S).Opens,
          Dense (U : Set (primeDivisorNormalizationScheme S)) ∧
          ∃ h : U ≤ primeDivisorNormalization S ⁻¹ᵁ g₀.domain,
            U.ι ≫ ψ ≫ primeDivisorNormalization Sp =
              (primeDivisorNormalization S).resLE g₀.domain U h ≫ g₀.hom := by
  have := isFinite_primeDivisorNormalization_comp k sX sX' sZ E φ φ' g hflip hdim Sp hS
  have := S.integral
  obtain ⟨hdef, -⟩ := Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hSp
  obtain ⟨g₀, hη, hg₀⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  have hover := hom_comp_eq_ι_comp_of_isFlip k sX sX' sZ E φ φ' g hflip hg₀
  have : IsSeparated sX' := hflip.isNormalVariety_flip.1.toIsSeparated
  have := isSeparated_terminal_of_isSeparated sX'
  have : IsIntegral (primeDivisorNormalizationScheme S) :=
    Scheme.isIntegral_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have : IsNormal (primeDivisorNormalizationScheme S) :=
    Scheme.isNormal_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hgenN := primeDivisorNormalization_genericPoint S
  set U : (primeDivisorNormalizationScheme S).Opens :=
    primeDivisorNormalization S ⁻¹ᵁ g₀.domain
  have hηU : genericPoint (primeDivisorNormalizationScheme S) ∈ U := by
    change primeDivisorNormalization S _ ∈ g₀.domain
    rwa [hgenN]
  have hUdense : Dense (U : Set (primeDivisorNormalizationScheme S)) :=
    U.isOpen.dense ⟨_, hηU⟩
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : IsNormal U.toScheme := isNormal_of_isOpenImmersion U.ι
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsDominant U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  obtain ⟨ψU, hψU⟩ := exists_lift_resLE_comp hSp hg₀ hη U le_rfl
    (by rw [genericPoint_eq_of_isDominant U.ι, hgenN])
  have hψZ : ψU ≫ (primeDivisorNormalization Sp ≫ φ') =
      U.ι ≫ (primeDivisorNormalization S ≫ φ) := by
    rw [← Category.assoc ψU, hψU]
    simp only [Category.assoc, hover]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_extend_of_isFinite _ _ U hηU ψU hψZ
  exact ⟨ψ, g₀, hg₀, U, hUdense, le_rfl, by rw [reassoc_of% hψ, hψU]⟩

end MMP.Flips

