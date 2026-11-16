module
import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionBaseChange
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.Morphisms.ProductWithLine
public import MMP.Analysis.Complex.CauchyOsgoodLaurent
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
import MMP.AlgebraicGeometry.Normalization.IntegralScheme

/-!
# Normalization and branch counts of a product boundary

Let `Y` be a normal complex threefold and `Q = Q_1 ∪ ⋯ ∪ Q_m` a reduced union of distinct prime
divisors of `Y`, with normalizations `ν_j : Q_j^ν ⟶ Q_j`. Write `pr : Y × ℙ¹ ⟶ Y` for the first
projection of the fibre product over `Spec ℂ`. Then `Y × ℙ¹` is a normal fourfold, each
`Q_j × ℙ¹ = pr⁻¹(Q_j)` is a prime divisor of it, distinct `Q_j` giving distinct divisors, and
`ν_j × id : Q_j^ν × ℙ¹ ⟶ Q_j × ℙ¹` is the normalization of `Q_j × ℙ¹`. For an irreducible curve
`C ⊆ Q`, `C × ℙ¹ = pr⁻¹(C)` is an irreducible surface, `C ↦ C × ℙ¹` is injective, and the branch
counts agree: `r_{C × ℙ¹} = r_C`. Every irreducible surface of `Q × ℙ¹` and every irreducible
curve of `Q` has branch count at least one. If `Y` is projective, the divisor cycle rank of
`(Q_j × ℙ¹)^ν` is the boxed divisor cycle rank `ρ^□(Q_j^ν)`.

## Main results

* `MMP.Fourfold.exists_embedding_primeDivisor_pullback_projectiveLine`

## Implementation notes

`Y × ℙ¹` is `pullback sY (projectiveLine ℂ ↘ Spec ℂ)`, a scheme over `ℂ` through
`pullback.fst ≫ sY`. The assignment `Q_j ↦ Q_j × ℙ¹` is an embedding `Φ` of prime divisors
characterised by `supp Φ(S) = pr⁻¹(supp S)`; the boundary `Q × ℙ¹` is the finite set `Q.map Φ`.
"`ν_j × id` is the normalization" is an isomorphism of `(Q_j × ℙ¹)^ν` with
`Q_j^ν ×_ℂ ℙ¹` over `Y × ℙ¹`, the map to `Y × ℙ¹` being `pullback.map` of `ν_j` and the
identity of `ℙ¹`. Branch counts are `MMP.Fourfold.boundaryBranchCount`, the count underlying
`MMP.Fourfold.IsThreefoldBoundaryBranchCount` and `MMP.Fourfold.IsFourfoldBoundaryBranchCount`;
curves and surfaces are irreducible closed subsets of dimension one and two.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MMP MMP.Mori Order

namespace MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

private theorem topologicalKrullDim_closure_singleton_eq_height {X : Scheme} (x : X) :
    topologicalKrullDim (closure {x} : Set X) = height x := by
  let T : Set X := closure {x}
  have hTc : IsClosed T := isClosed_closure
  haveI : QuasiSober T := hTc.isClosedEmbedding_subtypeVal.quasiSober
  have hpre : (specializationOrder T).toPreorder = (inferInstance : Preorder T) :=
    Preorder.ext fun a b => (Topology.IsInducing.subtypeVal.specializes_iff (x := b) (y := a)).symm
  have hheight : ∀ a : T, height a = height (a : X) := by
    refine height_eq_of_strictMono _ (Subtype.strictMono_coe _) fun a b hb => ?_
    have hbT : b ∈ T := (Scheme.le_iff_specializes.mp hb.le).mem_closed hTc a.2
    exact ⟨⟨b, hbT⟩, hb, rfl⟩
  have hx : x ∈ T := subset_closure rfl
  change krullDim (IrreducibleCloseds T) = _
  rw [@Order.krullDim_eq_of_orderIso _ _ _ (specializationOrder T).toPreorder
    irreducibleSetEquivPoints, hpre,
    krullDim_eq_iSup_height]
  refine le_antisymm (iSup_le fun a => ?_) (le_iSup_of_le ⟨x, hx⟩ ?_)
  · rw [hheight a]
    exact WithBot.coe_le_coe.mpr (height_mono (Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr a.2)))
  · rw [hheight ⟨x, hx⟩]

private theorem codimension_eq_of_topologicalKrullDim {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] {a b : ℕ}
    (hdim : topologicalKrullDim Y = (a + b : ℕ)) (C : IrreducibleCloseds Y)
    (hC : topologicalKrullDim (C : Set Y) = b) :
    codimension C = a := by
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := sY)
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have h := MMP.height_add_coheight_eq_krullDim k C.isIrreducible.genericPoint
  have hcl : closure {C.isIrreducible.genericPoint} = (C : Set Y) :=
    (C.isIrreducible.isGenericPoint_genericPoint_closure).def.trans C.isClosed.closure_eq
  have hcod : codimension C = coheight C.isIrreducible.genericPoint := by
    rw [codimension_eq_coheight]
    exact (Order.coheight_orderIso (irreducibleSetEquivPoints (α := Y)) C).symm
  rw [← hcod] at h
  have h1 := topologicalKrullDim_closure_singleton_eq_height C.isIrreducible.genericPoint
  rw [hcl, hC] at h1
  have hK : krullDim Y = (a + b : ℕ) := by
    rw [← hdim]
    exact (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm
  rw [hK] at h
  have h' : height C.isIrreducible.genericPoint + codimension C = ((a + b : ℕ) : ℕ∞) :=
    WithBot.coe_injective (h.trans rfl)
  have hh : height C.isIrreducible.genericPoint = b := by exact_mod_cast h1.symm
  rw [hh] at h'
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (show codimension C ≠ ⊤ by
    intro ht
    rw [ht, add_top] at h'
    exact ENat.natCast_ne_top _ h'.symm)
  rw [← hc] at h' ⊢
  have : b + c = a + b := by exact_mod_cast h'
  norm_cast
  omega

private theorem isFinite_primeDivisorNormalization {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y) :
    IsFinite (primeDivisorNormalization S) := by
  have := S.integral
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    isFinite_normalization_of_locallyOfFiniteType S.idealSheaf.subscheme
      (S.idealSheaf.subschemeι ≫ sY) _
  infer_instance

/-- Only finitely many prime divisors of `S^ν` map onto a given irreducible closed subset. -/
private theorem finite_branch {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y)
    (V : IrreducibleCloseds Y) :
    {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      primeDivisorNormalization S '' P.support = V}.Finite := by
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober V.isIrreducible V.isClosed
  have := isFinite_primeDivisorNormalization sY S
  refine (Set.Finite.preimage AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
    ((primeDivisorNormalization S).finite_preimage_singleton ξ)).subset fun P hP => ?_
  set ν := primeDivisorNormalization S
  have hP : ν '' P.support = V := hP
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hP
  have hcl : closure {ν P.genericPoint} = (V : Set Y) := by
    rw [← hP, ← Set.image_singleton]
    refine le_antisymm ?_ (image_closure_subset_closure_image ν.continuous)
    exact closure_minimal (Set.image_mono subset_closure) (ν.isClosedMap _ isClosed_closure)
  exact (show IsGenericPoint _ (V : Set Y) from hcl).eq hξ

private theorem finite_boundaryBranch {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (V : IrreducibleCloseds Y) :
    {P : (S : Q) ×
      MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y)) |
    primeDivisorNormalization (P.1 : MMP.Mori.PrimeDivisor Y) '' P.2.support = V}.Finite :=
  (Set.finite_univ.sigma fun (S : Q) _ =>
    finite_branch sY (S : MMP.Mori.PrimeDivisor Y) V).subset fun _ hP => ⟨Set.mem_univ _, hP⟩

private theorem one_le_boundaryBranchCount {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (hY : MMP.Mori.IsNormalVariety ℂ sY) (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (V : IrreducibleCloseds Y) (hV : codimension V = 2)
    (hVQ : (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)) :
    1 ≤ boundaryBranchCount Q V := by
  haveI := hY.1
  obtain ⟨S, P, hP⟩ := exists_primeDivisor_image_primeDivisorNormalization_eq sY
    (fun S : Q => (S : MMP.Mori.PrimeDivisor Y)) V hV (by
      intro x hx
      obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp (hVQ hx)
      exact Set.mem_iUnion.mpr ⟨⟨S, hS⟩, hxS⟩)
  rw [Nat.one_le_iff_ne_zero, boundaryBranchCount, ne_eq,
    Set.ncard_eq_zero (finite_boundaryBranch sY Q V)]
  exact Set.nonempty_iff_ne_empty.mp ⟨⟨S, P⟩, hP⟩

/-- For a complex variety `Y` and an irreducible closed subset `T ⊆ Y`, the preimage of `T`
under the first projection `Y ×_ℂ ℙ¹ ⟶ Y` is irreducible, closed and of dimension
`dim T + 1`. -/
private theorem preimage_fst_projectiveLine {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sY] (T : IrreducibleCloseds Y) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    IsIrreducible ((pullback.fst sY p).base ⁻¹' (T : Set Y)) ∧
      IsClosed ((pullback.fst sY p).base ⁻¹' (T : Set Y)) ∧
      topologicalKrullDim ((pullback.fst sY p).base ⁻¹' (T : Set Y)) =
        topologicalKrullDim (T : Set Y) + 1 := by
  intro p
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, T.isClosed⟩ : Closeds Y)
  haveI : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ T.isIrreducible
  haveI hv : AlgebraicGeometry.IsVariety ℂ (I.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hline := (isVariety_pullback_line_and_irreducibleComponents_baseChange_ratFunc
    (I.subschemeι ≫ sY) (𝟙 (Spec (.of ℂ)))).2.1
  let e := pullbackRightPullbackFstIso sY p I.subschemeι
  let φ := e.inv ≫ pullback.snd I.subschemeι (pullback.fst sY p)
  have hrange : Set.range (pullback.snd I.subschemeι (pullback.fst sY p)).base =
      (pullback.fst sY p).base ⁻¹' (T : Set Y) := by
    rw [Scheme.Pullback.range_snd, Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hφ : Set.range φ.base = (pullback.fst sY p).base ⁻¹' (T : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, e.inv.surjective.range_eq,
      Set.image_univ, hrange]
  haveI := hline.1.toIsIntegral
  refine ⟨?_, T.isClosed.preimage (pullback.fst sY p).base.hom.continuous, ?_⟩
  · rw [← hφ, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ φ.base.hom.continuous.continuousOn
  · have hG : topologicalKrullDim I.subscheme = topologicalKrullDim (T : Set Y) := by
      rw [I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph
          |>.topologicalKrullDim_eq,
        Scheme.IdealSheafData.range_subschemeι]
      rfl
    rw [← hφ, ← (φ.isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq,
      hline.2.1, hG]

/-- A surjective morphism of integral schemes carries generic points to generic points. -/
private theorem mem_genericPoints_of_surjective {Z X : Scheme} [IsIntegral Z] [IsIntegral X]
    (f : Z ⟶ X) [Surjective f] : ∀ η : genericPoints Z, f η.1 ∈ genericPoints X := by
  rintro ⟨η, hη⟩
  obtain rfl : η = genericPoint Z := by rwa [genericPoints_eq_singleton] at hη
  change f (genericPoint Z) ∈ genericPoints X
  rw [genericPoint_eq_of_isDominant f, genericPoints_eq_singleton]
  rfl

/-- A morphism from a reduced scheme whose image lies in the support of an ideal sheaf `I`
kills `I`. -/
private theorem le_ker_of_range_subset {X Y : Scheme} [IsReduced X] (I : Y.IdealSheafData)
    (f : X ⟶ Y) (h : Set.range f ⊆ I.support) : I ≤ f.ker := by
  have hk : f.ker = Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range f)) := by
    rw [← Category.id_comp f, Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot_of_isIso,
      ← Scheme.nilradical_eq_bot, ← Scheme.IdealSheafData.vanishingIdeal_top,
      Scheme.IdealSheafData.map_vanishingIdeal]
    simp
  rwa [hk, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    TopologicalSpace.Closeds.closure_le]

/-- A morphism from a reduced scheme onto the support of an ideal sheaf `I` lifts to a surjection
onto the closed subscheme cut out by `I`. -/
private theorem surjective_subschemeLift_of_range_eq {X Y : Scheme} [IsReduced X]
    (I : Y.IdealSheafData) (f : X ⟶ Y) (h : Set.range f = I.support) :
    Surjective (I.subschemeLift f (le_ker_of_range_subset I f h.le)) := ⟨fun y => by
  obtain ⟨x, hx⟩ : I.subschemeι y ∈ Set.range f := by
    rw [h, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  refine ⟨x, I.subschemeι.isClosedEmbedding.injective ?_⟩
  rw [← hx, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeLift_subschemeι]⟩

/-- A morphism from a normal integral scheme onto the support of a prime divisor `D` factors
uniquely through the normalization `D^ν ⟶ Y`. -/
private theorem existsUnique_lift_primeDivisorNormalization {X Y : Scheme} [IsIntegral X]
    [IsNormal X] (D : MMP.Mori.PrimeDivisor Y) (f : X ⟶ Y) (hf : Set.range f = D.support) :
    ∃! g : X ⟶ primeDivisorNormalizationScheme D, g ≫ primeDivisorNormalization D = f := by
  haveI := D.integral
  let L := D.idealSheaf.subschemeLift f (le_ker_of_range_subset _ f hf.le)
  have hL : L ≫ D.idealSheaf.subschemeι = f :=
    Scheme.IdealSheafData.subschemeLift_subschemeι _ _
  haveI : Surjective L := surjective_subschemeLift_of_range_eq D.idealSheaf f hf
  obtain ⟨g, hg, hu⟩ := Scheme.existsUnique_lift_normalization
    (MMP.finite_irreducibleComponents_of_isIntegral D.idealSheaf.subscheme) L
    (mem_genericPoints_of_surjective L)
  refine ⟨g, (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ D.idealSheaf.subschemeι) hg).trans hL), fun g' hg' => hu g' ?_⟩
  exact (cancel_mono D.idealSheaf.subschemeι).mp ((Category.assoc _ _ _).trans (hg'.trans hL.symm))

/-- The projective-line case of `MMP.Fourfold.product_line_basic`: for a normal complex variety
`Y`, the projection `Y ×_ℂ ℙ¹ ⟶ Y` is surjective and `Y ×_ℂ ℙ¹` is a normal variety of
dimension `dim Y + 1`. -/
private theorem product_projectiveLine {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (hY : MMP.Mori.IsNormalVariety ℂ sY) :
    Surjective (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))) ∧
      MMP.Mori.IsNormalVariety ℂ (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) ∧
      topologicalKrullDim (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) : Scheme.{0}) =
        topologicalKrullDim Y + 1 :=
  have h := (MMP.Fourfold.product_line_basic sY _ hY (Or.inl ⟨Iso.refl _, by simp⟩)).1
  ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The normalization `S^ν` of a prime divisor of a complex variety is a normal variety, and
`ν_S` maps it onto `S`. -/
private theorem isNormalVariety_primeDivisorNormalization {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsVariety ℂ sY] (S : MMP.Mori.PrimeDivisor Y) :
    MMP.Mori.IsNormalVariety ℂ (primeDivisorNormalization S ≫ sY) ∧
      Set.range (primeDivisorNormalization S) = (S.support : Set Y) := by
  haveI := S.integral
  haveI : AlgebraicGeometry.IsVariety ℂ (S.idealSheaf.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hspecS := (MMP.Threefold.normalization_spec (S.idealSheaf.subschemeι ≫ sY)).1
  haveI : Surjective (S.idealSheaf.subscheme.normalization
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)) := hspecS.2.2.2.1
  refine ⟨⟨?_, hspecS.2.1⟩, ?_⟩
  · have h1 := hspecS.1
    rwa [← Category.assoc] at h1
  · refine (range_primeDivisorNormalization_subset S).antisymm fun y hy => ?_
    obtain ⟨z, hz⟩ : y ∈ Set.range S.idealSheaf.subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    obtain ⟨w, rfl⟩ := (S.idealSheaf.subscheme.normalization
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)).surjective z
    exact ⟨w, hz⟩

private theorem isIntegral_of_isNormalVariety {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}
    (h : MMP.Mori.IsNormalVariety ℂ f) : IsIntegral X :=
  haveI := h.1
  AlgebraicGeometry.IsVariety.toIsIntegral (k := ℂ) (f := f)

/-- Clause (1): the normalization of `Φ S` is `S^ν ×_ℂ ℙ¹` through `ν_S × id`. -/
private theorem normalization_iso
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (Φ : MMP.Mori.PrimeDivisor Y ↪
      MMP.Mori.PrimeDivisor (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hΦ : ∀ S, ((Φ S).support : Set (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) :
      Scheme.{0})) = (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base ⁻¹'
        (S.support : Set Y)) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    ∀ S, ∃ e : primeDivisorNormalizationScheme (Φ S) ≅
          pullback (primeDivisorNormalization S ≫ sY) p,
        e.hom ≫ pullback.map (primeDivisorNormalization S ≫ sY) p sY p
          (primeDivisorNormalization S) (𝟙 _) (𝟙 _) (by simp) (by simp) =
          primeDivisorNormalization (Φ S) := by
  intro p S
  haveI := hY.1
  obtain ⟨hpr, hYb, -⟩ := product_projectiveLine sY hY
  haveI := hYb.1
  obtain ⟨hSν, hrS⟩ := isNormalVariety_primeDivisorNormalization sY S
  obtain ⟨hTν, hrT⟩ := isNormalVariety_primeDivisorNormalization (pullback.fst sY p ≫ sY) (Φ S)
  haveI := isIntegral_of_isNormalVariety hTν
  haveI : IsNormal (primeDivisorNormalizationScheme (Φ S)) := hTν.2
  obtain ⟨hfs, hN, -⟩ := product_projectiveLine _ hSν
  haveI : IsNormal (pullback (primeDivisorNormalization S ≫ sY) p) := hN.2
  haveI := isIntegral_of_isNormalVariety hN
  let m := pullback.map (primeDivisorNormalization S ≫ sY) p sY p
    (primeDivisorNormalization S) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hmf : m ≫ pullback.fst sY p = pullback.fst _ p ≫ primeDivisorNormalization S :=
    pullback.lift_fst _ _ _
  have hms : m ≫ pullback.snd sY p = pullback.snd _ p :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hrm : Set.range m = ((Φ S).support : Set (pullback sY p : Scheme.{0})) := by
    rw [Scheme.Pullback.range_map, hrS, hΦ]
    simp only [Scheme.Hom.id_base, TopCat.hom_id, ContinuousMap.coe_id, Set.range_id,
      Set.preimage_univ, Set.inter_univ]
    rfl
  obtain ⟨g, hg, -⟩ := existsUnique_lift_primeDivisorNormalization (Φ S) m hrm
  have hrf : Set.range (primeDivisorNormalization (Φ S) ≫ pullback.fst sY p) = S.support := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrT, hΦ]
    exact Set.image_preimage_eq _ hpr.surj
  obtain ⟨a, hav, -⟩ := existsUnique_lift_primeDivisorNormalization S _ hrf
  have hcond : a ≫ primeDivisorNormalization S ≫ sY =
      (primeDivisorNormalization (Φ S) ≫ pullback.snd sY p) ≫ p := by
    rw [← Category.assoc a, hav]
    simp only [Category.assoc, pullback.condition]
  obtain ⟨h, hh₁, hh₂⟩ : ∃ h, h ≫ pullback.fst (primeDivisorNormalization S ≫ sY) p = a ∧
      h ≫ pullback.snd (primeDivisorNormalization S ≫ sY) p =
        primeDivisorNormalization (Φ S) ≫ pullback.snd sY p :=
    ⟨pullback.lift _ _ hcond, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hhm : h ≫ m = primeDivisorNormalization (Φ S) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, ← Category.assoc h, hh₁, hav]
    · rw [Category.assoc, hms, hh₂]
  have hhg : h ≫ g = 𝟙 _ :=
    (existsUnique_lift_primeDivisorNormalization (Φ S) _ hrT).unique
      (by rw [Category.assoc, hg, hhm]) (Category.id_comp _)
  have hfs' : Set.range (pullback.fst (primeDivisorNormalization S ≫ sY) p ≫
      primeDivisorNormalization S) = S.support := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hfs.surj.range_eq, Set.image_univ,
      hrS]
  have hgh : g ≫ h = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc g, hh₁, Category.id_comp]
      refine (existsUnique_lift_primeDivisorNormalization S _ hfs').unique ?_ rfl
      rw [Category.assoc g, hav, ← Category.assoc g, hg, hmf]
    · rw [Category.assoc g, hh₂, ← Category.assoc g, hg, hms, Category.id_comp]
  exact ⟨⟨h, g, hhg, hgh⟩, hhm⟩

/-- For `g : X ⟶ Y` and the induced `g × id : X ×_Z L ⟶ Y ×_Z L`, the image of the preimage of
`A ⊆ X` is the preimage of `g(A)`. -/
private theorem image_preimage_fst_pullbackMap {X Y Z L : Scheme} (g : X ⟶ Y) (s : Y ⟶ Z)
    (p : L ⟶ Z) (A : Set X) :
    pullback.map (g ≫ s) p s p g (𝟙 _) (𝟙 _) (by simp) (by simp) ''
        (pullback.fst (g ≫ s) p ⁻¹' A) = pullback.fst s p ⁻¹' (g '' A) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨_, hx, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  · rintro ⟨a, ha, hya⟩
    obtain ⟨w, hw1, hw2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := g) (g := pullback.fst s p) a y hya
    let i := pullbackRightPullbackFstIso s p g
    have hi : i.hom ≫ pullback.map (g ≫ s) p s p g (𝟙 _) (𝟙 _) (by simp) (by simp) =
        pullback.snd g (pullback.fst s p) := by
      apply pullback.hom_ext <;> simp [i, pullback.condition]
    refine ⟨i.hom w, ?_, ?_⟩
    · rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, pullbackRightPullbackFstIso_hom_fst, hw1]
    · rw [← Scheme.Hom.comp_apply, hi, hw2]

/-- A prime divisor pulls back along an isomorphism to the prime divisor with the preimage
support. -/
private theorem exists_primeDivisor_support_eq_preimage {V W : Scheme.{0}} (f : V ⟶ W) [IsIso f]
    (D : MMP.Mori.PrimeDivisor W) :
    ∃ D' : MMP.Mori.PrimeDivisor V, D'.support = f ⁻¹' D.support := by
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne (inv f D.genericPoint) (by
    rw [coheight_eq_of_isOpenImmersion]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint D), ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
    f.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage f.continuous]
  congr 1
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · rintro rfl
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  · intro h
    calc x = (f ≫ inv f) x := by rw [IsIso.hom_inv_id]; rfl
      _ = _ := by rw [Scheme.Hom.comp_apply]; exact congrArg _ h

/-- Transporting prime divisors along an isomorphism `e : V ≅ W` over `Z` preserves the number of
prime divisors mapping onto a given subset of `Z`. -/
private theorem ncard_primeDivisor_image_eq_of_iso {V W Z : Scheme.{0}} (e : V ≅ W) {f : V ⟶ Z}
    {g : W ⟶ Z} (hf : e.hom ≫ g = f) (A : Set Z) :
    {D : MMP.Mori.PrimeDivisor V | f '' D.support = A}.ncard =
      {D : MMP.Mori.PrimeDivisor W | g '' D.support = A}.ncard := by
  subst hf
  have hc : ∀ B : Set V, (e.hom ≫ g) '' B = g '' (e.hom '' B) := fun B => by
    rw [Set.image_image]
    rfl
  have hinv : ∀ B : Set V, e.inv ⁻¹' B = e.hom '' B := fun B =>
    (congrFun (Set.image_eq_preimage_of_inverse (f := e.hom) (g := e.inv)
      (fun x => by rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl)
      (fun x => by rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl)) _).symm
  choose F hF using exists_primeDivisor_support_eq_preimage e.inv
  refine Set.ncard_congr (fun D _ => F D) (fun D hD => ?_) (fun D D' _ _ h => ?_) fun D hD => ?_
  · change g '' (F D).support = A
    rwa [hF, hinv, ← hc]
  · apply MMP.Resolution.Aux.PrimeDivisor.eq_of_support_eq
    have := congrArg AlgebraicGeometry.PrimeDivisor.support h
    rw [hF, hF] at this
    exact Set.preimage_injective.mpr e.inv.surjective this
  · obtain ⟨D0, hD0⟩ := exists_primeDivisor_support_eq_preimage e.hom D
    have hD0' : e.hom '' D0.support = D.support := by
      rw [hD0]
      exact Set.image_preimage_eq _ e.hom.surjective
    refine ⟨D0, ?_, MMP.Resolution.Aux.PrimeDivisor.eq_of_support_eq ?_⟩
    · change (e.hom ≫ g) '' D0.support = A
      rwa [hc, hD0']
    · rw [hF, hinv, hD0']

/-- On a complex threefold, the support of a prime divisor is never a curve. -/
private theorem support_ne_of_topologicalKrullDim_eq_one {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsVariety ℂ sY] (hdim : topologicalKrullDim Y = 3)
    (S : MMP.Mori.PrimeDivisor Y) (C : IrreducibleCloseds Y)
    (hC : topologicalKrullDim (C : Set Y) = 1) : (S.support : Set Y) ≠ C := by
  intro hSC
  have h2 := codimension_eq_of_topologicalKrullDim sY (a := 2) (b := 1) (hdim.trans rfl) C
    (hC.trans rfl)
  haveI := S.integral
  have h1 := S.codimension_one
  have hcl : IrreducibleCloseds.closureSingleton
      (S.idealSheaf.subschemeι (_root_.genericPoint S.idealSheaf.subscheme)) = C := by
    apply IrreducibleCloseds.ext
    rw [← hSC]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure S).symm
  rw [hcl, h2] at h1
  exact absurd h1 (by decide)

/-- For a curve `C`, the prime divisors of `S^ν ×_ℂ ℙ¹` mapping onto `pr⁻¹ C` under `ν_S × id`
correspond to the prime divisors of `S^ν` mapping onto `C`. -/
private theorem ncard_primeDivisor_image_pullbackMap
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3) (S : MMP.Mori.PrimeDivisor Y) (C : IrreducibleCloseds Y)
    (hC : topologicalKrullDim (C : Set Y) = 1) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    {D : MMP.Mori.PrimeDivisor (pullback (primeDivisorNormalization S ≫ sY) p) |
        pullback.map (primeDivisorNormalization S ≫ sY) p sY p (primeDivisorNormalization S)
          (𝟙 _) (𝟙 _) (by simp) (by simp) '' D.support =
          (pullback.fst sY p).base ⁻¹' (C : Set Y)}.ncard = branchNumber S C := by
  intro p
  haveI := hY.1
  obtain ⟨hSν, hrS⟩ := isNormalVariety_primeDivisorNormalization sY S
  haveI := hSν.1
  have hspr := (product_projectiveLine sY hY).1.surj
  have hK := image_preimage_fst_pullbackMap (primeDivisorNormalization S) sY p
  set M := pullback.map (primeDivisorNormalization S ≫ sY) p sY p
    (primeDivisorNormalization S) (𝟙 _) (𝟙 _) (by simp) (by simp)
  set fN := pullback.fst (primeDivisorNormalization S ≫ sY) p
  have hD := MMP.primeDivisor_pullback_line_eq_preimage_or_dense
    (primeDivisorNormalization S ≫ sY)
  have hfwd : ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S),
      ∃ D : MMP.Mori.PrimeDivisor (pullback (primeDivisorNormalization S ≫ sY) p),
        D.support = fN ⁻¹' P.support := hD.2.1.1
  choose F hF using hfwd
  rw [branchNumber, eq_comm]
  refine Set.ncard_congr (fun P _ => F P) ?_ ?_ ?_
  · intro P hP
    change primeDivisorNormalization S '' P.support = (C : Set Y) at hP
    change M '' (F P).support = (pullback.fst sY p).base ⁻¹' (C : Set Y)
    rw [hF, hK, hP]
  · intro P P' _ _ h
    apply MMP.Resolution.Aux.PrimeDivisor.eq_of_support_eq
    have := congrArg AlgebraicGeometry.PrimeDivisor.support h
    rw [hF, hF] at this
    exact Set.preimage_injective.mpr (product_projectiveLine _ hSν).1.surj this
  · intro D0 hmD0
    change M '' D0.support = (pullback.fst sY p).base ⁻¹' (C : Set Y) at hmD0
    rcases hD.2.1.2 D0 with ⟨Γ, -, hΓ⟩ | hdense
    · have hΓC : primeDivisorNormalization S '' Γ.support = (C : Set Y) := by
        apply Set.preimage_injective.mpr hspr
        rw [← hK, ← hmD0]
        exact congrArg _ hΓ.symm
      refine ⟨Γ, hΓC, MMP.Resolution.Aux.PrimeDivisor.eq_of_support_eq ?_⟩
      exact (hF Γ).trans hΓ.symm
    · refine absurd ?_ (support_ne_of_topologicalKrullDim_eq_one sY hdim S C hC)
      have hcomp : fN ≫ primeDivisorNormalization S = M ≫ pullback.fst sY p :=
        (pullback.lift_fst _ _ _).symm
      rw [← hrS, ← Set.image_univ, ← hD.2.2 D0 hdense, Set.image_image]
      change (fN ≫ primeDivisorNormalization S) '' _ = _
      rw [hcomp]
      change (fun x => pullback.fst sY p (M x)) '' _ = _
      rw [← Set.image_image, hmD0]
      exact Set.image_preimage_eq _ hspr

/-- Clause (2), one component at a time: for a curve `C`, `r_{pr⁻¹ C, Φ S} = r_{C, S}`. -/
private theorem branchNumber_preimage_curve
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3)
    (Φ : MMP.Mori.PrimeDivisor Y ↪
      MMP.Mori.PrimeDivisor (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hΦ : ∀ S, ((Φ S).support : Set (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) :
      Scheme.{0})) = (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base ⁻¹'
        (S.support : Set Y)) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    let pr := pullback.fst sY p
    ∀ S, ∀ C : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 →
      branchNumber (Φ S) (pr.base ⁻¹' (C : Set Y)) = branchNumber S C := by
  intro p pr S C hC
  obtain ⟨e, he⟩ := normalization_iso sY hY Φ hΦ S
  rw [branchNumber, ncard_primeDivisor_image_eq_of_iso e he]
  exact ncard_primeDivisor_image_pullbackMap sY hY hdim S C hC

/-- Clause (2): for a curve `C`, `r_{pr⁻¹ C} = r_C`. -/
private theorem boundaryBranchCount_preimage_curve
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3) (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (Φ : MMP.Mori.PrimeDivisor Y ↪
      MMP.Mori.PrimeDivisor (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hΦ : ∀ S, ((Φ S).support : Set (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) :
      Scheme.{0})) = (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base ⁻¹'
        (S.support : Set Y)) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    let pr := pullback.fst sY p
    ∀ C : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 →
        boundaryBranchCount (Q.map Φ) (pr.base ⁻¹' (C : Set Y)) =
            boundaryBranchCount Q C := by
  intro p pr C hC
  haveI := hY.1
  haveI := (product_projectiveLine sY hY).2.1.1
  obtain ⟨hirr, hcl, -⟩ := preimage_fst_projectiveLine sY C
  let V : IrreducibleCloseds (pullback sY p : Scheme.{0}) := ⟨_, hirr, hcl⟩
  rw [boundaryBranchCount_eq_sum (V := pr.base ⁻¹' (C : Set Y))
      (fun S _ => finite_branch (pr ≫ sY) S V),
    boundaryBranchCount_eq_sum (fun S _ => finite_branch sY S C), Finset.sum_map]
  exact Finset.sum_congr rfl fun S _ => branchNumber_preimage_curve sY hY hdim Φ hΦ S C hC

/-- Clause (2): for a curve `C ⊆ Q`, `pr⁻¹ C` is an irreducible closed surface with
`r_{pr⁻¹ C} = r_C`. -/
private theorem curve_preimage
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3) (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (Φ : MMP.Mori.PrimeDivisor Y ↪
      MMP.Mori.PrimeDivisor (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hΦ : ∀ S, ((Φ S).support : Set (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) :
      Scheme.{0})) = (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base ⁻¹'
        (S.support : Set Y)) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    let pr := pullback.fst sY p
    ∀ C : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 →
        (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) →
          IsIrreducible (pr.base ⁻¹' (C : Set Y)) ∧ IsClosed (pr.base ⁻¹' (C : Set Y)) ∧
          topologicalKrullDim (pr.base ⁻¹' (C : Set Y)) = 2 ∧
          boundaryBranchCount (Q.map Φ) (pr.base ⁻¹' (C : Set Y)) =
            boundaryBranchCount Q C := by
  intro p pr C hC hCQ
  haveI := hY.1
  obtain ⟨hirr, hcl, hd⟩ := preimage_fst_projectiveLine sY C
  refine ⟨hirr, hcl, ?_, boundaryBranchCount_preimage_curve sY hY hdim Q Φ hΦ C hC⟩
  rw [hd, hC]
  rfl

/-- Clause (2): `C ↦ pr⁻¹ C` is injective on curves. -/
private theorem preimage_injective_curves
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    let pr := pullback.fst sY p
    ∀ C C' : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 →
        topologicalKrullDim (C' : Set Y) = 1 →
        pr.base ⁻¹' (C : Set Y) = pr.base ⁻¹' (C' : Set Y) → C = C' := by
  intro p pr C C' _ _ h
  exact IrreducibleCloseds.ext
    (Set.preimage_injective.mpr (product_projectiveLine sY hY).1.surj h)

/-- Clause (3): every irreducible surface of `Q × ℙ¹` has branch count at least
one. -/
private theorem one_le_boundaryBranchCount_surface
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3) (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (Φ : MMP.Mori.PrimeDivisor Y ↪
      MMP.Mori.PrimeDivisor (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    ∀ V : IrreducibleCloseds (pullback sY p : Scheme.{0}),
        topologicalKrullDim (V : Set (pullback sY p : Scheme.{0})) = 2 →
        (V : Set (pullback sY p : Scheme.{0})) ⊆ ⋃ S ∈ Q.map Φ, (S.support : Set _) →
          1 ≤ boundaryBranchCount (Q.map Φ) V := by
  intro p V hV hVQ
  let pr := pullback.fst sY p
  obtain ⟨-, h, hd⟩ := product_projectiveLine sY hY
  haveI := h.1
  exact one_le_boundaryBranchCount (pr ≫ sY) h (Q.map Φ) V
    (codimension_eq_of_topologicalKrullDim (pr ≫ sY) (a := 2) (b := 2)
      (by rw [hd, hdim]; rfl) V (hV.trans rfl)) hVQ

/-- Clause (3): every irreducible curve of `Q` has branch count at least one. -/
private theorem one_le_boundaryBranchCount_curve
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3) (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (C : IrreducibleCloseds Y) (hC : topologicalKrullDim (C : Set Y) = 1)
    (hCQ : (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)) : 1 ≤ boundaryBranchCount Q C := by
  haveI := hY.1
  exact one_le_boundaryBranchCount sY hY Q C
    (codimension_eq_of_topologicalKrullDim sY (a := 2) (b := 1) (hdim.trans rfl) C (hC.trans rfl))
    hCQ

/-- Clause (4): for projective `Y`, `ρ_*(Φ(S)^ν) = ρ^□(S^ν)`. -/
private theorem divisorCycleRank_eq
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (Q : Finset (MMP.Mori.PrimeDivisor Y))
    (Φ : MMP.Mori.PrimeDivisor Y ↪
      MMP.Mori.PrimeDivisor (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hΦ : ∀ S, ((Φ S).support : Set (pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) :
      Scheme.{0})) = (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base ⁻¹'
        (S.support : Set Y)) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    let pr := pullback.fst sY p
    ∀ hproj : AlgebraicGeometry.IsProjectiveVariety ℂ sY, ∀ S ∈ Q,
        letI := primeDivisorNormalizationOver (pr ≫ sY) (Φ S)
        letI := primeDivisorNormalizationOver sY S
        haveI := isComplexScheme_primeDivisorNormalizationScheme sY hproj S
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme (Φ S)),
          MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme (Φ S)) =
            boxedSurfaceRank (primeDivisorNormalizationScheme S) := by
  intro p pr hproj S _
  letI := primeDivisorNormalizationOver (pr ≫ sY) (Φ S)
  letI := primeDivisorNormalizationOver sY S
  haveI := isComplexScheme_primeDivisorNormalizationScheme sY hproj S
  obtain ⟨e, he⟩ := normalization_iso sY hY Φ hΦ S
  letI : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ 1)).Over
      (Spec (.of ℂ)) := ⟨Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1⟩
  haveI := MMP.Fourfold.isComplexScheme_projectiveSpace 1 rfl
  haveI : MMP.IsComplexScheme (CategoryTheory.Limits.pullback
      ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ))
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1)) :=
    MMP.Chow.isComplexScheme_pullback _ _
  let L : projectiveLine ℂ ≅
      AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ 1) :=
    projectiveLineIsoProj ℂ
  have hL : L.hom ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1 = p :=
    projectiveLineIsoProj_hom_comp_projToSpecCoeff ℂ
  let f : pullback (primeDivisorNormalization S ≫ sY) p ≅
      CategoryTheory.Limits.pullback ((primeDivisorNormalizationScheme S) ↘ Spec (.of ℂ))
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1) :=
    pullback.congrHom rfl hL.symm ≪≫
      asIso (pullback.map _ _ _ _ (𝟙 _) L.hom (𝟙 _)
        (by rw [Category.id_comp, Category.comp_id]; rfl) (by simp))
  let g := e ≪≫ f
  have hg : g.hom ≫ (pullback.snd _ _ ≫
        Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ 1) =
      primeDivisorNormalizationScheme (Φ S) ↘ Spec (.of ℂ) := by
    show _ = primeDivisorNormalization (Φ S) ≫ pr ≫ sY
    rw [← he]
    simp only [g, f, pr, Iso.trans_hom, asIso_hom, pullback.congrHom_hom, Category.assoc,
      pullback.lift_snd_assoc, pullback.map, Category.id_comp, hL]
    rw [pullback.condition, pullback.lift_snd_assoc, Category.comp_id]
  haveI : g.hom.IsOver (Spec (.of ℂ)) := ⟨hg⟩
  haveI : MMP.IsComplexScheme (primeDivisorNormalizationScheme (Φ S)) :=
    MMP.IsComplexScheme.of_isFinite g.hom
  exact ⟨this, ((MMP.Analytic.cycleRank_eq_of_iso g hg).2.2.2 2).trans
    (boxedSurfaceRank_eq_divisorCycleRank _).symm⟩

/-- For a normal complex threefold `Y` and a reduced union `Q` of distinct prime divisors of `Y`,
with `pr : Y ×_ℂ ℙ¹ ⟶ Y` the first projection: `Y ×_ℂ ℙ¹` is a normal fourfold and there is an
embedding `Φ` of prime divisors with `supp Φ(S) = pr⁻¹(supp S)`, such that
(1) the normalization of `Φ(S)` is `S^ν ×_ℂ ℙ¹` through `ν_S × id`;
(2) for every irreducible curve `C ⊆ Q`, `pr⁻¹(C)` is an irreducible closed surface,
`C ↦ pr⁻¹(C)` is injective on curves, and `r_{pr⁻¹(C)}(Q.map Φ) = r_C(Q)`;
(3) every irreducible surface of `⋃_{S ∈ Q} Φ(S)` and every irreducible curve of `Q` has
branch count at least one;
(4) if `Y` is projective, `ρ_*(Φ(S)^ν) = ρ^□(S^ν)` for every prime divisor `S`. -/
@[mmp "lem_mmp_indexb_product_normalization"]
public theorem exists_embedding_primeDivisor_pullback_projectiveLine
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 3) (Q : Finset (MMP.Mori.PrimeDivisor Y)) :
    let p := projectiveLine ℂ ↘ Spec (.of ℂ)
    let pr := pullback.fst sY p
    MMP.Mori.IsNormalVariety ℂ (pr ≫ sY) ∧
    topologicalKrullDim (pullback sY p : Scheme.{0}) = 4 ∧
    ∃ Φ : MMP.Mori.PrimeDivisor Y ↪ MMP.Mori.PrimeDivisor (pullback sY p),
      -- `Φ S = S × ℙ¹`
      (∀ S, ((Φ S).support : Set (pullback sY p : Scheme.{0})) =
        pr.base ⁻¹' (S.support : Set Y)) ∧
      -- (1) `ν_S × id` is the normalization of `S × ℙ¹`
      (∀ S, ∃ e : primeDivisorNormalizationScheme (Φ S) ≅
          pullback (primeDivisorNormalization S ≫ sY) p,
        e.hom ≫ pullback.map (primeDivisorNormalization S ≫ sY) p sY p
          (primeDivisorNormalization S) (𝟙 _) (𝟙 _) (by simp) (by simp) =
          primeDivisorNormalization (Φ S)) ∧
      -- (2) curves `C ⊆ Q` and the surfaces `C × ℙ¹`
      (∀ C : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 →
        (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) →
          IsIrreducible (pr.base ⁻¹' (C : Set Y)) ∧ IsClosed (pr.base ⁻¹' (C : Set Y)) ∧
          topologicalKrullDim (pr.base ⁻¹' (C : Set Y)) = 2 ∧
          boundaryBranchCount (Q.map Φ) (pr.base ⁻¹' (C : Set Y)) =
            boundaryBranchCount Q C) ∧
      (∀ C C' : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 →
        topologicalKrullDim (C' : Set Y) = 1 →
        pr.base ⁻¹' (C : Set Y) = pr.base ⁻¹' (C' : Set Y) → C = C') ∧
      -- (3) positivity of branch counts
      (∀ V : IrreducibleCloseds (pullback sY p : Scheme.{0}),
        topologicalKrullDim (V : Set (pullback sY p : Scheme.{0})) = 2 →
        (V : Set (pullback sY p : Scheme.{0})) ⊆ ⋃ S ∈ Q.map Φ, (S.support : Set _) →
          1 ≤ boundaryBranchCount (Q.map Φ) V) ∧
      (∀ C : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 →
        (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) → 1 ≤ boundaryBranchCount Q C) ∧
      -- (4) cycle ranks, for projective `Y`
      (∀ hproj : AlgebraicGeometry.IsProjectiveVariety ℂ sY, ∀ S ∈ Q,
        letI := primeDivisorNormalizationOver (pr ≫ sY) (Φ S)
        letI := primeDivisorNormalizationOver sY S
        haveI := isComplexScheme_primeDivisorNormalizationScheme sY hproj S
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme (Φ S)),
          MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme (Φ S)) =
            boxedSurfaceRank (primeDivisorNormalizationScheme S)) := by
  intro p pr
  obtain ⟨hs, hN, hd⟩ := product_projectiveLine sY hY
  refine ⟨hN, by rw [hd, hdim]; rfl, ?_⟩
  haveI := hY.1
  choose F hF using (MMP.primeDivisor_pullback_line_eq_preimage_or_dense sY).2.1.1
  have hF' : ∀ S, ((F S).support : Set (pullback sY p : Scheme.{0})) =
      pr.base ⁻¹' (S.support : Set Y) := hF
  let Φ : MMP.Mori.PrimeDivisor Y ↪ MMP.Mori.PrimeDivisor (pullback sY p) :=
    ⟨F, fun S T hST => MMP.Resolution.Aux.PrimeDivisor.eq_of_support_eq
      (Set.preimage_injective.mpr hs.surj (by rw [← hF' S, ← hF' T, hST]))⟩
  exact ⟨Φ, hF', normalization_iso sY hY Φ hF',
    curve_preimage sY hY hdim Q Φ hF', preimage_injective_curves sY hY,
    one_le_boundaryBranchCount_surface sY hY hdim Q Φ,
    one_le_boundaryBranchCount_curve sY hY hdim Q, divisorCycleRank_eq sY hY Q Φ hF'⟩

end MMP.Fourfold

end
