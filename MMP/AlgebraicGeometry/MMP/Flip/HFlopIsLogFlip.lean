module

public import MMP.AlgebraicGeometry.MMP.Flip.TrivialFlopPullback

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

namespace MMP.FourfoldProofs.FourfoldFa15ProjectiveHFlopIsLogFlipProof

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### `ℝ`-Cartier combinations -/

section CartierCombination

variable {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]

private theorem isCartierCombination_add {D D' : RDivisor X} (h : IsCartierCombination D)
    (h' : IsCartierCombination D') : IsCartierCombination (D + D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r r', Fin.append L L', fun j => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hL i
    · simpa using hL' i
  · rw [Fin.sum_univ_add]
    simp

private theorem isCartierCombination_smul {D : RDivisor X} (h : IsCartierCombination D) (c : ℝ) :
    IsCartierCombination (c • D) := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  exact ⟨m, fun j => c * r j, L, hL, by simp [Finset.smul_sum, smul_smul]⟩

private theorem isCartierCombination_toRDivisor {L : Divisor X} (hL : L.IsCartier) :
    IsCartierCombination (Divisor.toRDivisor L) :=
  ⟨1, fun _ => 1, fun _ => L, fun _ => hL, by
    simp
    rfl⟩

end CartierCombination

/-! ### Relative ampleness and pull-back twists -/

section Ample

variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

private theorem isRelativelyAmple_add {f : Y ⟶ X} {A A' : RDivisor Y}
    (h : IsRelativelyAmple f A) (h' : IsRelativelyAmple f A') : IsRelativelyAmple f (A + A') := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := h
  obtain ⟨m', r', L', hm', hr', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r r', Fin.append L L', by omega, fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hr i
    · simpa using hr' i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hL i
    · simpa using hL' i
  · rw [Fin.sum_univ_add]
    simp

private theorem isRelativelyAmple_smul {f : Y ⟶ X} {A : RDivisor Y}
    (h : IsRelativelyAmple f A) {c : ℝ} (hc : 0 < c) : IsRelativelyAmple f (c • A) := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := h
  exact ⟨m, fun j => c * r j, L, hm, fun j => mul_pos hc (hr j), hL,
    by simp [Finset.smul_sum, smul_smul]⟩

/-- A Cartier divisor `D'` on `Y` which preserves `f`-ampleness of Cartier divisors under every
nonnegative multiple twist also preserves it for `ℝ`-divisors under every positive real twist. -/
private theorem isRelativelyAmple_add_smul_of_twist {f : Y ⟶ X} {A : RDivisor Y}
    (hA : IsRelativelyAmple f A) {D' : Divisor Y}
    (hD' : ∀ L : Divisor Y, IsRelativelyAmpleCartier f L → IsRelativelyAmpleCartier f (L + D'))
    {c : ℝ} (hc : 0 < c) : IsRelativelyAmple f (A + c • Divisor.toRDivisor D') := by
  have hq : ∀ q : ℕ, ∀ L, IsRelativelyAmpleCartier f L →
      IsRelativelyAmpleCartier f (L + q • D') := by
    intro q
    induction q with
    | zero => intro L hL; simpa using hL
    | succ q ih => intro L hL; rw [succ_nsmul, ← add_assoc]; exact hD' _ (ih L hL)
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hA
  let j0 : Fin m := ⟨0, hm⟩
  have hr0 := hr j0
  obtain ⟨q, hq'⟩ := exists_nat_gt (c / r j0)
  have hqpos : (0 : ℝ) < q := lt_trans (div_pos hc hr0) hq'
  have hεr : c / q < r j0 := by
    rw [div_lt_iff₀ hr0] at hq'
    rw [div_lt_iff₀ hqpos]
    linarith
  have hε : 0 < c / q := div_pos hc hqpos
  have h1 : IsRelativelyAmple f
      (∑ j, (r j - if j = j0 then c / q else 0) • Divisor.toRDivisor (L j)) := by
    refine ⟨m, _, L, hm, fun j => ?_, hL, rfl⟩
    by_cases h : j = j0
    · subst h
      simp only [ite_true]
      linarith
    · simpa [h] using hr j
  have h2 : IsRelativelyAmple f ((c / q) • Divisor.toRDivisor (L j0 + q • D')) :=
    isRelativelyAmple_smul ⟨1, fun _ => 1, fun _ => L j0 + q • D', le_rfl, fun _ => one_pos,
      fun _ => hq q _ (hL j0), by simp⟩ hε
  convert isRelativelyAmple_add h1 h2 using 1
  simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, map_add, map_nsmul, smul_add]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, div_mul_cancel₀ c hqpos.ne']
  abel

variable [IsLocallyNoetherian X] [IsNormal X]

/-- `L + f^*N` is `f`-ample for an `f`-ample Cartier divisor `L` and a Cartier divisor `N`. -/
private theorem isRelativelyAmpleCartier_add_of_isPullback (f : Y ⟶ X) [QuasiCompact f]
    {L : Divisor Y} (hL : IsRelativelyAmpleCartier f L) {N : Divisor X} (hN : N.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ N.supp}
    {N' : Divisor Y} (hN' : N.IsPullback f hB N') : IsRelativelyAmpleCartier f (L + N') := by
  obtain ⟨hLc, hamp⟩ := hL
  have hN'c : N'.IsCartier := hN'.isCartier hN
  have h1 : L.IsRelativelyAmple f hLc := by
    have := hLc.isInvertibleModule_divisorialSheaf
    intro y
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  have h2 := MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback f hLc h1 hN hN' hN'c
  have := (hLc.add hN'c).isInvertibleModule_divisorialSheaf
  exact ⟨hLc.add hN'c, fun U hU =>
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
      inferInstance h2).2 U hU⟩

/-- `A + c f^*N` is `f`-ample for an `f`-ample `ℝ`-divisor `A`, a Cartier divisor `N` and any
real `c`. -/
private theorem isRelativelyAmple_add_smul_of_isPullback (f : Y ⟶ X) [QuasiCompact f]
    {A : RDivisor Y} (hA : IsRelativelyAmple f A) {N : Divisor X} (hN : N.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ N.supp}
    {N' : Divisor Y} (hN' : N.IsPullback f hB N') (c : ℝ) :
    IsRelativelyAmple f (A + c • Divisor.toRDivisor N') := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hBn : ∀ Z : irreducibleComponents Y,
        f (componentGenericPoint Y Z) ∉ ((-1 : ℤ) • N).supp := by
      intro Z
      rw [neg_one_zsmul, DivisorWithCoeffs.supp_neg]
      exact hB Z
    have hpb := hN'.zsmul hN (-1) hBn
    have hNn : ((-1 : ℤ) • N).IsCartier := hN.zsmul (-1)
    have := isRelativelyAmple_add_smul_of_twist hA (D' := (-1 : ℤ) • N')
      (fun L hL => isRelativelyAmpleCartier_add_of_isPullback f hL hNn hpb) (neg_pos.mpr hc)
    convert this using 2
    rw [map_zsmul, neg_one_zsmul, smul_neg, neg_smul, neg_neg]
  · simpa using hA
  · exact isRelativelyAmple_add_smul_of_twist hA
      (fun L hL => isRelativelyAmpleCartier_add_of_isPullback f hL hN hN') hc

end Ample

/-! ### Transforms through the base -/

section Transform

private theorem transformDivisor_mapCoeffs {X Y : Scheme.{0}} {R S : Type*} [AddCommMonoid R]
    [AddCommMonoid S] (ρ : X.RationalMap Y) (c : R →+ S) (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor ρ (D.mapCoeffs c (map_zero c)) =
      (RationalMap.transformDivisor ρ D).mapCoeffs c (map_zero c) := by
  have : (RationalMap.transformDivisor ρ).comp (DivisorWithCoeffs.mapCoeffsAddMonoidHom c) =
      (DivisorWithCoeffs.mapCoeffsAddMonoidHom c).comp
        (RationalMap.transformDivisor ρ : DivisorWithCoeffs R X →+ _) := by
    refine Finsupp.addHom_ext fun P r => ?_
    simp only [AddMonoidHom.comp_apply, DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply,
      DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_single, RationalMap.transformDivisor_single]
    cases RationalMap.transformPrimeDivisor ρ P <;> simp
  exact DFunLike.congr_fun this D

/-- The generic point of a prime divisor lies outside every closed set of codimension at least
two. -/
private theorem genericPoint_notMem_of_two_le_closedsCodimension {X : Scheme.{0}}
    (Z : TopologicalSpace.Closeds X) (hZ : 2 ≤ closedsCodimension Z)
    (P : MMP.Mori.PrimeDivisor X) : P.genericPoint ∉ Z := by
  intro hP
  have hsub : ((irreducibleSetEquivPoints (α := X)).symm P.genericPoint : Set X) ⊆ Z :=
    Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hP)
  have h2 := le_closedsCodimension_iff.mp hZ _ hsub
  rw [codimension_eq_coheight, Order.coheight_orderIso, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

private theorem ι_morphismRestrict_apply {Y T : Scheme.{0}} (g : Y ⟶ T) (U : T.Opens)
    (p : (g ⁻¹ᵁ U).toScheme) : U.ι ((g ∣_ U) p) = g ((g ⁻¹ᵁ U).ι p) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- `g` is injective on the preimage of its biregular locus. -/
private theorem eq_of_mem_preimage_biregularLocus {Y T : Scheme.{0}} (g : Y ⟶ T) {y y' : Y}
    (hy : y ∈ g ⁻¹ᵁ biregularLocus g) (hy' : y' ∈ g ⁻¹ᵁ biregularLocus g) (h : g y = g y') :
    y = y' := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have : (⟨y, hy⟩ : (g ⁻¹ᵁ biregularLocus g).toScheme) = ⟨y', hy'⟩ :=
    (g ∣_ biregularLocus g).isOpenEmbedding.injective <|
      (biregularLocus g).ι.isOpenEmbedding.injective <|
        (ι_morphismRestrict_apply g _ ⟨y, hy⟩).trans
          (h.trans (ι_morphismRestrict_apply g _ ⟨y', hy'⟩).symm)
  exact congrArg Subtype.val this

/-- A rational map `ρ : X ⤏ Y` over `T`, defined in codimension one, sends a prime divisor `P`
of `X` to the prime divisor `DY` of `Y` lying over the image of `P` in the biregular locus of
`g`. -/
private theorem transformPrimeDivisor_eq_some_of_isOver {X Y T : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] [IsSeparated (T ↘ Limits.terminal Scheme)]
    {f : X ⟶ T} {g : Y ⟶ T} {ρ : X.RationalMap Y} (hρ : RationalMap.IsOver f g ρ)
    (hρc : RationalMap.IsMorphismInCodimOne ρ) (P : MMP.Mori.PrimeDivisor X)
    (DY : MMP.Mori.PrimeDivisor Y) (hDY : g DY.genericPoint = f P.genericPoint)
    (htB : f P.genericPoint ∈ biregularLocus g) :
    RationalMap.transformPrimeDivisor ρ P = some DY := by
  have hξd : P.genericPoint ∈ RationalMap.dom ρ := by
    by_contra h
    exact genericPoint_notMem_of_two_le_closedsCodimension (RationalMap.dom ρ).compl hρc P h
  obtain ⟨g', hξg', hg'⟩ := RationalMap.definedAt_iff.mp hξd
  have hy' : g (g'.hom ⟨P.genericPoint, hξg'⟩) = f P.genericPoint := by
    have h := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq (g := g'.compHom g)
      (g' := f.toPartialMap) (by rw [Scheme.RationalMap.compHom_toRationalMap, hg']; exact hρ)
      hξg' trivial
    change (g'.hom ≫ g) ⟨P.genericPoint, hξg'⟩ = (X.topIso.hom ≫ f) ⟨P.genericPoint, trivial⟩ at h
    exact h
  have hy'y : g'.hom ⟨P.genericPoint, hξg'⟩ = DY.genericPoint :=
    eq_of_mem_preimage_biregularLocus g (by change g _ ∈ biregularLocus g; rw [hy']; exact htB)
      (by change g _ ∈ biregularLocus g; rw [hDY]; exact htB) (hy'.trans hDY.symm)
  refine RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨RationalMap.definedAt_iff.mpr ⟨g', hξg', hg'⟩, ?_⟩
  have hc : RationalMap.transform ρ P.idealSheaf.support = DY.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hξg', hy'y]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure DY).symm
  have := DY.integral
  rw [RationalMap.transformIdeal, hc, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- Under the hypotheses of `transformDivisor_eq_inverseTransformDivisor`, every prime divisor
of `X` is transformed by `ρ` to the strict transform through `T` of its image on `T`. -/
private theorem exists_transformPrimeDivisor_eq_some {X Y T : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] [IsSeparated (T ↘ Limits.terminal Scheme)]
    {f : X ⟶ T} {g : Y ⟶ T} [IsProper g] (hg : IsBirationalMorphism g)
    (hf : IsIsoInCodimOne f) {ρ : X.RationalMap Y} (hρ : RationalMap.IsOver f g ρ)
    (hρc : RationalMap.IsMorphismInCodimOne ρ) (P : MMP.Mori.PrimeDivisor X) :
    ∃ (DT : MMP.Mori.PrimeDivisor T) (DY : MMP.Mori.PrimeDivisor Y),
      RationalMap.transformPrimeDivisor f.toRationalMap P = some DT ∧
      inverseTransformPrimeDivisor g DT = some DY ∧
      RationalMap.transformPrimeDivisor ρ P = some DY := by
  obtain ⟨V, W, hV, -, hle, hiso⟩ := hf
  have hξV : P.genericPoint ∈ V.compl :=
    genericPoint_notMem_of_two_le_closedsCodimension V hV P
  let U : X.Opens := V.compl
  let U' : T.Opens := W.compl
  let p : U.toScheme := ⟨P.genericPoint, hξV⟩
  have hfp : U'.ι (f.resLE U' U hle p) = f P.genericPoint := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    rfl
  have hT1 : Order.coheight (f P.genericPoint) = 1 := by
    rw [← hfp, Topology.IsOpenEmbedding.coheight_eq _ U'.ι.isOpenEmbedding,
      Topology.IsOpenEmbedding.coheight_eq _ (f.resLE U' U hle).isOpenEmbedding,
      ← Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding]
    exact P.coheight_genericPoint
  let DT : MMP.Mori.PrimeDivisor T :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne (f P.genericPoint) hT1
  have hDT : MMP.Mori.PrimeDivisor.genericPoint DT = f P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hT1
  have htB : f P.genericPoint ∈ biregularLocus g :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg hT1.le
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  obtain ⟨q, hq⟩ := (g ∣_ biregularLocus g).surjective ⟨f P.genericPoint, htB⟩
  have hgq : g q.1 = f P.genericPoint := by
    have := ι_morphismRestrict_apply g _ q
    rw [hq] at this
    exact this.symm
  have hy1 : Order.coheight q.1 = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g (show g q.1 ∈ _ from hgq ▸ htB),
      hgq, hT1]
  let DY : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne q.1 hy1
  have hDY : MMP.Mori.PrimeDivisor.genericPoint DY = q.1 :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy1
  exact ⟨DT, DY, (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P DT).mpr
    hDT.symm, MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (by rw [hDY, hgq, hDT]) (by rw [hDY, hgq]; exact htB),
    transformPrimeDivisor_eq_some_of_isOver hρ hρc P DY (by rw [hDY, hgq]) htB⟩

/-- A rational map `ρ : X ⤏ Y` over `T`, defined in codimension one, between integral schemes,
with `f : X ⟶ T` an isomorphism in codimension one and `g : Y ⟶ T` proper birational onto the
normal `T`, transforms divisors as `g⁻¹_* ∘ f_*`. -/
private theorem transformDivisor_eq_inverseTransformDivisor {X Y T : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] [IsSeparated (T ↘ Limits.terminal Scheme)]
    {f : X ⟶ T} {g : Y ⟶ T} [IsProper g] (hg : IsBirationalMorphism g)
    (hf : IsIsoInCodimOne f) {ρ : X.RationalMap Y} (hρ : RationalMap.IsOver f g ρ)
    (hρc : RationalMap.IsMorphismInCodimOne ρ) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor ρ D =
      inverseTransformDivisor g (RationalMap.transformDivisor f.toRationalMap D) := by
  classical
  have : (RationalMap.transformDivisor ρ : DivisorWithCoeffs R X →+ _) =
      (inverseTransformDivisor g).comp (RationalMap.transformDivisor f.toRationalMap) := by
    refine Finsupp.addHom_ext fun P r => ?_
    obtain ⟨DT, DY, h1, h2, h3⟩ := exists_transformPrimeDivisor_eq_some hg hf hρ hρc P
    rw [AddMonoidHom.comp_apply, RationalMap.transformDivisor_single_of_eq_some h3,
      RationalMap.transformDivisor_single_of_eq_some h1,
      inverseTransformDivisor_single_of_eq_some h2]
  exact DFunLike.congr_fun this D

private theorem transformDivisor_smul {X Y : Scheme.{0}} (ρ : X.RationalMap Y) (c : ℝ)
    (D : RDivisor X) :
    RationalMap.transformDivisor ρ (c • D) = c • RationalMap.transformDivisor ρ D :=
  (RationalMap.transformDivisorₗ ℝ ρ).map_smul c D

/-- Under the hypotheses of `transformDivisor_eq_inverseTransformDivisor`, `ρ` transforms a
divisor `MX` with `MX = r (K + B)` to a divisor `MY` with `MY = r (K_Y + B_Y)`, where `K_Y + B_Y`
is the transform of `K + B` through `T`. -/
private theorem transformDivisor_toRDivisor_eq {X Y T : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] [IsSeparated (T ↘ Limits.terminal Scheme)]
    {f : X ⟶ T} {g : Y ⟶ T} [IsProper g] (hg : IsBirationalMorphism g)
    (hf : IsIsoInCodimOne f) {ρ : X.RationalMap Y} (hρ : RationalMap.IsOver f g ρ)
    (hρc : RationalMap.IsMorphismInCodimOne ρ) {K : Divisor X} {B : QDivisor X} {r : ℕ}
    {MX : Divisor X} {MY : Divisor Y}
    (hMX : Divisor.toQDivisor MX = (r : ℤ) • (Divisor.toQDivisor K + B))
    (hMY : Divisor.toQDivisor MY = (r : ℤ) •
      (Divisor.toQDivisor (inverseTransformDivisor g (RationalMap.transformDivisor
        f.toRationalMap K)) +
        inverseTransformDivisor g (RationalMap.transformDivisor f.toRationalMap B))) :
    RationalMap.transformDivisor ρ (Divisor.toRDivisor MX) = Divisor.toRDivisor MY := by
  have htr := fun {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X) =>
    transformDivisor_eq_inverseTransformDivisor hg hf hρ hρc D
  have hX := congrArg QDivisor.toRDivisor hMX
  have hY := congrArg QDivisor.toRDivisor hMY
  rw [QDivisor.toRDivisor_toQDivisor, map_zsmul, map_add, QDivisor.toRDivisor_toQDivisor] at hX hY
  rw [hX, hY, map_zsmul, map_add]
  congr 1
  have hK := transformDivisor_mapCoeffs ρ (Int.castAddHom ℝ) K
  have hB := transformDivisor_mapCoeffs ρ (Rat.castHom ℝ).toAddMonoidHom B
  change RationalMap.transformDivisor ρ (Divisor.toRDivisor K) +
    RationalMap.transformDivisor ρ (QDivisor.toRDivisor B) = _
  erw [hK, hB, htr K, htr B]
  rfl

end Transform

/-! ### Flips and pull-back twists -/

section Flip

variable {k : Type} [Field k] {X Y T : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsLocallyNoetherian T]
  [IsNormal T] {f : X ⟶ T} {g : Y ⟶ T} {ρ : X.RationalMap Y} {M : Divisor T}
  {hBX : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ M.supp} {MX : Divisor X}
  {hBY : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ M.supp} {MY : Divisor Y}

/-- A flip with respect to `D` is a flip with respect to `a D + b f^*M` for `a > 0`, a Cartier
divisor `M` on `T` and pull-backs `f^*M`, `g^*M` corresponding under the transform. -/
private theorem isFlip_smul_add_smul_of_isPullback {D : RDivisor X}
    (h : IsFlip k sX sT sY D f g ρ) {a : ℝ} (ha : 0 < a) (b : ℝ) (hMc : M.IsCartier)
    (hpbX : M.IsPullback f hBX MX) (hpbY : M.IsPullback g hBY MY)
    (hτ : RationalMap.transformDivisor ρ (Divisor.toRDivisor MX) = Divisor.toRDivisor MY) :
    IsFlip k sX sT sY (a • D + b • Divisor.toRDivisor MX) f g ρ := by
  have hτ' : RationalMap.transformDivisor ρ (a • D + b • Divisor.toRDivisor MX) =
      a • RationalMap.transformDivisor ρ D + b • Divisor.toRDivisor MY := by
    rw [map_add, transformDivisor_smul, transformDivisor_smul, hτ]
  have := h.isProper
  have := h.isSmall_source.isProper
  exact
    { h.toIsGeneralizedFlip with
      isCartierCombination := isCartierCombination_add
        (isCartierCombination_smul h.isCartierCombination _)
        (isCartierCombination_smul (isCartierCombination_toRDivisor (hpbX.isCartier hMc)) _)
      isRelativelyAntiAmple := by
        change IsRelativelyAmple f (-_)
        convert isRelativelyAmple_add_smul_of_isPullback f
          (isRelativelyAmple_smul h.isRelativelyAntiAmple ha) hMc hpbX (-b) using 2
        rw [neg_add, smul_neg, neg_smul]
      isCartierCombination_transform := by
        rw [hτ']
        exact isCartierCombination_add
          (isCartierCombination_smul h.isCartierCombination_transform _)
          (isCartierCombination_smul (isCartierCombination_toRDivisor (hpbY.isCartier hMc)) _)
      isRelativelyAmple_transform := by
        rw [hτ']
        exact isRelativelyAmple_add_smul_of_isPullback g
          (isRelativelyAmple_smul h.isRelativelyAmple_transform ha) hMc hpbY _
      isSmall_source := h.isSmall_source }

/-- Flips with respect to `E` and to `a E + b f^*M` agree for `a > 0`, a Cartier divisor `M` on
`T` and pull-backs `f^*M`, `g^*M` corresponding under the transform of every map over `T`
defined in codimension one. -/
private theorem isFlip_iff_isFlip_of_isPullback {E D : RDivisor X} {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hD : D = a • E + b • Divisor.toRDivisor MX) (hMc : M.IsCartier)
    (hpbX : M.IsPullback f hBX MX) (hpbY : M.IsPullback g hBY MY)
    (hτ : RationalMap.IsOver f g ρ → RationalMap.IsMorphismInCodimOne ρ →
      RationalMap.transformDivisor ρ (Divisor.toRDivisor MX) = Divisor.toRDivisor MY) :
    IsFlip k sX sT sY E f g ρ ↔ IsFlip k sX sT sY D f g ρ := by
  subst hD
  refine ⟨fun h => isFlip_smul_add_smul_of_isPullback h ha b hMc hpbX hpbY
    (hτ h.isModificationOf.2 h.isMorphismInCodimOne), fun h => ?_⟩
  convert isFlip_smul_add_smul_of_isPullback h (inv_pos.mpr ha) (-(a⁻¹ * b)) hMc hpbX hpbY
    (hτ h.isModificationOf.2 h.isMorphismInCodimOne) using 1
  rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul, neg_smul]
  abel

end Flip

/-- The structure morphism of a scheme separated over `Spec k` is separated over the terminal
scheme. -/
private theorem isSeparated_terminal {k : Type} [Field k] {Z : Scheme.{0}}
    (s : Z ⟶ Spec (.of k)) [IsSeparated s] : IsSeparated (Z ↘ Limits.terminal Scheme) := by
  rw [show (Z ↘ Limits.terminal Scheme) = s ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

end MMP.FourfoldProofs.FourfoldFa15ProjectiveHFlopIsLogFlipProof

end

section

/-!
# Projective `H`-flops are perturbed log flips

Let `(X, B)` be a klt pair on a projective variety over an algebraically closed field `k` of
characteristic zero, with `B` a `ℚ`-divisor, and let `H ≥ 0` be a `ℚ`-Cartier `ℚ`-divisor on `X`.
Let `f : X ⟶ T` be a small contraction onto a normal projective variety with `K_X + B` numerically
`f`-trivial and `-H` `f`-ample, and let `η > 0` be rational with `(X, B + η H)` klt. For a small
projective birational morphism `g : Y ⟶ T` from a normal variety and a birational map
`ρ : X ⤏ Y`, the triple `(Y, g, ρ)` is an `H`-flop of `f` with respect to `K_X + B` if and only
if it is a log flip of `f` for the pair `(X, B + η H)`: since `K_X + B` and its transform on `Y`
are pullbacks of one `ℚ`-Cartier divisor on `T`, the transforms of `H` and of `K_X + B + η H` are
`ℚ`-Cartier and relatively ample simultaneously.

## Main results

* `MMP.Flips.IsHFlop.iff_isLogFlip_add_smul`

## Implementation notes

The complex numbers of the source are replaced by an algebraically closed field of characteristic
zero, as in `MMP.Flips.IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne`. "Small" is the
contraction notion `MMP.Flips.IsSmall` for both `f` and `g`, and projectivity of `g` is
`AlgebraicGeometry.IsProjective`.

By the projective trivial-flop bundle, there are `r > 0` and a Cartier divisor `M` on `T` with
`f^*M = r (K_X + B)` and `g^*M = r (K_Y + B_Y)`, where `K_Y + B_Y` is the transform of `K_X + B`
through `T`. Since `ρ` is a map over `T`, an isomorphism at the generic points of the prime
divisors of `X`, its transform agrees with the transform through `T`. Hence
`K + B + η H` and `η H` differ, on `X` and on `Y`, by a rational multiple of the pull-back of a
Cartier divisor from `T`, which changes neither `ℝ`-Cartierness nor relative ampleness.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 6.8, 15.4
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori MMP.FourfoldProofs.FourfoldFa15ProjectiveHFlopIsLogFlipProof

/-- **`H`-flops of a projective contraction are log flips of the perturbed pair.** Let `(X, B)` be
klt (`MMP.Flips.IsKawamataLogTerminal`) on a projective variety over an algebraically closed field
of characteristic zero, with canonical divisor `K` of dimension `n` and `B` a `ℚ`-divisor, and let
`H ≥ 0` be a `ℚ`-Cartier `ℚ`-divisor. Let `f : X ⟶ T` be a small contraction
(`MMP.Flips.IsSmall`) onto a normal projective variety with `K + B` numerically `f`-trivial and
`-H` `f`-ample, and let `η > 0` be rational with `(X, B + η H)` klt. Then for every small
projective morphism `g : Y ⟶ T` from a normal scheme and every rational map `ρ : X ⤏ Y`,
`(g, ρ)` is an `H`-flop of `f` with respect to `K + B` (`MMP.Flips.IsHFlop`) if and only if it is a
log flip of `f` for `(X, B + η H)` (`MMP.Flips.IsLogFlip`). -/
@[mmp "lem_fourfold_fa15_projective_h_flop_is_log_flip"]
public theorem IsHFlop.iff_isLogFlip_add_smul
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y T : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsNormal T]
    (hX : Mori.IsProjectiveVariety k sX) (hT : Mori.IsProjectiveVariety k sT)
    {n : ℕ} {K : Divisor X} {B H : QDivisor X}
    (hklt : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor B))
    (hH : 0 ≤ H) (hHC : H.IsQCartier)
    {f : X ⟶ T} (hf : IsSmall k sT sX f)
    (htriv : IsNumericallyTrivialOver k sX f (logCanonicalDivisor K (QDivisor.toRDivisor B)))
    (hHf : IsRelativelyAntiAmple f (QDivisor.toRDivisor H))
    {η : ℚ} (hη : 0 < η) (hkltη : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor (B + η • H)))
    {g : Y ⟶ T} (hg : IsSmall k sT sY g) (hgp : IsProjective g) (ρ : X.RationalMap Y) :
    IsHFlop k sX sT sY n K (QDivisor.toRDivisor B) H f g ρ ↔
      IsLogFlip k sX sT sY n K (QDivisor.toRDivisor (B + η • H)) f g ρ := by
  have hTv : AlgebraicGeometry.IsVariety k sT := hT.toIsVariety
  have : IsIntegral T := hTv.toIsIntegral
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have : QuasiCompact sT := hTv.toQuasiCompact
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have hYv : AlgebraicGeometry.IsVariety k sY := hg.isVariety_source
  have : IsIntegral Y := hYv.toIsIntegral
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : IsProper f := hf.isProper
  have : IsProper g := hg.isProper
  have := hYv.toIsSeparated
  have := hTv.toIsSeparated
  have := isSeparated_terminal sY
  have := isSeparated_terminal sT
  have hY : MMP.Mori.IsProjectiveVariety k sY := by
    refine (AlgebraicGeometry.isProjectiveVariety_iff k sY).2 ⟨hYv, ?_⟩
    rw [← isProjective_iff_isProjectiveMorphism_of_isAffine, ← hg.comp_eq]
    exact hgp.comp ((isProjective_iff_isProjectiveMorphism_of_isAffine sT).2 hT.isProjective)
  have hR : QDivisor.toRDivisor (Divisor.toQDivisor K + B) =
      logCanonicalDivisor K (QDivisor.toRDivisor B) := by
    rw [map_add, QDivisor.toRDivisor_toQDivisor]
    rfl
  obtain ⟨-, ⟨r, hr, M, -, hMc, ⟨MX, hBX, hMX, hpbX⟩, ⟨MY, hBY, hMY, hpbY⟩⟩, -⟩ :=
    IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne hX hY hT hf.comp_eq hg.comp_eq
      (IsSmall.isBirationalMorphism sT sX hf) (IsSmall.isBirationalMorphism sT sY hg)
      hf.exists_isIso hg.exists_isIso hklt (by rw [hR]; exact htriv)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  have hsmul : QDivisor.toRDivisor (η • H) = (η : ℝ) • QDivisor.toRDivisor H := by
    ext P
    change (((η • H).coeff P : ℚ) : ℝ) = (η : ℝ) * ((H.coeff P : ℚ) : ℝ)
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul, Rat.cast_mul]
  have hD : logCanonicalDivisor K (QDivisor.toRDivisor (B + η • H)) =
      (η : ℝ) • QDivisor.toRDivisor H + (r : ℝ)⁻¹ • Divisor.toRDivisor MX := by
    have h := congrArg QDivisor.toRDivisor hMX
    rw [QDivisor.toRDivisor_toQDivisor, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, map_add,
      QDivisor.toRDivisor_toQDivisor] at h
    rw [h, smul_smul, Int.cast_natCast, inv_mul_cancel₀ hr'.ne', one_smul, logCanonicalDivisor,
      map_add, hsmul]
    abel
  have hflip := isFlip_iff_isFlip_of_isPullback (sX := sX) (sY := sY) (sT := sT) (ρ := ρ) hη' _
    hD hMc hpbX hpbY fun hρ hρc => transformDivisor_toRDivisor_eq
      (IsSmall.isBirationalMorphism sT sY hg) hf.exists_isIso hρ hρc hMX hMY
  have hlc : IsLogCanonical sX n K (QDivisor.toRDivisor B) := by
    obtain ⟨h1, h2, h3, h4⟩ := hklt
    exact ⟨h1, h2, h3, fun F hF a ha => by linarith [h4 F hF (1 + a) ⟨a, ha, rfl⟩]⟩
  constructor
  · rintro ⟨-, -, -, -, -, hfl⟩
    exact ⟨hkltη.1, hkltη.2.1, hflip.1 hfl⟩
  · rintro ⟨-, -, hfl⟩
    exact ⟨hlc, hHC, hf, htriv, hHf, hflip.2 hfl⟩

end MMP.Flips

end
