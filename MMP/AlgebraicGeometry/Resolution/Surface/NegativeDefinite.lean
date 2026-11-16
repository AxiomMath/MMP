module

public import MMP.AlgebraicGeometry.Resolution.Blowup
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.LinearAlgebra.Matrix.NegativeDefinite
public import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
public import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor

/-!
# Negative definiteness of exceptional curves on a smooth surface (Kollár 2.12)

Let `f : X → Y` be a projective, generically finite morphism from a smooth surface `X` to a
quasi-projective variety `Y`, and `C₁, …, Cₘ` distinct `f`-exceptional curves. Then the
intersection matrix `((Cᵢ · Cⱼ))` is negative definite ("Hodge index theorem").

## Main results

* `MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isContractedProjectiveCurve`

## Implementation notes

* Each curve `Cᵢ` is given twice: as a prime divisor `Pᵢ` of `X` (a Cartier divisor, since `X` is
  smooth: `MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme`) and as the proper curve
  `Cᵢ` with the same generic point; `(Cᵢ · Cⱼ)` is the intersection number
  `MMP.Mori.QDivisor.intersectionNumber` of `Pᵢ` with `Cⱼ`. This is the form used by
  `MMP.Threefold.Mori.coeff_nonpos_of_negDef_of_intersectionNumber_nonneg`.
* "Negative definite" is `Matrix.PosDef` of the negated real matrix (which includes symmetry).
* `f` is *generically finite* if some open `V ⊆ Y` meeting `f(X)` has `f⁻¹(V) → V` finite;
  `Y` is quasi-projective if `s_Y` is H-quasi-projective (an immersion into some `ℙⁿ_k`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Threefold.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Threefold.Resolution

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-! ### Divisors on a smooth scheme -/

section Smooth

variable {U : Scheme.{u}} {sU : U ⟶ Spec (.of k)} [QuasiCompact sU] [IsLocallyNoetherian U]
  [IsNormal U]

omit [QuasiCompact sU] in
/-- On a smooth scheme every divisor is Cartier. -/
theorem isCartier_of_isSmoothScheme (hsm : IsSmoothScheme sU) (D : Divisor U) : D.IsCartier := by
  induction D using Finsupp.induction_linear with
  | zero => exact Divisor.isCartier_zero
  | add f g hf hg => exact hf.add hg
  | single E n =>
    simpa [Finsupp.smul_single] using
      (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm E).zsmul n

/-- The degree along a curve is additive over finite sums of divisors on a smooth scheme. -/
theorem degreeOn_finset_sum (hsm : IsSmoothScheme sU) {C : Scheme.{u}} (i : C ⟶ U)
    [IsProper (i ≫ sU)] (hdim : topologicalKrullDim C ≤ 1) {ι : Type*} (s : Finset ι)
    (D : ι → Divisor U) :
    (∑ j ∈ s, D j).degreeOn k sU i hdim (isCartier_of_isSmoothScheme hsm _) =
      ∑ j ∈ s, (D j).degreeOn k sU i hdim (isCartier_of_isSmoothScheme hsm _) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Divisor.degreeOn_zero' k sU i hdim
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact Divisor.degreeOn_add k sU i hdim _ _ _ _

/-- A curve `C` whose generic point lies on no component of an effective divisor `D` has
`deg_C 𝒪_U(D) ≥ 0`. -/
theorem degreeOn_nonneg_of_coeff_eq_zero (hsm : IsSmoothScheme sU) (D : Divisor U) (hD : 0 ≤ D)
    (C : ProperCurve sU) (P : Mori.PrimeDivisor U) (hC : C.point = P.genericPoint)
    (hP : D P = 0) :
    0 ≤ D.degreeOn k sU C.ι C.dim_le (isCartier_of_isSmoothScheme hsm D) := by
  obtain ⟨c, hc⟩ := exists_ι_eq_point C.point
  refine (degreeOn_nonneg_and_eq_zero_iff sU C.ι C.dim_le D _ hD ⟨c, ?_⟩).1
  change curveSubschemeAtι C.point c ∉ _
  rw [hc, hC]
  intro hmem
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
  obtain rfl := primeDivisor_eq_of_genericPoint_mem_support E P hxE
  exact hE hP

omit [IsLocallyNoetherian U] [IsNormal U] in
/-- For an effective divisor `W` and distinct prime divisors `Pᵢ`, the divisor
`W - ∑ᵢ W(Pᵢ) Pᵢ` is effective and has coefficient zero along every `Pᵢ`. -/
theorem sub_sum_single_nonneg_and_apply_eq_zero {m : ℕ} {P : Fin m → Mori.PrimeDivisor U}
    (hP : Function.Injective P) {W : Divisor U} (hW : 0 ≤ W) :
    0 ≤ W - ∑ i, (W (P i)).toNat • (Finsupp.single (P i) 1 : Divisor U) ∧
      ∀ i, (W - ∑ i, (W (P i)).toNat • (Finsupp.single (P i) 1 : Divisor U)) (P i) = 0 := by
  classical
  set S : Divisor U := ∑ i, (W (P i)).toNat • (Finsupp.single (P i) 1 : Divisor U) with hS
  have hScoeff : ∀ i, S (P i) = W (P i) := by
    intro i
    simp only [hS, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply]
    rw [Finset.sum_eq_single i]
    · simp only [ite_true, nsmul_eq_mul, mul_one]
      exact Int.toNat_of_nonneg (hW (P i))
    · intro b _ hb
      simp [hP.ne hb]
    · exact fun h => absurd (Finset.mem_univ i) h
  have hScoeff' : ∀ E, (∀ i, P i ≠ E) → S E = 0 := by
    intro E hE
    simp only [hS, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply]
    exact Finset.sum_eq_zero fun i _ => by simp [hE i]
  refine ⟨fun E => ?_, fun i => by rw [Finsupp.sub_apply, hScoeff i, sub_self]⟩
  change 0 ≤ (W - S) E
  rw [Finsupp.sub_apply]
  by_cases hE : ∃ i, P i = E
  · obtain ⟨i, rfl⟩ := hE
    rw [hScoeff i, sub_self]
  · push Not at hE
    rw [hScoeff' E hE, sub_zero]
    exact hW E

/-- If an effective divisor `W` is negative on a curve `C` with generic point that of `P j`, then
so is its part `∑ᵢ W(Pᵢ) Pᵢ` along distinct prime divisors `Pᵢ`. -/
theorem sum_toNat_mul_degreeOn_single_neg (hsm : IsSmoothScheme sU) {m : ℕ}
    {P : Fin m → Mori.PrimeDivisor U} (hP : Function.Injective P) {W : Divisor U} (hW : 0 ≤ W)
    (C : ProperCurve sU) (j : Fin m) (hC : C.point = (P j).genericPoint)
    (hWC : W.degreeOn k sU C.ι C.dim_le (isCartier_of_isSmoothScheme hsm W) < 0) :
    ∑ i, ((W (P i)).toNat : ℤ) * Divisor.degreeOn k sU C.ι C.dim_le
      (Finsupp.single (P i) 1) (isCartier_of_isSmoothScheme hsm _) < 0 := by
  classical
  set S : Divisor U := ∑ i, (W (P i)).toNat • (Finsupp.single (P i) 1 : Divisor U) with hS
  have ⟨h₀, hP₀⟩ : 0 ≤ W - S ∧ ∀ i, (W - S) (P i) = 0 :=
    sub_sum_single_nonneg_and_apply_eq_zero hP hW
  have h₁ : W.degreeOn k sU C.ι C.dim_le (isCartier_of_isSmoothScheme hsm W) =
      S.degreeOn k sU C.ι C.dim_le (isCartier_of_isSmoothScheme hsm S) +
        (W - S).degreeOn k sU C.ι C.dim_le (isCartier_of_isSmoothScheme hsm _) := by
    rw [← Divisor.degreeOn_add k sU C.ι C.dim_le]
    exact Divisor.degreeOn_congr (by abel) _ _
  have h₂ : S.degreeOn k sU C.ι C.dim_le (isCartier_of_isSmoothScheme hsm S) =
      ∑ i, ((W (P i)).toNat : ℤ) * Divisor.degreeOn k sU C.ι C.dim_le
        (Finsupp.single (P i) 1) (isCartier_of_isSmoothScheme hsm _) := by
    rw [hS, degreeOn_finset_sum hsm]
    exact Finset.sum_congr rfl fun i _ => Divisor.degreeOn_nsmul' k sU C.ι C.dim_le _ _ _
  have h₃ := degreeOn_nonneg_of_coeff_eq_zero hsm (W - S) h₀ C (P j) hC (hP₀ j)
  rw [h₁, h₂] at hWC
  linarith

end Smooth

/-! ### Pull-back of an effective Cartier divisor -/

/-- An effective Cartier divisor `IY` has, near every point, a local equation `g` on an open `W`
whose germs generate the stalks of `IY` on `W`. -/
theorem exists_stalk_eq_span_germ_of_isEffectiveCartierDivisor (IY : Y.IdealSheafData)
    (hIY : Stacks.Divisors.IsEffectiveCartierDivisor IY) (y : Y) :
    ∃ W : Y.Opens, y ∈ W ∧ ∃ g : Γ(Y, W), ∀ z (hz : z ∈ W),
      IdealSheafData.stalk IY z = Ideal.span {(Y.presheaf.germ W z hz).hom g} := by
  obtain ⟨W, hW, hyW, g, -, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor IY hIY y
  refine ⟨W, hyW, g, fun z hz => ?_⟩
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ IY z ⟨W, hW⟩ hz, hspan,
    Ideal.map_span, Set.image_singleton]

/-- A germ generating the stalk of `IY` at `z` is a unit iff `z` is off the support of `IY`. -/
theorem isUnit_germ_iff_notMem_support {IY : Y.IdealSheafData} {W : Y.Opens} {g : Γ(Y, W)}
    {z : Y} (hz : z ∈ W)
    (h : IdealSheafData.stalk IY z = Ideal.span {(Y.presheaf.germ W z hz).hom g}) :
    IsUnit ((Y.presheaf.germ W z hz).hom g) ↔ z ∉ IY.support := by
  rw [← Ideal.span_singleton_eq_top, ← h,
    AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support]

/-- **The pull-back of an effective Cartier divisor.** If `IY` is an effective Cartier divisor
on `Y` avoiding `f(η_X)`, there is an effective divisor `G` on `X`, locally principal over the
opens of a cover of `Y`, with `G E ≥ 1` for every prime divisor `E` with `f(η_E) ∈ Supp IY`. -/
theorem exists_divisor_pullback_of_isEffectiveCartierDivisor [CompactSpace X] [IsIntegral X]
    [IsIntegral Y]
    (f : X ⟶ Y) (IY : Y.IdealSheafData) (hIY : Stacks.Divisors.IsEffectiveCartierDivisor IY)
    (hy₀ : f (genericPoint X) ∉ IY.support) :
    ∃ G : Divisor X, 0 ≤ G ∧
      (∀ E : Mori.PrimeDivisor X, f E.genericPoint ∈ IY.support → 1 ≤ G E) ∧
      ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ ψ : (RationalFunctions X)ˣ,
        G.IsLocalEquation (f ⁻¹ᵁ V) ψ := by
  classical
  have hcomp : ∀ Z : irreducibleComponents X, componentGenericPoint X Z = genericPoint X := by
    intro Z
    have hZ : Z.1 = Set.univ := Set.eq_univ_of_univ_subset
      (Z.2.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _))
    have h₁ := isGenericPoint_componentGenericPoint X Z
    rw [hZ] at h₁
    exact h₁.eq (genericPoint_spec X)
  choose W hyW g hgerm using exists_stalk_eq_span_germ_of_isEffectiveCartierDivisor IY hIY
  let U : Y → X.Opens := fun y => f ⁻¹ᵁ W y
  let a : ∀ y, Γ(X, U y) := fun y => (f.app (W y)).hom (g y)
  have hga : ∀ y x (hx : x ∈ U y), (X.presheaf.germ (U y) x hx).hom (a y) =
      (f.stalkMap x).hom ((Y.presheaf.germ (W y) (f x) hx).hom (g y)) := fun y x hx =>
    (Scheme.Hom.germ_stalkMap_apply f (W y) x hx (g y)).symm
  have ha : ∀ y (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U y),
      (X.presheaf.germ (U y) _ hZ).hom (a y) ≠ 0 := by
    intro y Z hZ
    rw [hga]
    have hu := (isUnit_germ_iff_notMem_support _ (hgerm y _ hZ)).2 (by rwa [hcomp Z])
    exact (hu.map (f.stalkMap _).hom).ne_zero
  have hcompat : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      Associated ((X.presheaf.germ (U i) x hi).hom (a i))
        ((X.presheaf.germ (U j) x hj).hom (a j)) := by
    intro i j x hi hj
    rw [hga, hga]
    exact (Ideal.span_singleton_eq_span_singleton.1
      ((hgerm i _ hi).symm.trans (hgerm j _ hj))).map (f.stalkMap x).hom
  have hxU : ∀ x : X, x ∈ U (f x) := fun x => hyW (f x)
  obtain ⟨G, hG⟩ := exists_divisor_isLocalEquation_sectionUnit U
    (fun x => ⟨f x, hxU x⟩) a ha hcompat
  have hGcoeff : ∀ E : Mori.PrimeDivisor X, G E =
      E.ord (sectionUnit (a (f E.genericPoint)) (ha _)) := fun E =>
    hG (f E.genericPoint) E ⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl, hxU _⟩
  refine ⟨G, fun E => ?_, fun E hE => ?_, fun y => ⟨W y, hyW y, _, hG y⟩⟩
  · change 0 ≤ G E
    rw [hGcoeff]
    exact ord_sectionUnit_nonneg _ _ E (hxU _)
  · rw [hGcoeff]
    refine one_le_ord_sectionUnit _ _ E (hxU _) ?_
    rw [hga (f E.genericPoint) E.genericPoint (hxU _)]
    intro hu
    exact (isUnit_germ_iff_notMem_support _ (hgerm _ _ (hyW _))).1
      (isUnit_of_map_unit (f.stalkMap _).hom _ hu) hE

/-- Local equations of `G` over the preimages of a cover of `Y` give local equations of
`-(N • G)` over the same opens. -/
theorem exists_isLocalEquation_neg_zsmul_preimage {f : X ⟶ Y} {G : Divisor X} (N : ℤ)
    (hG : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ ψ : (RationalFunctions X)ˣ,
      G.IsLocalEquation (f ⁻¹ᵁ V) ψ) (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧ ∃ ψ : (RationalFunctions X)ˣ,
      (-(N • G)).IsLocalEquation (f ⁻¹ᵁ V) ψ := by
  obtain ⟨V, hyV, ψ, hψ⟩ := hG y
  refine ⟨V, hyV, ψ ^ (-N), fun E hE => ?_⟩
  rw [PrimeDivisor.ord_zpow]
  change -(N • G) E = _
  rw [Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
  change -(N * G.coeff E) = _
  rw [hψ E hE]
  ring

/-! ### The geometric input -/

omit [QuasiCompact sX] in
/-- **An effective Cartier divisor `W` with `-W` relatively ample** (Kollár 2.9). Under the
hypotheses of Kollár 2.12 there is an effective divisor `W` on `X` (Cartier, `X` being smooth)
such that `-W` is `f`-ample. As in the source, `W = N f^*D - H` for an effective ample `H` on
the quasi-projective `X` (the divisor of a section of a power of an ample sheaf) and an effective
Cartier divisor `D` on `Y` with `f(Supp H) ⊆ Supp D` and `f(η_X) ∉ Supp D` (generic finiteness);
`f^*D` is principal over the opens of `Y` where `D` is, so `-W = H - N f^*D` is `f`-ample.
Normality of `Y` is not used. -/
theorem exists_isRelativelyAmple_neg_of_isProjectiveMorphism [CompactSpace X]
    (hX : Mori.IsVariety k sX) (hsm : IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)
    (hY : Mori.IsVariety k sY) (hYqp : Stacks.HProjective.IsHQuasiProjective sY)
    {f : X ⟶ Y} (hfs : f ≫ sY = sX) (hproj : IsProjectiveMorphism f)
    (hgf : ∃ V : Y.Opens, ((V : Set Y) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V)) :
    ∃ W : Divisor X, 0 ≤ W ∧ (-W).IsRelativelyAmple f (isCartier_of_isSmoothScheme hsm _) := by
  classical
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  obtain ⟨-, M, hMinv, hMamp⟩ :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sY hYqp
  have hM : Stacks.Ample.IsAmple Y M :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sY M hMamp
  obtain ⟨L, hLinv, hL⟩ := AlgebraicGeometry.exists_isAmple_of_isQuasiProjective f M hM
    (AlgebraicGeometry.isQuasiProjective_of_isHQuasiProjective f hproj.isHQuasiProjective)
  obtain ⟨IX, hIX, -, hηIX, n, hn, ⟨eX⟩⟩ :=
    exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨H, hH0, hHc, ⟨eH⟩, hHsupp⟩ := exists_divisor_of_isEffectiveCartierDivisor IX hIX
  have := hHc.isInvertibleModule_divisorialSheaf
  have hHf : H.IsRelativelyAmple f hHc := isRelativelyAmple_of_isAmple_divisorialSheaf f hHc
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL))
  have hy₀ : f (genericPoint X) ∉ f.base '' (IX.support : Set X) := by
    rintro ⟨x, hx, hfx⟩
    rw [eq_genericPoint_of_map_eq hgf hfx] at hx
    exact hηIX hx
  obtain ⟨IY, hIY, hTIY, hy₀IY, -⟩ :=
    exists_isEffectiveCartierDivisor_of_isAmple M hM (f.isClosedMap _ IX.support.isClosed) hy₀
  obtain ⟨G, hG0, hGH, hGloc⟩ := exists_divisor_pullback_of_isEffectiveCartierDivisor f IY hIY hy₀IY
  set N : ℤ := ∑ E ∈ H.support, H E
  have hHN : ∀ E, H E ≤ N := by
    intro E
    by_cases hE : E ∈ H.support
    · exact Finset.single_le_sum (fun i _ => hH0 i) hE
    · rw [Finsupp.notMem_support_iff.1 hE]
      exact Finset.sum_nonneg fun i _ => hH0 i
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => hH0 i
  refine ⟨N • G - H, fun E => ?_, ?_⟩
  · change 0 ≤ (N • G - H) E
    rw [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
    have hGE : 0 ≤ G E := hG0 E
    have hHE : 0 ≤ H E := hH0 E
    by_cases hE : 0 < H E
    · nlinarith [hHN E, hGH E (hTIY ⟨E.genericPoint, hHsupp E hE, rfl⟩)]
    · nlinarith [hHN E]
  · have hrel := isRelativelyAmple_add_of_isLocalEquation_preimage f hHc hHf
      (isCartier_of_isSmoothScheme hsm _) (exists_isLocalEquation_neg_zsmul_preimage N hGloc)
    have key : ∀ (D : Divisor X) (hD : D.IsCartier), D = H + -(N • G) →
        D.IsRelativelyAmple f hD := by
      rintro D hD rfl
      exact hrel
    exact key _ _ (by abel)

/-- **An effective divisor negative on every exceptional curve** (Kollár 2.9 with 2.10). Under
the hypotheses of Kollár 2.12 there is an effective divisor `W` on `X` with `(W · C) < 0` for
every `f`-exceptional curve `C`. -/
theorem exists_degreeOn_neg_of_isContractedProjectiveCurve
    (hX : Mori.IsVariety k sX) (hsm : IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)
    (hY : Mori.IsVariety k sY) (hYqp : Stacks.HProjective.IsHQuasiProjective sY)
    {f : X ⟶ Y} (hfs : f ≫ sY = sX) (hproj : IsProjectiveMorphism f)
    (hgf : ∃ V : Y.Opens, ((V : Set Y) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V)) :
    ∃ W : Divisor X, 0 ≤ W ∧ ∀ C : ProperCurve sX,
      MMP.Resolution.IsContractedProjectiveCurve sX f C →
        W.degreeOn k sX C.ι C.dim_le (isCartier_of_isSmoothScheme hsm W) < 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨W, hW0, hamp⟩ :=
    exists_isRelativelyAmple_neg_of_isProjectiveMorphism hX hsm hdim hY hYqp hfs hproj hgf
  refine ⟨W, hW0, fun C hC => ?_⟩
  have hneg := isCartier_of_isSmoothScheme hsm (-W)
  have := hneg.isInvertibleModule_divisorialSheaf
  have hpos : 0 < (-W).degreeOn k sX C.ι C.dim_le hneg :=
    degreeOn_pos_of_isRelativelyAmple hX f _ hamp C hC.2
  have hsum := Divisor.degreeOn_add k sX C.ι C.dim_le W (-W)
    (isCartier_of_isSmoothScheme hsm W) hneg
  have h0 : (W + -W).degreeOn k sX C.ι C.dim_le
      ((isCartier_of_isSmoothScheme hsm W).add hneg) = 0 := by
    rw [Divisor.degreeOn_congr (add_neg_cancel W) _ Divisor.isCartier_zero]
    exact Divisor.degreeOn_zero' k sX C.ι C.dim_le
  linarith

/-- **Kollár 2.12 ("Hodge index theorem").** Let `f : X → Y` be a projective and generically
finite morphism of `k`-varieties, `Y` quasi-projective and `X` a smooth surface, and let
`C₁, …, Cₘ` be distinct `f`-exceptional curves. Then the real symmetric matrix `((Cᵢ · Cⱼ))` is
negative definite. -/
@[mmp "thm_kr2a_negative_definite_exceptional_curves"]
theorem posDef_neg_intersectionMatrix_of_isContractedProjectiveCurve
    (hX : Mori.IsVariety k sX) (hsm : IsSmoothScheme sX) (hdim : topologicalKrullDim X = 2)
    (hY : Mori.IsVariety k sY) (hYqp : Stacks.HProjective.IsHQuasiProjective sY)
    {f : X ⟶ Y} (hfs : f ≫ sY = sX) (hproj : IsProjectiveMorphism f)
    (hgf : ∃ V : Y.Opens, ((V : Set Y) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V))
    {m : ℕ} (P : Fin m → Mori.PrimeDivisor X) (hP : Function.Injective P)
    (C : Fin m → ProperCurve sX) (hC : ∀ i, (C i).point = (P i).genericPoint)
    (hexc : ∀ i, MMP.Resolution.IsContractedProjectiveCurve sX f (C i)) :
    (-(Matrix.of fun i j : Fin m =>
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sX (C j).ι
        (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (P i)) :
          ℝ))).PosDef := by
  classical
  obtain ⟨W, hW0, hWneg⟩ :=
    exists_degreeOn_neg_of_isContractedProjectiveCurve hX hsm hdim hY hYqp hfs hproj hgf
  set A : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j : Fin m =>
    ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sX (C j).ι
      (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (P i)) : ℝ)
    with hA
  have hne : ∀ i j, i ≠ j → (C j).point ∉ (P i).support := by
    intro i j hij hmem
    rw [hC j] at hmem
    exact hij (hP (primeDivisor_eq_of_genericPoint_mem_support (P i) (P j) hmem))
  have hentry : ∀ i j, A i j = (Divisor.degreeOn k sX (C j).ι (C j).dim_le
      (Finsupp.single (P i) 1) (isCartier_of_isSmoothScheme hsm _) : ℝ) := by
    intro i j
    simp only [hA, Matrix.of_apply]
    rw [QDivisor.intersectionNumber_toQDivisor k sX (C j).ι (C j).dim_le _
      (isCartier_of_isSmoothScheme hsm _)]
    push_cast
    rfl
  set a : Fin m → ℕ := fun i => (W (P i)).toNat
  refine MMP.MatrixPosDef.posDef_neg_of_offDiag_nonneg_of_sum_mul_neg A ?_ ?_ (fun i => (a i : ℝ))
    (fun i => Nat.cast_nonneg _) ?_
  · intro i j
    simp only [hA, Matrix.of_apply]
    exact congrArg (fun q : ℚ => (q : ℝ))
      (intersectionNumber_single_comm hsm (P j) (P i) (C j) (C i) (hC j) (hC i))
  · intro i j hij
    simp only [hA, Matrix.of_apply]
    exact_mod_cast intersectionNumber_single_nonneg hsm (P i) (C j) (hne i j hij)
  · intro j
    have h₅ : ∑ i, (a i : ℝ) * A i j = ((∑ i, (a i : ℤ) * Divisor.degreeOn k sX (C j).ι
        (C j).dim_le (Finsupp.single (P i) 1) (isCartier_of_isSmoothScheme hsm _) : ℤ) :
          ℝ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [hentry i j]
    rw [h₅]
    exact_mod_cast sum_toNat_mul_degreeOn_single_neg hsm hP hW0 (C j) j (hC j)
      (hWneg (C j) (hexc j))

end MMP.Threefold.Resolution
