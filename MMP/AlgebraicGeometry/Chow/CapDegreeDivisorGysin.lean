module

public import MMP.AlgebraicGeometry.Chow.CycleClassDegree
public import MMP.AlgebraicGeometry.Chow.RationalCycleClass
public import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.Divisor
public import MMP.AlgebraicGeometry.CycleMap.Stacks.Pushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassCommute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveOverAmpleBase

/-!
# Degrees of iterated first Chern class caps, cycle classes and the Gysin map of a divisor

Let `X` be a complex scheme proper over `ℂ`, with Stacks' Chow groups over
`Stacks.Chow.fieldChowSituation ℂ`, and `deg(c₁(L₁) ∩ ⋯ ∩ c₁(L_d) ∩ a)` the degree of an
iterated first Chern class cap (`AlgebraicGeometry.capDegree`). This file proves the following
facts about these degrees:

* on a scheme carrying an ample invertible module, a class `a` with `cl(a) = 0` in Borel–Moore
  homology has `deg(c₁(L₁) ⋯ c₁(L_d) ∩ a) = 0` for every family of invertible modules
  (Fulton 19.2 for line bundles, then §19.1);
* the degree on the fundamental class `[X]_d` is the intersection number `(L₁ ⋯ L_d)` (Stacks
  0BFI);
* on a smooth projective threefold, `cl(c₁(𝒪(A)) ∩ [W]) = [S]` for a Cartier divisor `A` with Weil
  divisor a prime divisor `S` (the Cartier divisor dictionary).

## Main results

* `MMP.Chow.capDegree_eq_zero_of_chowCycleClass_eq_zero_of_isAmple`
* `MMP.Chow.capDegree_fundamentalChowClass_eq_intersectionNumber`
* `MMP.Chow.chowCycleClass_firstChernClassCapChow_fundamentalChowClass`
* `MMP.Chow.exists_isAmple_of_isProjective`

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, Proposition 19.2.
* [Stacks Project, Tag 0BFI](https://stacks.math.columbia.edu/tag/0BFI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set
open MMP.UnderlyingSpace

namespace MMP.Chow

open MMP MMP.Modules MMP.Analytic Stacks.Chow Stacks.Ample

/-! ### Ample modules -/

/-- The structure sheaf of `Spec ℂ` is an ample invertible module. -/
private theorem exists_isAmple_spec :
    ∃ (M : (Spec (.of ℂ)).Modules) (hM : Stacks.Ample.IsInvertibleModule (Spec (.of ℂ)) M),
      letI : Stacks.Ample.IsInvertibleModule (Spec (.of ℂ)) M := hM
      Stacks.Ample.IsAmple (Spec (.of ℂ)) M :=
  ⟨Stacks.Ample.unitModule _, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩

/-- A scheme projective over `ℂ` carries an ample invertible module. -/
theorem exists_isAmple_of_isProjective {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    (hZ : IsProjectiveMorphism sZ) :
    ∃ (L : Z.Modules) (hL : Stacks.Ample.IsInvertibleModule Z L),
      letI : Stacks.Ample.IsInvertibleModule Z L := hL
      Stacks.Ample.IsAmple Z L := by
  have h := (isProjective_tfae_seven_of_exists_isAmple sZ exists_isAmple_spec).out 2 5
  exact (h.mp hZ).2

/-! ### Vanishing of degrees of homologically trivial classes -/

section Vanishing

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [IsProper (X ↘ Spec (.of ℂ))] (A : X.Modules) [IsInvertibleModule X A] (hA : IsAmple X A)

include hA in
/-- On a complex scheme proper over `ℂ` with an ample invertible module, a class `a ∈ A_d(X)` with
`cl(a) = 0` has `deg(c₁(L₁) ∩ ⋯ ∩ c₁(L_d) ∩ a) = 0` for every family of invertible modules: by
Fulton 19.2, `cl(c₁(L) ∩ b) = c₁ᵗᵒᵖ(L) ∩ cl(b)`, so the cycle class stays zero, and a zero-cycle
class with zero cycle class has degree zero. -/
theorem capDegree_eq_zero_of_chowCycleClass_eq_zero_of_isAmple :
    ∀ (d : ℕ) (L : Fin d → X.Modules)
      [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
      (a : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) d),
      chowCycleClass ℚ d a = 0 → capDegree ℂ (X ↘ Spec (.of ℂ)) L a = 0
  | 0, L, _, a, h => by
    rw [capDegree_zero]
    exact chowDegree_eq_zero_of_chowCycleClass_eq_zero a h
  | d + 1, L, hL, a, h => by
    have : IsInvertibleModule X (L (Fin.last d)) := hL (Fin.last d)
    have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L (Fin.last d)) :=
      hL (Fin.last d)
    rw [capDegree_succ]
    refine capDegree_eq_zero_of_chowCycleClass_eq_zero_of_isAmple d _ _ ?_
    rw [← GenuineChern.firstChernClassCapChow_eq_invCap]
    have e := chowCycleClass_firstChernClassCap ℚ (L (Fin.last d)) d A hA a
    dsimp only at e
    exact e.trans (by rw [h, map_zero])

end Vanishing

/-! ### Degrees on fundamental classes -/

/-- **Stacks 0BFI on the fundamental class.** On a scheme `W` proper over `ℂ` of dimension `d`,
`deg(c₁(L₁) ∩ ⋯ ∩ c₁(L_d) ∩ [W]_d)` is the intersection number `(L₁ ⋯ L_d)`. -/
theorem capDegree_fundamentalChowClass_eq_sheafIntersectionNumber {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsProper (W ↘ Spec (.of ℂ))] (d : ℕ)
    (hd : topologicalKrullDim W = d) (L : Fin d → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L j)] :
    capDegree ℂ (W ↘ Spec (.of ℂ)) L
        (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) d) =
      MMP.Mori.sheafIntersectionNumber ℂ (W ↘ Spec (.of ℂ)) (𝟙 W) d hd.le L := by
  rw [MMP.Mori.Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    AlgebraicGeometry.intersectionNumber_eq_chowDegree_iteratedFirstChernCap ℂ _ _ d hd]
  rfl

/-! ### The class of `c₁(𝒪(A)) ∩ [W]` -/

section DivisorClass

variable {W : Scheme.{0}} [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [IsLocallyNoetherian W]
  [IsNormal W]

/-- **The Cartier divisor dictionary on Stacks cycles.** On a smooth projective complex threefold
`W`, for a Cartier divisor `A` whose Weil divisor is a prime divisor `S`,
`cl(c₁(𝒪(A)) ∩ [W]) = [S]` in `H_4(W, ℚ)`. -/
theorem chowCycleClass_firstChernClassCapChow_fundamentalChowClass
    (hW : Mori.IsProjectiveVariety ℂ (W ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = (2 + 1 : ℕ))
    (S : Mori.PrimeDivisor W) (A : W.CartierDivisor)
    (hA : MMP.Intersection.IsWeilDivisorOfCartier A (Finsupp.single S 1)) :
    chowCycleClass ℚ 2 (firstChernClassCapChow (fieldChowSituation ℂ) ((2 : ℕ) : ℤ)
        (W ↘ Spec (.of ℂ)) (MMP.CartierDivisor.sheaf A)
        (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((2 + 1 : ℕ) : ℤ))) =
      divisorClass W (Finsupp.single S 1) := by
  classical
  have hWv := (MMP.Mori.isProjectiveVariety_iff _ _).1 hW
  have : IsIntegral W := hWv.1.toIsIntegral
  obtain ⟨A', hA'i, hA'⟩ := exists_isAmple_of_isProjective (W ↘ Spec (.of ℂ)) hWv.2
  have : IsProper (W ↘ Spec (.of ℂ)) := isProper_of_isProjectiveMorphism _ hWv.2
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (W ↘ Spec (.of ℂ))
  obtain ⟨e⟩ := hA.nonempty_sheaf_iso_divisorialSheaf
  set M : Mori.Divisor W := Finsupp.single S 1 with hM
  have hcM := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm M
  have := hcM.isInvertibleModule_divisorialSheaf
  rw [firstChernClassCapChow_congr (C := fieldChowSituation ℂ) _ _ e]
  have h19 := chowCycleClass_firstChernClassCap ℚ M.divisorialSheaf 2 A' hA'
    (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((2 + 1 : ℕ) : ℤ))
  dsimp only at h19
  rw [h19]
  have hgen : relativeDimension (fieldChowSituation ℂ).dimensionFunction (W ↘ Spec (.of ℂ))
      (_root_.genericPoint W) = ((2 + 1 : ℕ) : ℤ) :=
    relativeDimension_genericPoint_eq ℂ _ hdim
  have hsingle : MMP.Mori.Divisor.toQDivisor M = ((1 : ℕ) : ℤ) • (Finsupp.single S (1 : ℚ)) := by
    rw [Nat.cast_one, one_smul]
    ext E
    change ((Finsupp.single S (1 : ℤ) E : ℤ) : ℚ) = _
    by_cases h : S = E <;> simp [h, Mori.DivisorWithCoeffs.coeff_apply]
  have hd := (MMP.Fourfold.smul_rationalCycleClass_eq_capProductPullback hW hsm hdim
    (Finsupp.single S 1) one_pos M hsingle (_root_.genericPoint W) hgen).1
  rw [Nat.cast_one, one_smul] at hd
  rw [divisorClass, LinearMap.comp_apply]
  refine Eq.trans ?_ hd.symm
  have hfund : chowCycleClass ℚ (2 + 1)
      (fundamentalChowClass (fieldChowSituation ℂ) (W ↘ Spec (.of ℂ)) ((2 + 1 : ℕ) : ℤ)) =
      rationalCycleClass W (2 + 1) (rationalPointCycle (fieldChowSituation ℂ)
        (W ↘ Spec (.of ℂ)) ((2 + 1 : ℕ) : ℤ) (_root_.genericPoint W) hgen) := by
    rw [rationalCycleClass_rationalPointCycle, ← cycleClass_pointCycle]
    refine congrArg (cycleClass ℚ (2 + 1)) (Subtype.ext ?_)
    ext y
    rw [Stacks.Chow.pointCycle_apply]
    by_cases hy : y = _root_.genericPoint W
    · subst hy
      rw [if_pos rfl]
      exact Stacks.Chow.cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint _ _ (𝟙 W)
        _ hgen
    · rw [if_neg hy]
      exact Stacks.Chow.cycleAssociatedToClosedSubscheme_isIntegral_apply_of_ne _ _ (𝟙 W) _ hy
  rw [hfund, borelMooreHomology.capProductPullback_apply, firstChernClassTopCap,
    firstChernClassTop, MMP.Modules.topFirstChernClass_dual ℚ M.divisorialSheaf]
  rfl

end DivisorClass

/-! ### Degrees of iterated caps: isomorphisms and peeling -/

section Peel

variable {W : Scheme.{0}} (q : W ⟶ Spec (.of ℂ)) [IsProper q]

/-- The degree of an iterated cap only depends on the modules up to isomorphism. -/
theorem capDegree_congr_iso : ∀ {d : ℕ} (L M : Fin d → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (M j)]
    (_ : ∀ j, Nonempty (L j ≅ M j)), capDegree ℂ q L = capDegree ℂ q M
  | 0, L, M, _, _, _ => by
    refine AddMonoidHom.ext fun a => ?_
    rw [capDegree_zero, capDegree_zero]
  | d + 1, L, M, hL, hM, e => by
    refine AddMonoidHom.ext fun a => ?_
    have : SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property (L (Fin.last d)) :=
      hL (Fin.last d)
    have : SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property (M (Fin.last d)) :=
      hM (Fin.last d)
    rw [capDegree_succ, capDegree_succ,
      capDegree_congr_iso (fun j => L j.castSucc) (fun j => M j.castSucc) (fun j => e _),
      ← GenuineChern.firstChernClassCapChow_eq_invCap,
      ← GenuineChern.firstChernClassCapChow_eq_invCap,
      firstChernClassCapChow_congr (C := fieldChowSituation ℂ) _ _ (e (Fin.last d)).some]

/-- The family `(K₁, …, K_d, N)` of invertible modules. -/
instance isInvertible_snoc {d : ℕ} (K : Fin d → W.Modules)
    [hK : ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (K j)] (N : W.Modules)
    [hN : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N] :
    ∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      ((Fin.snoc K N : Fin (d + 1) → W.Modules) j) :=
  Fin.lastCases (by simpa using hN) (fun j => by simpa using hK j)

/-- **Peeling off the innermost cap**: `deg(c₁(K₁) ⋯ c₁(K_d) ∩ (c₁(N) ∩ a)) =
deg(c₁(K₁) ⋯ c₁(K_d) c₁(N) ∩ a)`. -/
theorem capDegree_firstChernClassCapChow {d : ℕ} (K : Fin d → W.Modules)
    [∀ j, SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (K j)] (N : W.Modules)
    [hN : SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N]
    (a : chowGroup (fieldChowSituation ℂ) q ((d + 1 : ℕ) : ℤ)) :
    haveI : SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property N := hN
    capDegree ℂ q K (firstChernClassCapChow (fieldChowSituation ℂ) (d : ℤ) q N a) =
      capDegree ℂ q (Fin.snoc K N : Fin (d + 1) → W.Modules) a := by
  have : SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property N := hN
  rw [capDegree_succ ℂ q (Fin.snoc K N : Fin (d + 1) → W.Modules),
    ← GenuineChern.firstChernClassCapChow_eq_invCap]
  have hfam : (fun j : Fin d => (Fin.snoc K N : Fin (d + 1) → W.Modules) j.castSucc) = K :=
    funext fun j => Fin.snoc_castSucc (α := fun _ => W.Modules) _ _ _
  rw [capDegree_congr_family ℂ q hfam,
    firstChernClassCapChow_congr (C := fieldChowSituation ℂ) _ _
      (eqToIso (Fin.snoc_last (α := fun _ => W.Modules) _ _))]
  rfl

end Peel

/-! ### The Gysin map of a divisor -/

section Gysin

attribute [local instance] fibreProductOver isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct

open CategoryTheory.Limits Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] [IsClosedImmersion f]
  [IsComplexScheme X] [IsComplexScheme Y] (hf : IsRegularClosedImmersionOfCodim f 1)

/-- **The Gysin map of a divisor**, `f^! : A_{m+1}(Y) ⟶ A_m(X ×_Y Y)`: the cap product with
Stacks' class `c(X ⟶ Y, 𝒩)` of the normal sheaf (Stacks 0FBK), on the test scheme `𝟙 Y`. -/
def divisorGysin (m : ℕ) :
    chowGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) (m + 1 : ℕ) →+
      chowGroup (fieldChowSituation ℂ) (pullback.fst f (𝟙 Y) ≫ X ↘ Spec (.of ℂ)) m :=
  (chowGroupCongrDegree (fieldChowSituation ℂ) (pullback.fst f (𝟙 Y) ≫ X ↘ Spec (.of ℂ))
      (natCast_add_sub_natCast m 1)).toAddMonoidHom.comp
    (((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
        (comp_over f _) hf).cap (𝟙 Y) ((m + 1 : ℕ) : ℤ)).comp
      (chowGroupCongr (fieldChowSituation ℂ) (q := Y ↘ Spec (.of ℂ))
        (q' := 𝟙 Y ≫ Y ↘ Spec (.of ℂ)) (Category.id_comp _).symm
        ((m + 1 : ℕ) : ℤ)).toAddMonoidHom)

/-- **The class `t_*(c₁(L) ∩ [V])`** in `A_{m+1}(Y)`, for a closed immersion `t : V ⟶ Y` of a
scheme of dimension `m + 2` and an invertible module `L` on `V`. -/
def pushforwardFirstChernCapFundamental {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] (t : V ⟶ Y) [t.IsOver (Spec (.of ℂ))] [IsClosedImmersion t] (m : ℕ)
    (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L] :
    chowGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) ((m + 1 : ℕ) : ℤ) :=
  properChowPushforward (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) t
    (comp_over t _) ((m + 1 : ℕ) : ℤ)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ t (comp_over t _) _)
    (firstChernClassCapChow (fieldChowSituation ℂ) ((m + 1 : ℕ) : ℤ) (V ↘ Spec (.of ℂ)) L
      (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) ((m + 1 + 1 : ℕ) : ℤ)))

omit [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [IsClosedImmersion f] [IsComplexScheme X] [IsComplexScheme Y] in
/-- `Stacks.Chow.chowGroupCongr` commutes with the first Chern class cap. -/
theorem chowGroupCongr_firstChernClassCapChow {T : Scheme.{0}} {q q' : T ⟶ (fieldChowSituation ℂ).S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q') (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L] (k : ℤ)
    (x : chowGroup (fieldChowSituation ℂ) q (k + 1)) :
    chowGroupCongr (fieldChowSituation ℂ) h k
        (firstChernClassCapChow (fieldChowSituation ℂ) k q L x) =
      firstChernClassCapChow (fieldChowSituation ℂ) k q' L
        (chowGroupCongr (fieldChowSituation ℂ) h (k + 1) x) := by
  subst h
  rfl

/-- **The Gysin map on `t_*(c₁(L) ∩ [V])` at vanishing excess.** Let `t : V ⟶ Y` be a closed
complex subvariety of dimension `m + 2` whose intersection `X ×_Y V ⟶ V` with the divisor is again
a divisor, and `L` an invertible module on `V`. Then
`f^!(t_*(c₁(L) ∩ [V])) = t'_*(c₁(L|) ∩ [X ×_Y V])`. -/
theorem divisorGysin_properChowPushforward_of_isRegular {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] [IsIntegral V] (t : V ⟶ Y) [t.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion t] {m : ℕ} (hV : topologicalKrullDim V = (m + 1 + 1 : ℕ))
    (ht : IsRegularClosedImmersionOfCodim (pullback.snd f (t ≫ 𝟙 Y)) 1) (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L] :
    haveI := GenuineChern.isInvertible_pullback (pullback.snd f (t ≫ 𝟙 Y)) L
    haveI := isOver_bivariantBaseChangeMap f (𝟙 Y) t
    haveI : IsProper (bivariantBaseChangeMap f (𝟙 Y) t) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f (𝟙 Y) t)
        (P := @IsProper) inferInstance
    divisorGysin f hf m (properChowPushforward (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
        (Y ↘ Spec (.of ℂ)) t (comp_over t _) ((m + 1 : ℕ) : ℤ)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ t
          (comp_over t _) _)
        (firstChernClassCapChow (fieldChowSituation ℂ) ((m + 1 : ℕ) : ℤ) (V ↘ Spec (.of ℂ)) L
          (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) ((m + 1 + 1 : ℕ) : ℤ)))) =
      properChowPushforward (fieldChowSituation ℂ)
        (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ)) (pullback.fst f (𝟙 Y) ≫ X ↘ Spec (.of ℂ))
        (bivariantBaseChangeMap f (𝟙 Y) t)
        (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) (m : ℤ)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (firstChernClassCapChow (fieldChowSituation ℂ) (m : ℤ)
          (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ))
          ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Y))).obj L)
          (fundamentalChowClass (fieldChowSituation ℂ)
            (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ)) ((m + 1 : ℕ) : ℤ))) := by
  have := GenuineChern.isInvertible_pullback (pullback.snd f (t ≫ 𝟙 Y)) L
  have := isOver_bivariantBaseChangeMap f (𝟙 Y) t
  have : IsProper (bivariantBaseChangeMap f (𝟙 Y) t) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f (𝟙 Y) t)
      (P := @IsProper) inferInstance
  set c := regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
    (comp_over f _) hf
  simp only [divisorGysin, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [chowGroupCongr_properChowPushforward (fieldChowSituation ℂ) t
      (comp_over (t ≫ 𝟙 Y) _).symm (Category.id_comp _).symm (comp_over t _)
      (Category.assoc _ _ _).symm _ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ t _ _),
    c.cap_properPushforward (𝟙 Y) t (bivariantBaseChangeMap f (𝟙 Y) t)
      (isPullback_bivariantBaseChangeMap f (𝟙 Y) t) (bivariantBaseChangeMap_fst f (𝟙 Y) t),
    chowGroupCongrDegree_properChowPushforward _ _ _ _ _ _ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)]
  congr 1
  rw [chowGroupCongr_firstChernClassCapChow]
  have hT := regularNormalGysinClass_cap_fundamentalChowClass_of_isRegular f (t ≫ 𝟙 Y) hf
    (m := m + 1) hV.symm ht
  rw [c.cap_firstChernClassCapChow (t ≫ 𝟙 Y) L
    ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Y))).obj L) (Iso.refl _) ((m + 1 : ℕ) : ℤ) _
    (fundamentalChowClass (fieldChowSituation ℂ) (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ))
      (((m + 1 : ℕ) : ℤ) - 1 + 1))
    ((fundamentalChowClass_heq_of_degree_eq _ (by omega)).trans
      (hT ▸ chowGroupCongrDegree_heq' _ _ _))]
  exact eq_of_heq ((chowGroupCongrDegree_heq' _ _ _).trans
    (GenuineChern.firstChernClassCapChow_heq _ _ (by omega)
      (fundamentalChowClass_heq_of_degree_eq _ (by omega))))

/-- **Degrees against `f^!(t_*(c₁(L) ∩ [V]))` at vanishing excess.** For invertible modules
`K₁, …, K_m` on `X ×_Y Y`,
`deg(c₁(K) ∩ f^!(t_*(c₁(L) ∩ [V]))) = deg(c₁(t'^*K) c₁(L|) ∩ [X ×_Y V])`. -/
theorem capDegree_divisorGysin_of_isRegular [IsProper (X ↘ Spec (.of ℂ))] {V : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V] (t : V ⟶ Y)
    [t.IsOver (Spec (.of ℂ))] [IsClosedImmersion t] {m : ℕ}
    (hV : topologicalKrullDim V = (m + 1 + 1 : ℕ))
    (ht : IsRegularClosedImmersionOfCodim (pullback.snd f (t ≫ 𝟙 Y)) 1) (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L]
    (K : Fin m → (pullback f (𝟙 Y)).Modules)
    [∀ j, SheafOfModules.IsInvertible (pullback f (𝟙 Y)).presheaf
      (pullback f (𝟙 Y)).ringCatSheaf.2 (K j)] :
    haveI := GenuineChern.isInvertible_pullback (pullback.snd f (t ≫ 𝟙 Y)) L
    haveI : ∀ j, SheafOfModules.IsInvertible (pullback f (t ≫ 𝟙 Y)).presheaf
        (pullback f (t ≫ 𝟙 Y)).ringCatSheaf.2
        ((Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Y) t)).obj (K j)) := fun _ =>
      GenuineChern.isInvertible_pullback _ _
    capDegree ℂ (pullback.fst f (𝟙 Y) ≫ X ↘ Spec (.of ℂ)) K
        (divisorGysin f hf m (pushforwardFirstChernCapFundamental t m L)) =
      capDegree ℂ (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ))
        (Fin.snoc (fun j => (Scheme.Modules.pullback (bivariantBaseChangeMap f (𝟙 Y) t)).obj
            (K j)) ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Y))).obj L) :
          Fin (m + 1) → (pullback f (t ≫ 𝟙 Y)).Modules)
        (fundamentalChowClass (fieldChowSituation ℂ)
          (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ)) ((m + 1 : ℕ) : ℤ)) := by
  have := GenuineChern.isInvertible_pullback (pullback.snd f (t ≫ 𝟙 Y)) L
  have := isOver_bivariantBaseChangeMap f (𝟙 Y) t
  have : IsProper (bivariantBaseChangeMap f (𝟙 Y) t) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f (𝟙 Y) t)
      (P := @IsProper) inferInstance
  rw [pushforwardFirstChernCapFundamental,
    divisorGysin_properChowPushforward_of_isRegular f hf t hV ht L,
    ← capDegree_properChowPushforward]
  exact capDegree_firstChernClassCapChow _ _ _ _

/-- **Stacks 0FBM at full excess** for `c(X ⟶ Y, 𝒩)`: if `j : V ⟶ Y` factors through the divisor
(`X ×_Y V ⟶ V` an isomorphism), `f^![V]_{m+1} = e_*(c₁(π^*𝒩) ∩ [V])`, for the factorization
`π : V ⟶ X` and the isomorphism `e : V ≅ X ×_Y V`. -/
theorem exists_regularNormalGysinClass_cap_fundamentalChowClass_of_isIso {V : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V]
    (j : V ⟶ Y) [j.IsOver (Spec (.of ℂ))] [LocallyOfFiniteType j] {m : ℕ}
    (hV : ((m + 1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V) [IsIso (pullback.snd f j)] :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
    haveI := hf.isFiniteLocallyFreeOfRank_conormalModule
    haveI : Stacks.Ample.IsInvertibleModule X (dualSheaf (conormalModule f)) :=
      GenuineChern.isInvertible_of_rank_one _
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property
        ((Scheme.Modules.pullback (inv (pullback.snd f j) ≫ pullback.fst f j)).obj
          (dualSheaf (conormalModule f))) :=
      GenuineChern.isInvertible_pullback _ _
    ∃ (e : V ≅ pullback f j) (heS : e.hom ≫ (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) =
        V ↘ Spec (.of ℂ)), e.hom ≫ pullback.snd f j = 𝟙 V ∧
      chowGroupCongrDegree (fieldChowSituation ℂ) (pullback.fst f j ≫ X ↘ Spec (.of ℂ))
          (natCast_add_sub_natCast m 1)
          ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
              f (comp_over f _) hf).cap j ((m + 1 : ℕ) : ℤ)
            (chowGroupCongr (fieldChowSituation ℂ) (q := V ↘ Spec (.of ℂ))
              (q' := j ≫ Y ↘ Spec (.of ℂ)) (comp_over j _).symm ((m + 1 : ℕ) : ℤ)
              (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ)))) =
        chowPushforwardOfIso (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
          (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) e.hom heS (m : ℤ)
          (firstChernClassCapChow (fieldChowSituation ℂ) (m : ℤ) (V ↘ Spec (.of ℂ))
            ((Scheme.Modules.pullback (inv (pullback.snd f j) ≫ pullback.fst f j)).obj
              (dualSheaf (conormalModule f)))
            (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ))) := by
  have hD := isEffectiveCartierDivisor_ker_of_isRegularClosedImmersionOfCodim_one f hf
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of ℂ))
  have := hf.isFiniteLocallyFreeOfRank_conormalModule
  let π : V ⟶ X := inv (pullback.snd f j) ≫ pullback.fst f j
  have hπ : π ≫ f = j := by
    simp only [π, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  have : π.IsOver (Spec (.of ℂ)) := ⟨by
    change inv (pullback.snd f j) ≫ (pullback f j ↘ Spec (.of ℂ)) = _
    rw [← comp_over (pullback.snd f j) (Spec (.of ℂ)), IsIso.inv_hom_id_assoc]⟩
  have sq : IsPullback (𝟙 V) π j f :=
    (IsPullback.of_iso_pullback (show CommSq π (𝟙 V) f j from ⟨by rw [hπ, Category.id_comp]⟩)
      (asIso (inv (pullback.snd f j))) rfl (by simp)).flip
  let e : V ⟶ pullback f j := sq.flip.isoPullback.hom
  have he₂ : e ≫ pullback.snd f j = 𝟙 V := by simp [e]
  have heS : e ≫ (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) = V ↘ Spec (.of ℂ) :=
    isoPullback_hom_comp_structureMorphism (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
      (Y ↘ Spec (.of ℂ)) sq (comp_over f _) (V ↘ Spec (.of ℂ))
      (by rw [Category.id_comp, comp_over])
  have : e.IsOver (Spec (.of ℂ)) := ⟨heS⟩
  have hNX : Stacks.Ample.IsInvertibleModule X (dualSheaf (conormalModule f)) :=
    GenuineChern.isInvertible_of_rank_one _
  let N : V.Modules := (Scheme.Modules.pullback π).obj (dualSheaf (conormalModule f))
  have hdim : schemeDeltaDimension (fieldChowSituation ℂ) (j ≫ Y ↘ Spec (.of ℂ)) ≤
      (((m + 1 : ℕ) : ℤ) : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_genericPoint_eq ℂ _ hV.symm]
  set 𝒩 := VirtualNormalBundle.ofIsRegularImmersion f hf.isRegularImmersion with h𝒩
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} 𝒩.bundle (0 + 1) :=
    (inferInstance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0}
      𝒩.bundle 1)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0}
      (conormalModule (𝟙 V)) 0 :=
    Stacks.Chow.isFiniteLocallyFreeOfRank_zero_of_isZero
      (Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso (𝟙 V))
  have hreg' : IsRegularImmersion (𝟙 V) :=
    Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth (𝟙 V) (𝟙 V)
  have hcap := virtualNormalBundleClass_cap_fundamentalChowClass_excess (fieldChowSituation ℂ)
    (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f (comp_over f _) 𝒩 0 1
    (c := regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
      f (comp_over f _) hf)
    (isVirtualNormalBundleClass_virtualNormalBundleClass (fieldChowSituation ℂ) _ _ f _ 𝒩 (0 + 1))
    j (𝟙 V) π sq (V ↘ Spec (.of ℂ)) (by rw [Category.id_comp, comp_over]) hreg' _ hdim
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0}
      (𝒩.baseChange f (𝟙 V) π j sq).bundle (0 + 1) :=
    isFiniteLocallyFreeOfRank_modulePullback π 𝒩.bundle (0 + 1) inferInstance
  have := (𝒩.baseChange f (𝟙 V) π j sq).isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add 0 1
  have hchow : chowGroupCongrDegree (fieldChowSituation ℂ) (pullback.fst f j ≫ X ↘ Spec (.of ℂ))
      (natCast_add_sub_natCast m 1)
      ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
          (comp_over f _) hf).cap j ((m + 1 : ℕ) : ℤ)
        (chowGroupCongr (fieldChowSituation ℂ) (q := V ↘ Spec (.of ℂ))
          (q' := j ≫ Y ↘ Spec (.of ℂ)) (comp_over j _).symm ((m + 1 : ℕ) : ℤ)
          (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ)))) =
      chowPushforwardOfIso (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
        (pullback.fst f j ≫ X ↘ Spec (.of ℂ)) e heS (m : ℤ)
        (firstChernClassCapChow (fieldChowSituation ℂ) (m : ℤ) (V ↘ Spec (.of ℂ)) N
          (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) (m + 1 : ℕ))) := by
    rw [chowGroupCongr_fundamentalChowClass, hcap,
      GenuineChern.chernCap_congr (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) 1
        (excessNormalSheafIsoOfIdentity f hf.isRegularImmersion π j sq)]
    refine eq_of_heq ((chowGroupCongrDegree_heq' _ _ _).trans
      (chowPushforwardOfIso_heq_congr_base (fieldChowSituation ℂ) _ _ rfl _ _ rfl rfl
        (by push_cast; ring) _ _ ?_))
    refine (chowGroupDegreeEquiv_heq (fieldChowSituation ℂ) _ _ _).trans ?_
    rw [show (Fin.last 1 : Fin (1 + 1)) = 1 from rfl, GenuineChern.chernCap_one_eq_invCap,
      ← GenuineChern.firstChernClassCapChow_eq_invCap]
    have hNinv : AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj
        V.ringCatSheaf.property N := GenuineChern.isInvertible_of_rank_one _
    refine GenuineChern.firstChernClassCapChow_heq (C := fieldChowSituation ℂ)
      (V ↘ Spec (.of ℂ)) N (d₁ := ((m + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - 1) (d₂ := (m : ℤ)) ?_ ?_
    · push_cast; ring
    · exact (chowGroupCast_heq' _ _ _).trans
        (fundamentalChowClass_heq_of_degree_eq _ (by push_cast; ring))
  exact ⟨sq.flip.isoPullback, heS, he₂, hchow⟩

/-- **The Gysin map commutes with proper push-forward** (Stacks 0B76 (1)):
`f^!(t_* β) = t'_*(f^!_t β)`, with `f^!_t` the cap product on the test scheme `t : V ⟶ Y`. -/
theorem divisorGysin_properChowPushforward {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [IsComplexScheme V] (t : V ⟶ Y) [t.IsOver (Spec (.of ℂ))] [IsClosedImmersion t] {m : ℕ}
    (β : chowGroup (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) ((m + 1 : ℕ) : ℤ)) :
    haveI := isOver_bivariantBaseChangeMap f (𝟙 Y) t
    haveI : IsProper (bivariantBaseChangeMap f (𝟙 Y) t) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f (𝟙 Y) t)
        (P := @IsProper) inferInstance
    divisorGysin f hf m (properChowPushforward (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
        (Y ↘ Spec (.of ℂ)) t (comp_over t _) ((m + 1 : ℕ) : ℤ)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ t
          (comp_over t _) _) β) =
      properChowPushforward (fieldChowSituation ℂ)
        (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ)) (pullback.fst f (𝟙 Y) ≫ X ↘ Spec (.of ℂ))
        (bivariantBaseChangeMap f (𝟙 Y) t)
        (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) (m : ℤ)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (chowGroupCongrDegree (fieldChowSituation ℂ) (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ))
          (natCast_add_sub_natCast m 1)
          ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
              f (comp_over f _) hf).cap (t ≫ 𝟙 Y) ((m + 1 : ℕ) : ℤ)
            (chowGroupCongr (fieldChowSituation ℂ) (q := V ↘ Spec (.of ℂ))
              (q' := (t ≫ 𝟙 Y) ≫ Y ↘ Spec (.of ℂ)) (comp_over (t ≫ 𝟙 Y) _).symm
              ((m + 1 : ℕ) : ℤ) β))) := by
  have := isOver_bivariantBaseChangeMap f (𝟙 Y) t
  have : IsProper (bivariantBaseChangeMap f (𝟙 Y) t) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f (𝟙 Y) t)
      (P := @IsProper) inferInstance
  simp only [divisorGysin, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [chowGroupCongr_properChowPushforward (fieldChowSituation ℂ) t
      (comp_over (t ≫ 𝟙 Y) _).symm (Category.id_comp _).symm (comp_over t _)
      (Category.assoc _ _ _).symm _ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ t _ _),
    (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
      (comp_over f _) hf).cap_properPushforward (𝟙 Y) t (bivariantBaseChangeMap f (𝟙 Y) t)
      (isPullback_bivariantBaseChangeMap f (𝟙 Y) t) (bivariantBaseChangeMap_fst f (𝟙 Y) t),
    chowGroupCongrDegree_properChowPushforward _ _ _ _ _ _ _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)]

/-- The factorization `π : V ⟶ X` of `t : V ⟶ Y` through the divisor, when `X ×_Y V ⟶ V` is an
isomorphism. -/
abbrev divisorFactor {V : Scheme.{0}} (t : V ⟶ Y) [IsIso (pullback.snd f (t ≫ 𝟙 Y))] : V ⟶ X :=
  inv (pullback.snd f (t ≫ 𝟙 Y)) ≫ pullback.fst f (t ≫ 𝟙 Y)

omit [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [IsClosedImmersion f] [IsComplexScheme X] [IsComplexScheme Y] in
/-- The factorization `divisorFactor f t : V ⟶ X` composed with `f` is `t ≫ 𝟙 Y`. -/
theorem divisorFactor_comp {V : Scheme.{0}} (t : V ⟶ Y) [IsIso (pullback.snd f (t ≫ 𝟙 Y))] :
    divisorFactor f t ≫ f = t ≫ 𝟙 Y := by
  simp only [divisorFactor, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- **Degrees against `f^!(t_*(c₁(L) ∩ [V]))` at full excess.** If `t : V ⟶ Y` factors through
the divisor as `π`, with `v = (π, t) : V ⟶ X ×_Y Y`, then for invertible modules `K₁, …, K_m` on
`X ×_Y Y`: `deg(c₁(K) ∩ f^!(t_*(c₁(L) ∩ [V]))) = deg(c₁(v^*K) c₁(L) c₁(π^*𝒩) ∩ [V])`, with
`𝒩 = 𝒞_{X/Y}^∨` the normal sheaf. -/
theorem capDegree_divisorGysin_of_isIso [IsProper (X ↘ Spec (.of ℂ))] {V : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsProper (V ↘ Spec (.of ℂ))] [IsIntegral V]
    (t : V ⟶ Y) [t.IsOver (Spec (.of ℂ))] [IsClosedImmersion t] [IsIso (pullback.snd f (t ≫ 𝟙 Y))]
    {m : ℕ}
    (hV : topologicalKrullDim V = (m + 1 + 1 : ℕ)) (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L]
    (K : Fin m → (pullback f (𝟙 Y)).Modules)
    [∀ j, SheafOfModules.IsInvertible (pullback f (𝟙 Y)).presheaf
      (pullback f (𝟙 Y)).ringCatSheaf.2 (K j)]
    [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((Scheme.Modules.pullback (divisorFactor f t)).obj (dualSheaf (conormalModule f)))]
    [∀ j, SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.lift (divisorFactor f t) t
        (divisorFactor_comp f t))).obj (K j))] :
    capDegree ℂ (pullback.fst f (𝟙 Y) ≫ X ↘ Spec (.of ℂ)) K
        (divisorGysin f hf m (properChowPushforward (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
          (Y ↘ Spec (.of ℂ)) t (comp_over t _) ((m + 1 : ℕ) : ℤ)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ t
            (comp_over t _) _)
          (firstChernClassCapChow (fieldChowSituation ℂ) ((m + 1 : ℕ) : ℤ) (V ↘ Spec (.of ℂ)) L
            (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
              ((m + 1 + 1 : ℕ) : ℤ))))) =
      capDegree ℂ (V ↘ Spec (.of ℂ))
        (Fin.snoc (Fin.snoc (fun j => (Scheme.Modules.pullback (pullback.lift (divisorFactor f t) t
            (divisorFactor_comp f t))).obj (K j)) L : Fin (m + 1) → V.Modules)
          ((Scheme.Modules.pullback (divisorFactor f t)).obj (dualSheaf (conormalModule f))) :
          Fin (m + 1 + 1) → V.Modules)
        (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) ((m + 1 + 1 : ℕ) : ℤ)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have := hf.isFiniteLocallyFreeOfRank_conormalModule
  have : Stacks.Ample.IsInvertibleModule X (dualSheaf (conormalModule f)) :=
    GenuineChern.isInvertible_of_rank_one _
  have := isOver_bivariantBaseChangeMap f (𝟙 Y) t
  have : IsProper (bivariantBaseChangeMap f (𝟙 Y) t) :=
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f (𝟙 Y) t)
      (P := @IsProper) inferInstance
  have := GenuineChern.isInvertible_pullback (pullback.snd f (t ≫ 𝟙 Y)) L
  obtain ⟨e, heS, he₂, hchow⟩ := exists_regularNormalGysinClass_cap_fundamentalChowClass_of_isIso
    f hf (t ≫ 𝟙 Y) (m := m + 1) hV.symm
  rw [divisorGysin_properChowPushforward, ← capDegree_properChowPushforward,
    chowGroupCongr_firstChernClassCapChow,
    (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
      (comp_over f _) hf).cap_firstChernClassCapChow (t ≫ 𝟙 Y) L
      ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Y))).obj L) (Iso.refl _)
      ((m + 1 : ℕ) : ℤ) _ (chowGroupCast (fieldChowSituation ℂ) _ (by omega) _)
      ((chowGroupCast_heq _ _ _ _).trans (hchow ▸ chowGroupCongrDegree_heq' _ _ _))]
  set N := (Scheme.Modules.pullback (divisorFactor f t)).obj (dualSheaf (conormalModule f))
  have : AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property N :=
    GenuineChern.isInvertible_pullback _ _
  set z := firstChernClassCapChow (fieldChowSituation ℂ) ((m + 1 : ℕ) : ℤ) (V ↘ Spec (.of ℂ)) N
    (fundamentalChowClass (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ)) ((m + 1 + 1 : ℕ) : ℤ))
  have hstep : chowGroupCongrDegree (fieldChowSituation ℂ)
      (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ)) (natCast_add_sub_natCast m 1)
      (firstChernClassCapChow (fieldChowSituation ℂ) (((m + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
        (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Y))).obj L)
        (chowGroupCast (fieldChowSituation ℂ) _ (by omega)
          (chowPushforwardOfIso (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
            (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ)) e.hom heS ((m + 1 : ℕ) : ℤ) z))) =
      firstChernClassCapChow (fieldChowSituation ℂ) (m : ℤ)
        (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback (pullback.snd f (t ≫ 𝟙 Y))).obj L)
        (chowPushforwardOfIso (fieldChowSituation ℂ) (V ↘ Spec (.of ℂ))
          (pullback.fst f (t ≫ 𝟙 Y) ≫ X ↘ Spec (.of ℂ)) e.hom heS ((m + 1 : ℕ) : ℤ) z) :=
    eq_of_heq ((chowGroupCongrDegree_heq' _ _ _).trans
      (GenuineChern.firstChernClassCapChow_heq _ _ (by omega) (chowGroupCast_heq _ _ _ _)))
  rw [hstep]
  refine (capDegree_firstChernClassCapChow _ _ _ _).trans ?_
  rw [chowPushforwardOfIso, ← capDegree_properChowPushforward]
  refine (capDegree_firstChernClassCapChow _ _ _ _).trans ?_
  have he : e.hom = inv (pullback.snd f (t ≫ 𝟙 Y)) := by
    rw [← cancel_mono (pullback.snd f (t ≫ 𝟙 Y)), he₂, IsIso.inv_hom_id]
  have hv : e.hom ≫ bivariantBaseChangeMap f (𝟙 Y) t =
      pullback.lift (divisorFactor f t) t (divisorFactor_comp f t) := by
    apply pullback.hom_ext
    · rw [Category.assoc, bivariantBaseChangeMap_fst, pullback.lift_fst, he]
    · simp only [Category.assoc, bivariantBaseChangeMap, pullback.lift_snd]
      rw [← Category.assoc, he₂, Category.id_comp]
  refine DFunLike.congr_fun (capDegree_congr_iso _ _ _ fun j => ?_) _
  refine Fin.lastCases ⟨eqToIso (by simp only [Fin.snoc_last, N])⟩ (fun i => ?_) j
  simp only [Fin.snoc_castSucc]
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [Fin.snoc_last]
    exact ⟨(Scheme.Modules.pullbackComp e.hom (pullback.snd f (t ≫ 𝟙 Y))).app L ≪≫
      (Scheme.Modules.pullbackCongr he₂).app L ≪≫ (Scheme.Modules.pullbackId V).app L⟩
  · simp only [Fin.snoc_castSucc]
    exact ⟨(Scheme.Modules.pullbackComp e.hom (bivariantBaseChangeMap f (𝟙 Y) t)).app _ ≪≫
      (Scheme.Modules.pullbackCongr hv).app _⟩

private instance isOver_inv_pullback_fst_id : (inv (pullback.fst f (𝟙 Y))).IsOver (Spec (.of ℂ)) :=
  ⟨by change inv (pullback.fst f (𝟙 Y)) ≫ pullback.fst f (𝟙 Y) ≫ X ↘ Spec (.of ℂ) = _
      rw [IsIso.inv_hom_id_assoc]⟩

omit [IsClosedImmersion f] [IsComplexScheme X] [IsComplexScheme Y] in
/-- A point of the preimage of `X(ℂ)` under the identity of `Y(ℂ)` lies in `X(ℂ)`. -/
theorem mem_range_of_mem_preimage_map_id
    (y : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 Y))).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) f)) :
    (y.1 : UnderlyingSpace ℂ Y) ∈ range (UnderlyingSpace.map (K := ℂ) f) := by
  simpa [UnderlyingSpace.map_id] using y.2

/-- The inverse `X(ℂ) ⊆ Y(ℂ) → (X ×_Y Y)(ℂ)` of the map of points of the fibre square of `f`
along `𝟙 Y`. -/
def fibreSquarePointsIdInv :
    C((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 Y))).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) f), UnderlyingSpace ℂ (pullback f (𝟙 Y))) :=
  let φ := (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isEmbedding.toHomeomorph
  (UnderlyingSpace.map (K := ℂ) (inv (pullback.fst f (𝟙 Y)))).comp
    ((ContinuousMap.mk φ.symm φ.symm.continuous).comp
      (⟨fun y => ⟨y.1, mem_range_of_mem_preimage_map_id f y⟩, continuous_subtype_val.subtype_mk _⟩ :
        C((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 Y))).hom ⁻¹'
          range (UnderlyingSpace.map (K := ℂ) f), range (UnderlyingSpace.map (K := ℂ) f))))

omit [IsComplexScheme X] [IsComplexScheme Y] in
/-- `fibreSquarePointsIdInv` is a left inverse of the map of points of the fibre square. -/
theorem fibreSquarePointsIdInv_fibreSquarePointsHom (p : UnderlyingSpace ℂ (pullback f (𝟙 Y))) :
    fibreSquarePointsIdInv f
      (fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 Y)).flip p) = p := by
  set F := fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 Y)).flip
  let φ := (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isEmbedding.toHomeomorph
  have hφ : ∀ x, (φ x : UnderlyingSpace ℂ Y) = UnderlyingSpace.map (K := ℂ) f x := fun _ => rfl
  have hsnd : pullback.snd f (𝟙 Y) = pullback.fst f (𝟙 Y) ≫ f := by
    rw [pullback.condition, Category.comp_id]
  have h₁ : φ.symm ⟨(F p).1, mem_range_of_mem_preimage_map_id f (F p)⟩ =
      UnderlyingSpace.map (K := ℂ) (pullback.fst f (𝟙 Y)) p := by
    apply φ.injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    rw [hφ]
    apply UnderlyingSpace.ext
    change p.toHom ≫ pullback.snd f (𝟙 Y) = (p.toHom ≫ pullback.fst f (𝟙 Y)) ≫ f
    rw [hsnd, Category.assoc]
  change UnderlyingSpace.map (K := ℂ) (inv (pullback.fst f (𝟙 Y)))
    (φ.symm ⟨(F p).1, mem_range_of_mem_preimage_map_id f (F p)⟩) = p
  rw [h₁]
  apply UnderlyingSpace.ext
  change (p.toHom ≫ pullback.fst f (𝟙 Y)) ≫ inv (pullback.fst f (𝟙 Y)) = p.toHom
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

omit [IsComplexScheme X] [IsComplexScheme Y] in
/-- `fibreSquarePointsIdInv` is a right inverse of the map of points of the fibre square. -/
theorem fibreSquarePointsHom_fibreSquarePointsIdInv
    (y : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 Y))).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) f)) :
    fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 Y)).flip
      (fibreSquarePointsIdInv f y) = y := by
  let φ := (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isEmbedding.toHomeomorph
  have hφ : ∀ x, (φ x : UnderlyingSpace ℂ Y) = UnderlyingSpace.map (K := ℂ) f x := fun _ => rfl
  have hsnd : pullback.snd f (𝟙 Y) = pullback.fst f (𝟙 Y) ≫ f := by
    rw [pullback.condition, Category.comp_id]
  apply Subtype.ext
  obtain ⟨x, hx⟩ : ∃ x, φ.symm ⟨y.1, mem_range_of_mem_preimage_map_id f y⟩ = x := ⟨_, rfl⟩
  have hx' : UnderlyingSpace.map (K := ℂ) f x = y.1 := by
    rw [← hφ, ← hx, Homeomorph.apply_symm_apply]
  change UnderlyingSpace.map (K := ℂ) (pullback.snd f (𝟙 Y))
    (UnderlyingSpace.map (K := ℂ) (inv (pullback.fst f (𝟙 Y)))
      (φ.symm ⟨y.1, mem_range_of_mem_preimage_map_id f y⟩)) = y.1
  rw [hx, ← hx']
  apply UnderlyingSpace.ext
  change (x.toHom ≫ inv (pullback.fst f (𝟙 Y))) ≫ pullback.snd f (𝟙 Y) = x.toHom ≫ f
  rw [hsnd, Category.assoc, IsIso.inv_hom_id_assoc]

omit [IsComplexScheme X] [IsComplexScheme Y] in
/-- For the test scheme `𝟙 Y`, the map `(X ×_Y Y)(ℂ) → X(ℂ) ⊆ Y(ℂ)` of the fibre square is a
homeomorphism onto its target, so its push-forward is injective. -/
private theorem injective_pushforward_fibreSquarePointsHom_id (n : ℤ) :
    Function.Injective (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 Y)).flip)
      (isProperMap_fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 Y)).flip) n).hom := by
  set F := fibreSquarePointsHom (IsPullback.of_hasPullback f (𝟙 Y)).flip
  let H : UnderlyingSpace ℂ (pullback f (𝟙 Y)) ≃ₜ
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 Y))).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f)) :=
    { toFun := F, invFun := fibreSquarePointsIdInv f
      left_inv := fibreSquarePointsIdInv_fibreSquarePointsHom f
      right_inv := fibreSquarePointsHom_fibreSquarePointsIdInv f
      continuous_toFun := F.hom.continuous
      continuous_invFun := (fibreSquarePointsIdInv f).continuous }
  let G : TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 Y))).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) f)) ⟶ TopCat.of (UnderlyingSpace ℂ (pullback f (𝟙 Y))) :=
    TopCat.ofHom (fibreSquarePointsIdInv f)
  have hG : IsProperMap G := H.symm.isProperMap
  have hFG : F ≫ G = 𝟙 _ :=
    ConcreteCategory.hom_ext _ _ (fibreSquarePointsIdInv_fibreSquarePointsHom f)
  intro a b hab
  have key : ∀ c, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) G hG n).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) F
        (isProperMap_fibreSquarePointsHom _) n).hom c) = c := fun c => by
    rw [borelMooreHomology.pushforward_comp_apply ℚ F G _ hG (hFG ▸ isProperMap_id)]
    exact borelMooreHomology.pushforward_id_apply' ℚ _ _ hFG n c
  rw [← key a, ← key b, hab]

/-- **Fulton's Theorem 19.2 for the Gysin map of a divisor, on homologically trivial classes.**
If `Y` carries an ample invertible module and `cl(α) = 0`, then `cl(f^! α) = 0`. -/
theorem chowCycleClass_divisorGysin_eq_zero (A : Y.Modules) [IsInvertibleModule Y A]
    (hA : IsAmple Y A) {m : ℕ} (α : chowGroup (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) (m + 1 : ℕ))
    (hα : chowCycleClass ℚ (m + 1) α = 0) :
    chowCycleClass (X := pullback f (𝟙 Y)) ℚ m (divisorGysin f hf m α) = 0 := by
  obtain ⟨u₀, hu₀⟩ := MMP.Modules.exists_isRegularImbeddingOrientationClass ℚ hf
  have h := chowCycleMapRefinedGysinFormulaAt_of_isEffectiveCartierDivisor f (𝟙 Y) ℚ hf hu₀ A hA
    m α
  unfold ChowCycleMapRefinedGysinFormulaAt at h
  rw [hα, map_zero, map_zero] at h
  exact injective_pushforward_fibreSquarePointsHom_id f (2 * m : ℕ) (h.trans (map_zero _).symm)

omit [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [IsComplexScheme X] [IsComplexScheme Y] in
/-- The two projections of the pullback of the monomorphism `f` along `f ≫ 𝟙 Y` agree. -/
theorem pullback_fst_eq_snd_self : pullback.fst f (f ≫ 𝟙 Y) = pullback.snd f (f ≫ 𝟙 Y) := by
  rw [← cancel_mono f, pullback.condition, Category.comp_id]

/-- The second projection `X ×_Y X ⟶ X` of the pullback of `f` along `f ≫ 𝟙 Y` is an
isomorphism. -/
instance isIso_pullback_snd_self : IsIso (pullback.snd f (f ≫ 𝟙 Y)) :=
  ⟨⟨pullback.lift (𝟙 _) (𝟙 _) (by simp), by
    apply pullback.hom_ext <;> simp [pullback_fst_eq_snd_self], by simp⟩⟩

omit [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [IsComplexScheme X] [IsComplexScheme Y] in
/-- The factorization of `f` itself through the divisor `f` is the identity of `X`. -/
theorem divisorFactor_self : divisorFactor f f = 𝟙 X := by
  simp only [divisorFactor, pullback_fst_eq_snd_self, IsIso.inv_hom_id]

omit [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] in
/-- The family `(H, L, N)` of invertible modules is invertible. -/
theorem isInvertible_snoc_snoc {m : ℕ} (H : Fin m → X.Modules) (L N : X.Modules)
    [hH : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (H j)]
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] :
    ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Fin.snoc (Fin.snoc H L : Fin (m + 1) → X.Modules) N : Fin (m + 1 + 1) → X.Modules) j) :=
  inferInstance

/-- **The self-intersection degree.** For the divisor `f : X ⟶ Y` itself, invertible modules
`K` on `X ×_Y Y` restricting to `H` on `X`, an invertible module `L` and a module `N'` isomorphic
to the normal sheaf `𝒩 = 𝒞_{X/Y}^∨`:
`deg(c₁(K) ∩ f^!(f_*(c₁(L) ∩ [X]))) = deg(c₁(H) c₁(L) c₁(N') ∩ [X])`. -/
theorem capDegree_divisorGysin_self [IsProper (X ↘ Spec (.of ℂ))]
    [IsIntegral X] {m : ℕ} (hX : topologicalKrullDim X = (m + 1 + 1 : ℕ))
    (L N' : X.Modules) (K : Fin m → (pullback f (𝟙 Y)).Modules) (H : Fin m → X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [hN' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N']
    [hK : ∀ j, SheafOfModules.IsInvertible (pullback f (𝟙 Y)).presheaf
      (pullback f (𝟙 Y)).ringCatSheaf.2 (K j)]
    [hH : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (H j)]
    (eH : ∀ j, Nonempty ((Scheme.Modules.pullback
      (pullback.lift (divisorFactor f f) f (divisorFactor_comp f f))).obj (K j) ≅ H j))
    (eN : Nonempty (dualSheaf (conormalModule f) ≅ N')) :
    capDegree ℂ (pullback.fst f (𝟙 Y) ≫ X ↘ Spec (.of ℂ)) K
        (divisorGysin f hf m (pushforwardFirstChernCapFundamental f m L)) =
      @capDegree ℂ _ X (X ↘ Spec (.of ℂ)) _ (m + 1 + 1)
        (Fin.snoc (Fin.snoc H L : Fin (m + 1) → X.Modules) N' : Fin (m + 1 + 1) → X.Modules)
        (isInvertible_snoc_snoc H L N')
        (fundamentalChowClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((m + 1 + 1 : ℕ) : ℤ)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have := hf.isFiniteLocallyFreeOfRank_conormalModule
  have : Stacks.Ample.IsInvertibleModule X (dualSheaf (conormalModule f)) :=
    GenuineChern.isInvertible_of_rank_one _
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback (divisorFactor f f)).obj (dualSheaf (conormalModule f))) :=
    GenuineChern.isInvertible_pullback _ _
  have : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.lift (divisorFactor f f) f
        (divisorFactor_comp f f))).obj (K j)) := fun j =>
    have : SheafOfModules.IsInvertible (pullback f (𝟙 Y)).sheaf.obj
      (pullback f (𝟙 Y)).ringCatSheaf.property (K j) := hK j
    GenuineChern.isInvertible_pullback _ _
  rw [pushforwardFirstChernCapFundamental, capDegree_divisorGysin_of_isIso f hf f hX L K]
  refine DFunLike.congr_fun (capDegree_congr_iso _ _ _ fun j => ?_) _
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
    exact ⟨(Scheme.Modules.pullbackCongr (divisorFactor_self f)).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _ ≪≫ eN.some⟩
  · simp only [Fin.snoc_castSucc]
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.snoc_last]
      exact ⟨Iso.refl _⟩
    · simp only [Fin.snoc_castSucc]
      exact eH k

end Gysin

end MMP.Chow
