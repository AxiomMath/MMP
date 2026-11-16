module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreComponentClasses
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreCurveDegree
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreComponentRestriction
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.IntersectionForms
public import MMP.AlgebraicGeometry.Intersection.PullbackAmpleIntersectionNumbers
public import MMP.AlgebraicGeometry.Divisor.CartierMovingLemma
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.AmpleSubExceptional
public import MMP.AlgebraicGeometry.Intersection.DegreeZeroCurveVanishing
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.PushforwardComparison
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericZeroByEdges

/-!
# The kernel step of the generic algebraic defect

Let `r : Z ⟶ Y` be a curve-and-point exceptional model with exceptional divisor `F = ∑ᵢ Fᵢ`. If
`ℚ`-divisors `Lᵢ` on the components have zero ambient class `∑ᵢ (ιᵢ)_*[Lᵢ] = 0` in `H_4(Z, ℚ)`
and the class of their fibre cycle vanishes on the general fibres over every singular curve of
`Y`, then `([Lᵢ])ᵢ` is the class tuple of an oriented double-surface system.

The proof: subtract an oriented system on the edges over curves so that the curve classes vanish
on the components of the general fibres
(`MMP.Fourfold.IsCurvePointExceptionalModel.exists_mem_orientedSurfaceCoefficients_sub`); turn
this vanishing into the vanishing of the intersection numbers with `H = r^*H_Y` on the curve
components and the double surfaces over curves (the moving lemma for `H_Y` and the degrees on the
curves of the general fibres); then apply the numerical Hodge index argument
`MMP.Fourfold.exists_mem_orientedSurfaceCoefficients_forall_sub_mem_of_hodgeIndex`, with
`A = N H - D` ample on every component and double surface, and the intersection numbers of `H`.

## Main results

* `MMP.Fourfold.map_eq_sum_of_isWeilDivisorOfCartier`: an additive invariant of divisorial
  sheaves is determined by the Weil divisor.
* `MMP.Fourfold.IsCurvePointExceptionalModel.forall_lin_bGA_sub_eq_zero_of_fibre`: the vanishing
  on the general fibres, in the intersection forms.
* `Fourfold.IsCurvePointExceptionalModel.exists_mem_orientedSurfaceCoefficients_forall_sub_mem`:
  the Hodge index argument on a curve-and-point exceptional model.
* `MMP.Fourfold.IsCurvePointExceptionalModel.mem_orientedSurfaceClasses_of_fibre_vanishing`: the
  kernel step.

## Implementation notes

`H|_{Fᵢ}` enters the isotropic index theorem through a Weil divisor `hᵢ` with
`𝒪(∑ hᵢ,Q π_Q) ≅ H|_{Fᵢ}`; the intersection numbers and the first Chern class are linear in the
Weil divisor (`MMP.Fourfold.map_eq_sum_of_isWeilDivisorOfCartier`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MMP
open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open scoped MMP.SubschemeOver

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel

attribute [local instance] MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec1
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec2
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.inv_vec3
  MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.isComplete_subscheme

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z] [IsLocallyNoetherian Z]
  [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsComplexScheme Z]

/-- **An irreducible closed set of dimension zero is a point**, in a `T₀` space. -/
theorem eq_of_mem_of_isIrreducible_of_topologicalKrullDim_le_zero {X : Type*}
    [TopologicalSpace X] [T0Space X] {S : Set X} (hS : IsIrreducible S) (hSc : IsClosed S)
    (hd : topologicalKrullDim S ≤ 0) {x y : X} (hx : x ∈ S) (hy : y ∈ S) : x = y := by
  have key : ∀ z ∈ S, closure ({z} : Set X) = S := by
    intro z hz
    by_contra hne
    haveI : IrreducibleSpace S := Subtype.irreducibleSpace hS
    let A : IrreducibleCloseds S :=
      ⟨closure {⟨z, hz⟩}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds S := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
    have hAB : A < B := by
      refine lt_of_le_of_ne (fun _ _ => trivial) fun h => hne ?_
      have h1 : (A : Set S) = Set.univ := congrArg SetLike.coe h
      refine le_antisymm (closure_minimal (Set.singleton_subset_iff.2 hz) hSc) fun w hw => ?_
      have hw' : (⟨w, hw⟩ : S) ∈ closure ({⟨z, hz⟩} : Set S) := by
        change (⟨w, hw⟩ : S) ∈ (A : Set S)
        rw [h1]; trivial
      rw [closure_subtype] at hw'
      simpa using hw'
    exact absurd hd (not_le.2 (Order.krullDim_pos_iff.2 ⟨A, B, hAB⟩))
  exact IsGenericPoint.eq (key x hx) (key y hy)

/-- **A morphism with closed irreducible range of dimension zero is constant.** -/
theorem exists_forall_base_eq_of_topologicalKrullDim_range_le_zero {W Y : Scheme.{0}}
    [IrreducibleSpace W] (u : W ⟶ Y) (hc : IsClosed (Set.range u.base))
    (hd : topologicalKrullDim (Set.range u.base) ≤ 0) (x₀ : W) : ∀ x, u.base x = u.base x₀ := by
  have hirr : IsIrreducible (Set.range u.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ W).image _ u.base.hom.continuous.continuousOn
  exact fun x => eq_of_mem_of_isIrreducible_of_topologicalKrullDim_le_zero hirr hc hd ⟨x, rfl⟩
    ⟨x₀, rfl⟩

/-- `(L₁ · L₂ · L₃) = 0` when `L₃` is pulled back along a constant morphism. -/
theorem num3_eq_zero_of_forall_eq {W Y : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProper f]
    (u : W ⟶ Y) (y : Y) (hy : ∀ x, u.base x = y) (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] (L₁ L₂ L₃ : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃]
    (e : Nonempty (L₃ ≅ (Scheme.Modules.pullback u).obj M)) : num3 W f L₁ L₂ L₃ = 0 := by
  rw [num3_congr f _ _ _ _ _ _ ⟨Iso.refl _⟩ ⟨Iso.refl _⟩ e]
  unfold num3
  split_ifs with h
  · exact_mod_cast sheafIntersectionNumber_eq_zero_of_forall_eq ℂ f u (𝟙 W) 3 h _ y hy M 2 rfl
  · rfl

/-- `(L₁ · L₂) = 0` on a surface when `L₂` is pulled back along a constant morphism. -/
theorem num2_eq_zero_of_forall_eq {W Y : Scheme.{0}} (f : W ⟶ Spec (.of ℂ)) [IsProper f]
    (u : W ⟶ Y) (y : Y) (hy : ∀ x, u.base x = y) (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M] (L₁ L₂ : W.Modules)
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₁]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    (e : Nonempty (L₂ ≅ (Scheme.Modules.pullback u).obj M)) : num2 W f L₁ L₂ = 0 := by
  rw [num2_congr f _ _ _ _ ⟨Iso.refl _⟩ e]
  unfold num2
  split_ifs with h
  · exact_mod_cast sheafIntersectionNumber_eq_zero_of_forall_eq ℂ f u (𝟙 W) 2 h _ y hy M 1 rfl
  · rfl

section Forms

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsProper (Z ↘ Spec (.of ℂ))] {F : Divisor Z}
  (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
    i.1.idealSheaf.subscheme.CartierDivisor)

/-- On a component over a point, the forms `x · H · A` and `x² · H` vanish. -/
theorem lin_bGA_eq_zero_and_bilin_bB_eq_zero_of_forall_eq {Y : Scheme.{0}}
    (Hc Hh : Z.CartierDivisor) (i : F.support) (u : i.1.idealSheaf.subscheme ⟶ Y) (y : Y)
    (hy : ∀ x, u.base x = y) (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    (e : Nonempty ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ (Scheme.Modules.pullback u).obj M))
    (x : QDivisor i.1.idealSheaf.subscheme) :
    Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) x = 0 ∧
      bilin (bB π Hh i) x x = 0 := by
  have h1 : bGA π (fun _ => Hh) Hc i = fun _ => 0 := funext fun P => by
    unfold bGA
    exact num3_eq_zero_of_forall_eq _ u y hy M _ _ _ e
  have h2 : bB π Hh i = fun _ _ => 0 := funext₂ fun P Q =>
    num3_eq_zero_of_forall_eq _ u y hy M _ _ _ e
  rw [h1, h2, bilin_zero]
  simp [Finsupp.linearCombination_apply]

end Forms

/-- **An additive invariant of divisorial sheaves is determined by the Weil divisor.** Let `X`
be a normal integral locally Noetherian scheme, `π_Q` a Cartier divisor with Weil divisor `Q` for
every prime divisor `Q`, and `φ` an additive function of the Cartier divisors of `X` depending only
on the isomorphism class of their sheaves. If `C` has Weil divisor `w = ∑ w_Q Q`, then
`φ(C) = ∑ w_Q φ(π_Q)`. -/
theorem map_eq_sum_of_isWeilDivisorOfCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {G : Type*} [AddCommGroup G]
    (φ : X.CartierDivisor →+ G)
    (hφ : ∀ C C' : X.CartierDivisor,
      Nonempty (MMP.CartierDivisor.sheaf C ≅ MMP.CartierDivisor.sheaf C') → φ C = φ C')
    (π : MMP.Mori.PrimeDivisor X → X.CartierDivisor)
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π P) (Finsupp.single P 1))
    {C : X.CartierDivisor} {w : Divisor X} (hC : MMP.Intersection.IsWeilDivisorOfCartier C w) :
    φ C = w.sum fun Q c => c • φ (π Q) := by
  classical
  have hadd : ∀ {A B : X.CartierDivisor} {v u : Divisor X},
      MMP.Intersection.IsWeilDivisorOfCartier A v →
      MMP.Intersection.IsWeilDivisorOfCartier B u →
      MMP.Intersection.IsWeilDivisorOfCartier (A + B) (v + u) := fun hA hB P => (hA P).add (hB P)
  have h0 : MMP.Intersection.IsWeilDivisorOfCartier (0 : X.CartierDivisor) 0 := fun P => by
    simpa using MMP.Intersection.isOrderAlong_zero (MMP.Intersection.primeDivisorSubvariety P)
  have hsum : ∀ (s : Finset (MMP.Mori.PrimeDivisor X)) (m : MMP.Mori.PrimeDivisor X → ℕ),
      MMP.Intersection.IsWeilDivisorOfCartier (∑ Q ∈ s, m Q • π Q)
        (∑ Q ∈ s, m Q • (Finsupp.single Q 1 : Divisor X)) := by
    intro s m
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine hadd ?_ ih
      induction m a with
      | zero => simpa using h0
      | succ k ihk => rw [succ_nsmul, succ_nsmul]; exact hadd ihk (hπ a)
  set mp : MMP.Mori.PrimeDivisor X → ℕ := fun Q => (w Q).toNat with hmp
  set mn : MMP.Mori.PrimeDivisor X → ℕ := fun Q => (-w Q).toNat with hmn
  have hw : w + ∑ Q ∈ w.support, mn Q • (Finsupp.single Q 1 : Divisor X) =
      ∑ Q ∈ w.support, mp Q • (Finsupp.single Q 1 : Divisor X) := by
    refine Finsupp.ext fun P => ?_
    simp only [Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_ite, smul_zero, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
      Finsupp.mem_support_iff, hmp, hmn]
    split_ifs with h
    · have := Int.toNat_sub_toNat_neg (w P)
      omega
    · simp [not_not.1 h]
  have e1 := (hadd hC (hsum w.support mn)).nonempty_sheaf_iso_divisorialSheaf
  rw [hw] at e1
  have e2 := (hsum w.support mp).nonempty_sheaf_iso_divisorialSheaf
  have h := hφ _ _ ⟨e1.some ≪≫ e2.some.symm⟩
  rw [map_add, map_sum, map_sum] at h
  simp only [map_nsmul] at h
  rw [Finsupp.sum, eq_sub_of_add_eq h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [← natCast_zsmul, ← natCast_zsmul, ← sub_smul, Int.toNat_sub_toNat_neg]

/-- The linear combination of a family over the coefficients of an integral divisor. -/
theorem linearCombination_toQDivisor {X : Scheme.{0}} {M : Type*} [AddCommGroup M] [Module ℚ M]
    (b : MMP.Mori.PrimeDivisor X → M) (w : Divisor X) :
    Finsupp.linearCombination ℚ b (Divisor.toQDivisor w) = w.sum fun Q c => c • b Q := by
  change Finsupp.linearCombination ℚ b (Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _) w) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
  simp [Int.cast_smul_eq_zsmul]

section Weil

variable {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
  (π : MMP.Mori.PrimeDivisor W → W.CartierDivisor)
  (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π P) (Finsupp.single P 1))
  {C : W.CartierDivisor} {w : Divisor W} (hC : MMP.Intersection.IsWeilDivisorOfCartier C w)

include hπ hC in
/-- `(C · L₂ · L₃) = ∑ w_Q (π_Q · L₂ · L₃)` for a Cartier divisor `C` with Weil divisor `w`. -/
theorem linearCombination_num3_toQDivisor (f : W ⟶ Spec (.of ℂ)) [IsProper f]
    (L₂ L₃ : W.Modules) [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₂]
    [SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L₃] :
    Finsupp.linearCombination ℚ (fun Q => num3 W f (MMP.CartierDivisor.sheaf (π Q)) L₂ L₃)
      (Divisor.toQDivisor w) = num3 W f (MMP.CartierDivisor.sheaf C) L₂ L₃ := by
  classical
  rw [linearCombination_toQDivisor]
  unfold num3
  split_ifs with h
  · let ψ : W.CartierDivisor → ℤ := fun B =>
      @sheafIntersectionNumber ℂ _ W W f _ (𝟙 W) _ 3 h ![CartierDivisor.sheaf B, L₂, L₃] inv_vec3
    have hadd : ∀ B B', ψ (B + B') = ψ B + ψ B' := by
      intro B B'
      have e := sheafIntersectionNumber_update_sheaf_add ℂ f (𝟙 W) 3 h
        ![MMP.CartierDivisor.sheaf B, L₂, L₃] 0 B B'
      have hc : ∀ B'' : W.CartierDivisor, @sheafIntersectionNumber ℂ _ W W f _ (𝟙 W) _ 3 h
          (Function.update ![MMP.CartierDivisor.sheaf B, L₂, L₃] 0 (MMP.CartierDivisor.sheaf B''))
          (AlgebraicGeometry.isInvertible_update _ 0 _) = ψ B'' := fun B'' =>
        @sheafIntersectionNumber_congr_family ℂ _ W W f _ (𝟙 W) _ 3 h _ _
          (AlgebraicGeometry.isInvertible_update _ 0 _) inv_vec3
          (funext fun t => by fin_cases t <;> simp)
      rw [hc, hc, hc] at e
      exact e
    let φ : W.CartierDivisor →+ ℤ := AddMonoidHom.mk' ψ hadd
    have hφ : ∀ B B' : W.CartierDivisor,
        Nonempty (MMP.CartierDivisor.sheaf B ≅ MMP.CartierDivisor.sheaf B') →
        φ B = φ B' := fun B B' e =>
      @sIN_congr_iso ℂ _ W W f _ (𝟙 W) _ 3 h _ _ inv_vec3 inv_vec3
        fun q => by fin_cases q; exacts [e, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩]
    have key := map_eq_sum_of_isWeilDivisorOfCartier φ hφ π hπ hC
    change ψ C = w.sum fun Q c => c • ψ (π Q) at key
    change (w.sum fun Q c => (c : ℤ) • (ψ (π Q) : ℚ)) = (ψ C : ℚ)
    rw [key, Finsupp.sum, Finsupp.sum, Int.cast_sum]
    simp [zsmul_eq_mul]
  · simp

include hπ hC in
/-- `(g^*C · L₂) = ∑ w_Q (g^*π_Q · L₂)` on a scheme `S` mapping to `W`, for a Cartier divisor `C`
with Weil divisor `w`. -/
theorem linearCombination_num2_toQDivisor {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) [IsProper f]
    (g : S ⟶ W) (L₂ : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L₂] :
    Finsupp.linearCombination ℚ
      (fun Q => num2 S f ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf (π Q))) L₂)
      (Divisor.toQDivisor w) =
      num2 S f ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf C)) L₂ := by
  classical
  rw [linearCombination_toQDivisor]
  unfold num2
  split_ifs with h
  · let ψ : W.CartierDivisor → ℤ := fun B =>
      @sheafIntersectionNumber ℂ _ S S f _ (𝟙 S) _ 2 h
        ![(Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf B), L₂] inv_vec2
    have hψ : ∀ B, ψ B = slotHom f (𝟙 S) 2 h ![L₂, L₂] 0 g B := fun B =>
      (@sheafIntersectionNumber_congr_family ℂ _ S S f _ (𝟙 S) _ 2 h _ _ inv_vec2
        (AlgebraicGeometry.isInvertible_update _ 0 _)
        (funext fun t => by fin_cases t <;> simp)).trans (slotHom_apply _ _ _ _ _ _ _ B).symm
    let φ : W.CartierDivisor →+ ℤ := slotHom f (𝟙 S) 2 h ![L₂, L₂] 0 g
    have hφ : ∀ B B' : W.CartierDivisor,
        Nonempty (MMP.CartierDivisor.sheaf B ≅ MMP.CartierDivisor.sheaf B') →
        φ B = φ B' := fun B B' e => by
      rw [← hψ, ← hψ]
      exact @sIN_congr_iso ℂ _ S S f _ (𝟙 S) _ 2 h _ _ inv_vec2 inv_vec2
        fun q => by fin_cases q; exacts [⟨(Scheme.Modules.pullback g).mapIso e.some⟩, ⟨Iso.refl _⟩]
    have key := map_eq_sum_of_isWeilDivisorOfCartier φ hφ π hπ hC
    simp only [φ, ← hψ] at key
    change (w.sum fun Q c => (c : ℤ) • (ψ (π Q) : ℚ)) = (ψ C : ℚ)
    rw [key, Finsupp.sum, Finsupp.sum, Int.cast_sum]
    simp [zsmul_eq_mul]
  · simp

include hπ hC in
/-- `c₁(𝒪(C)) = ∑ w_Q c₁(𝒪(π_Q))` in rational cohomology, for a Cartier divisor `C` with Weil
divisor `w`. -/
theorem linearCombination_mapCoeff_algebraicFirstChernClass_toQDivisor [W.Over (Spec (.of ℂ))] :
    Finsupp.linearCombination ℚ (fun Q => singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass (MMP.CartierDivisor.sheaf (π Q)))) (Divisor.toQDivisor w) =
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass (MMP.CartierDivisor.sheaf C)) := by
  classical
  rw [linearCombination_toQDivisor]
  let ψ : W.CartierDivisor → _ := fun B => singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
    (algebraicFirstChernClass (MMP.CartierDivisor.sheaf B))
  have hadd : ∀ B B', ψ (B + B') = ψ B + ψ B' := by
    intro B B'
    haveI := Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible W.presheaf
      W.ringCatSheaf.2 (MMP.CartierDivisor.sheaf B) (MMP.CartierDivisor.sheaf B')
    have h1 : algebraicFirstChernClass (MMP.CartierDivisor.sheaf (B + B')) =
        algebraicFirstChernClass (MMP.CartierDivisor.sheaf B) +
          algebraicFirstChernClass (MMP.CartierDivisor.sheaf B') :=
      (algebraicFirstChernClass_eq_of_iso (MMP.CartierDivisorSheaf.sheafMulIso B B')).symm.trans
        (algebraicFirstChernClass_sheafTensor _ _)
    simp only [ψ]
    rw [h1, map_add]
  let φ : W.CartierDivisor →+ _ := AddMonoidHom.mk' ψ hadd
  have hφ : ∀ B B' : W.CartierDivisor, Nonempty (CartierDivisor.sheaf B ≅ CartierDivisor.sheaf B') →
      φ B = φ B' := fun B B' e => by
    change ψ B = ψ B'
    simp only [ψ]
    rw [algebraicFirstChernClass_eq_of_iso e.some]
  exact (map_eq_sum_of_isWeilDivisorOfCartier φ hφ π hπ hC).symm

end Weil

section HForms

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsProper (Z ↘ Spec (.of ℂ))] {F : Divisor Z}
  (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
    i.1.idealSheaf.subscheme.CartierDivisor)
  {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsProper sY] (r : Z ⟶ Y)
  (hcomp : r ≫ sY = Z ↘ Spec (.of ℂ)) (MY : Y.Modules)
  [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 MY]

include hcomp in
/-- **`H|_{Fᵢ} · A² > 0` on a component over a curve**, for `H|_{Fᵢ}` the sheaf of a Cartier
divisor with Weil divisor `w`. -/
theorem lin_bLam_toQDivisor_pos (hM : Stacks.Ample.IsAmple Y MY) (Hc : Z.CartierDivisor)
    (i : F.support) [IsIntegral i.1.idealSheaf.subscheme]
    [IsLocallyNoetherian i.1.idealSheaf.subscheme] [IsNormal i.1.idealSheaf.subscheme]
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    {C : i.1.idealSheaf.subscheme.CartierDivisor} {w : Divisor i.1.idealSheaf.subscheme}
    (hC : MMP.Intersection.IsWeilDivisorOfCartier C w)
    (e : Nonempty (MMP.CartierDivisor.sheaf C ≅
      (Scheme.Modules.pullback (i.1.idealSheaf.subschemeι ≫ r)).obj MY))
    (hA : Stacks.Ample.IsAmple i.1.idealSheaf.subscheme
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (hd : topologicalKrullDim i.1.idealSheaf.subscheme = 3)
    (hpos : 0 < topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base)) :
    0 < Finsupp.linearCombination ℚ (bLam π Hc i) (Divisor.toQDivisor w) := by
  have h := linearCombination_num3_toQDivisor (π i) hπ hC
    (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
  change Finsupp.linearCombination ℚ (fun Q => num3 _ _ _ _ _) _ = _ at h
  unfold bLam
  rw [h, num3_congr _ _ _ _ _ _ _ e ⟨Iso.refl _⟩ ⟨Iso.refl _⟩, num3_eq _ _ _ _ hd.le]
  have hu : (i.1.idealSheaf.subschemeι ≫ r) ≫ sY =
      i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ) := by rw [Category.assoc, hcomp]
  have := sheafIntersectionNumber_pullback_isAmple_isAmple_pos ℂ
    (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) sY (i.1.idealSheaf.subschemeι ≫ r) hu MY
    _ (𝟙 _) hM hA hd (by rwa [Category.id_comp])
  exact_mod_cast this

include hcomp in
/-- **`(H|_{Fᵢ})² · A = 0` on a component over a curve.** -/
theorem lin_bGA_toQDivisor_eq_zero (Hc Hh : Z.CartierDivisor)
    (i : F.support) [IsIntegral i.1.idealSheaf.subscheme]
    [IsLocallyNoetherian i.1.idealSheaf.subscheme] [IsNormal i.1.idealSheaf.subscheme]
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    {C : i.1.idealSheaf.subscheme.CartierDivisor} {w : Divisor i.1.idealSheaf.subscheme}
    (hC : MMP.Intersection.IsWeilDivisorOfCartier C w)
    (e : Nonempty (MMP.CartierDivisor.sheaf C ≅
      (Scheme.Modules.pullback (i.1.idealSheaf.subschemeι ≫ r)).obj MY))
    (eH : Nonempty ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
      (CartierDivisor.sheaf Hh) ≅ (Scheme.Modules.pullback (i.1.idealSheaf.subschemeι ≫ r)).obj MY))
    (hA : Stacks.Ample.IsAmple i.1.idealSheaf.subscheme
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (hd : topologicalKrullDim i.1.idealSheaf.subscheme = 3)
    (him : topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) ≤ 1) :
    Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) (Divisor.toQDivisor w) = 0 := by
  have h := linearCombination_num3_toQDivisor (π i) hπ hC
    (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
  change Finsupp.linearCombination ℚ (fun Q => num3 _ _ _ _ _) _ = _ at h
  unfold bGA
  rw [h, num3_congr _ _ _ _ _ _ _ e ⟨Iso.refl _⟩ eH, num3_comm23, num3_eq _ _ _ _ hd.le]
  have hu : (i.1.idealSheaf.subschemeι ≫ r) ≫ sY =
      i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ) := by rw [Category.assoc, hcomp]
  have := sheafIntersectionNumber_pullback_pullback_isAmple_eq_zero ℂ
    (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) sY (i.1.idealSheaf.subschemeι ≫ r) hu MY
    _ (𝟙 _) hA hd.le (by rwa [Category.id_comp])
  exact_mod_cast this

/-- **`H|_{Fᵢ}|_S · A|_S = H|_S · A|_S`** on a double surface `S` with first component `Fᵢ`. -/
theorem lin_bUA_toQDivisor_eq (Hc Hh : Z.CartierDivisor) (σ : DoubleSurface F)
    [IsIntegral σ.fst.idealSheaf.subscheme]
    [IsLocallyNoetherian σ.fst.idealSheaf.subscheme] [IsNormal σ.fst.idealSheaf.subscheme]
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π σ.fstComponent P) (Finsupp.single P 1))
    {C : σ.fst.idealSheaf.subscheme.CartierDivisor} {w : Divisor σ.fst.idealSheaf.subscheme}
    (hC : MMP.Intersection.IsWeilDivisorOfCartier C w)
    (e : Nonempty ((Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ MMP.CartierDivisor.sheaf C)) :
    Finsupp.linearCombination ℚ (bUA π Hc σ) (Divisor.toQDivisor w) =
      num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
        ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)) := by
  have h := linearCombination_num2_toQDivisor (π σ.fstComponent) hπ hC
    ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) (sι σ)
    ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
  unfold bUA
  refine h.trans (num2_congr _ _ _ _ _ ⟨?_⟩ ⟨Iso.refl _⟩)
  exact (Scheme.Modules.pullback (sι σ)).mapIso e.some.symm ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr (sι_comp σ)).app _

include hcomp in
/-- **`H|_S · A|_S ≥ 0`** on every double surface. -/
theorem num2_dsIdeal_pullback_nonneg (hM : Stacks.Ample.IsAmple Y MY) (Hc Hh : Z.CartierDivisor)
    (σ : DoubleSurface F)
    (eH : Nonempty ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj
      (CartierDivisor.sheaf Hh) ≅ (Scheme.Modules.pullback ((dsIdeal σ).subschemeι ≫ r)).obj MY))
    (hA : Stacks.Ample.IsAmple (dsIdeal σ).subscheme
      ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (hd : topologicalKrullDim (dsIdeal σ).subscheme ≤ (2 : ℕ)) :
    0 ≤ num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
        ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)) := by
  rw [num2_congr _ _ _ _ _ eH ⟨Iso.refl _⟩, num2_eq _ _ _ hd]
  have hu : ((dsIdeal σ).subschemeι ≫ r) ≫ sY =
      (dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ) := by rw [Category.assoc, hcomp]
  have := sheafIntersectionNumber_pullback_isAmple_nonneg ℂ
    ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ)) sY ((dsIdeal σ).subschemeι ≫ r) hu MY
    _ (𝟙 _) hM hA hd
  exact_mod_cast this

end HForms

omit [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] in
/-- **The numerical Hodge index argument with the concrete intersection forms.** The core
`MMP.Fourfold.exists_mem_orientedSurfaceCoefficients_forall_sub_mem_of_hodgeIndex`, with the forms
of the components and double surfaces of `F` for `A = Hc` and `H = Hh`, and the adjunction,
kernel and index inputs (`threefold_index_of_isotropic`, `surface_index_of_isotropic`,
`kernel_identities_sub_surfaceCoefficientDivisor`) supplied. -/
theorem exists_mem_orientedSurfaceCoefficients_forall_sub_mem_of_isotropic
    [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z] {F : Divisor Z} [Fintype (DoubleSurface F)]
    [DecidableEq F.support]
    (hB : F.IsSNC (Z ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim Z = 4)
    (hvar : MMP.Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)))
    (hZp : IsProjectiveMorphism (Z ↘ Spec (.of ℂ))) (hBred : ∀ E ∈ F.support, F E = 1)
    (ε : F.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : F.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hc Hh : Z.CartierDivisor) (n : F.support → ℕ) (hn : ∀ i, 0 < n i) (N : ℕ)
    (hAH : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, n l • ε l) ≅
      MMP.CartierDivisor.sheaf (N • Hh)))
    (hAmp : ∀ i : F.support, Stacks.Ample.IsAmple i.1.idealSheaf.subscheme
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (hAmpS : ∀ σ : DoubleSurface F, Stacks.Ample.IsAmple (dsIdeal σ).subscheme
      ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    (pY : Y ⟶ Spec (.of ℂ)) [IsProper pY] (r : Z ⟶ Y)
    (hr : r ≫ pY = Z ↘ Spec (.of ℂ)) (MY : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 MY] (hM : Stacks.Ample.IsAmple Y MY)
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅ (Scheme.Modules.pullback r).obj MY))
    (cur : F.support → Prop) (pt : DoubleSurface F → Prop) (hpt : ∀ σ, pt σ.swap ↔ pt σ)
    (hptc : ∀ σ : DoubleSurface F, ¬ cur σ.fstComponent → pt σ)
    (hcur : ∀ i, cur i →
      topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) = 1)
    (hcurS : ∀ σ : DoubleSurface F, ¬ pt σ →
      topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) = 1)
    (hptS : ∀ σ : DoubleSurface F, pt σ →
      topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0)
    (hv : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme)
    (hhv : ∀ i, cur i → Finsupp.linearCombination ℚ (fun Q =>
        singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (algebraicFirstChernClass (MMP.CartierDivisor.sheaf (π i Q)))) (hv i) =
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hh))))
    (Zl : (DoubleSurface F → ℚ) →ₗ[ℚ] ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme)
    (hZl : ∀ a i, Zl a i = surfaceCoefficientDivisor a i.1)
    (ρv : ∀ σ : DoubleSurface F, QDivisor σ.fst.idealSheaf.subscheme)
    (hZlin : ∀ (f : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme →ₗ[ℚ] ℚ)
      (a : DoubleSurface F → ℚ),
      ∑ i, f i (Zl a i) = ∑ σ : DoubleSurface F, a σ * f σ.fstComponent (ρv σ))
    (hRA : ∀ (σ : DoubleSurface F) x, Finsupp.linearCombination ℚ (bUA π Hc σ) x =
      bilin (bB π Hc σ.fstComponent) x (ρv σ))
    (hpoint : ∀ i, ¬ cur i → ∀ x, Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) x = 0 ∧
      bilin (bB π Hh i) x x = 0)
    (hTIp : ∀ i, ¬ cur i → ∀ x, Finsupp.linearCombination ℚ (bLam π Hc i) x = 0 →
      bilin (bB π Hc i) x x ≤ 0 ∧ (bilin (bB π Hc i) x x = 0 →
        x ∈ LinearMap.ker (MMP.Chow.divisorClass i.1.idealSheaf.subscheme)))
    (hSIp : ∀ σ, pt σ → ∀ x y, Finsupp.linearCombination ℚ (bUA π Hc σ) x =
      Finsupp.linearCombination ℚ (bUA π Hc σ.swap) y →
      bilin (bU π σ) x x - 2 * bilin (bC π σ) x y + bilin (bU π σ.swap) y y ≤ 0)
    (hHA : ∀ i, cur i → 0 < Finsupp.linearCombination ℚ (bLam π Hc i) (hv i))
    (hHH : ∀ i, cur i → Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) (hv i) = 0)
    (hHsym : ∀ σ : DoubleSurface F, Finsupp.linearCombination ℚ (bUA π Hc σ) (hv σ.fstComponent) =
      Finsupp.linearCombination ℚ (bUA π Hc σ.swap) (hv σ.sndComponent))
    (hHnn : ∀ σ : DoubleSurface F, 0 ≤ Finsupp.linearCombination ℚ (bUA π Hc σ) (hv σ.fstComponent))
    (L : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme)
    (hL : ∑ i : F.support, componentHomologyMap i.1 4
      (MMP.Chow.divisorClass i.1.idealSheaf.subscheme (L i)) = 0)
    (hvan : ∀ a ∈ orientedSurfaceCoefficients F, (∀ σ, ¬ pt σ → a σ = 0) →
      (∀ i, cur i → Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) ((L - Zl a) i) = 0 ∧
        bilin (bB π Hh i) ((L - Zl a) i) ((L - Zl a) i) = 0) ∧
      ∀ σ, ¬ pt σ → Finsupp.linearCombination ℚ (bUA π Hh σ) ((L - Zl a) σ.fstComponent) = 0) :
    ∃ a ∈ orientedSurfaceCoefficients F, (∀ σ, ¬ pt σ → a σ = 0) ∧
      ∀ i, L i - Zl a i ∈ LinearMap.ker (MMP.Chow.divisorClass i.1.idealSheaf.subscheme) :=
  exists_mem_orientedSurfaceCoefficients_forall_sub_mem_of_hodgeIndex
    (m := fun i => (n i : ℚ)) (fun i => by exact_mod_cast hn i) (N : ℚ) cur pt hpt hptc
    (fun i => LinearMap.ker (MMP.Chow.divisorClass i.1.idealSheaf.subscheme)) hv Zl ρv
    (fun i => bilin (bB π Hc i)) (fun i => bilin (bB π Hh i)) (fun i => bilin (bG π ε i))
    (fun i => Finsupp.linearCombination ℚ (bLam π Hc i))
    (fun i => Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i))
    (fun i => Finsupp.linearCombination ℚ (bGA π ε Hc i))
    (fun σ => bilin (bU π σ)) (fun σ => bilin (bC π σ))
    (fun σ => Finsupp.linearCombination ℚ (bUA π Hc σ))
    (fun σ => Finsupp.linearCombination ℚ (bUA π Hh σ)) hZlin hRA
    (eq_zero_of_sum_bilin_bB_div_eq_zero hB hdim π hπ hvar hsm hZp hBred ε hε Hc Hh n hn N hAH
      hAmp pt hAmpS pY r hr MY eH hptS Zl hZl)
    (neg_mul_lin_bGA_eq_of_iso hB hdim hvar hsm ε hε π Hc Hh n N hAH)
    (neg_mul_bilin_bG_eq_of_iso hB hdim hvar hsm ε hε π Hc Hh n N hAH)
    hpoint hTIp
    (threefold_index_of_isotropic hB hdim π hπ hZp Hc Hh cur hv hAmp hhv pY r hr MY hM eH hcur)
    hSIp
    (surface_index_of_isotropic hB hdim π hZp Hc Hh pt hAmpS pY r hr MY hM eH hcurS)
    (linearCombination_bGA_eq_zero_of_mem_ker hB hdim hZp ε π hπ Hc)
    (linearCombination_bUA_eq_zero_of_mem_ker hB hdim hZp π hπ Hc)
    hHA hHH hHsym hHnn L hvan
    (kernel_identities_sub_surfaceCoefficientDivisor hB hdim hvar hsm ε hε π hπ hZp Hc pt Zl hZl
      L hL)

section Fibre

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat
  MMP.CartierDivisor.isInvertible_sheaf

open Classical in
/-- **The fibre vanishing as an intersection number.** On a component `E` over a curve, a
`ℚ`-divisor `M = ∑ c_P P` whose curve classes vanish on the components of the general fibres
satisfies `∑ c_P (π_P · r^*H_Y · A) = 0` for every invertible `A`. -/
theorem IsCurvePointExceptionalModel.sum_sheafIntersectionNumber_pullback_eq_zero_of_fibre
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support)
    (hE : topologicalKrullDim (r.base '' (E.1.support : Set Z)) = 1)
    [IsProper (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))]
    (hd : topologicalKrullDim E.1.idealSheaf.subscheme ≤ (3 : ℕ))
    (π : MMP.Mori.PrimeDivisor E.1.idealSheaf.subscheme → E.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π P) (Finsupp.single P 1))
    (HY : Y.CartierDivisor) (A : E.1.idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible E.1.idealSheaf.subscheme.presheaf
      E.1.idealSheaf.subscheme.ringCatSheaf.2 A]
    (M : QDivisor E.1.idealSheaf.subscheme)
    (hvan : ∃ U : Y.Opens, ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty ∧
      ∀ y ∈ (U : Set Y) ∩ r.base '' (E.1.support : Set Z), IsClosed {y} →
        ∀ G : {V : MMP.Intersection.Scheme.Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          M.sum (fun P c ↦ c •
            ∑ᶠ (x : {x : G.1.toScheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (G.1.toScheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
              (_ : Maximal (fun A ↦ IsIrreducible A ∧
                  A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) = 0) :
    (M.sum fun P c ↦ c * (@sheafIntersectionNumber ℂ _ _ _
        (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) _ (𝟙 _) _ 3 hd
        ![MMP.CartierDivisor.sheaf (π P),
          (Scheme.Modules.pullback (E.1.idealSheaf.subschemeι ≫ r)).obj
            (MMP.CartierDivisor.sheaf HY), A]
        (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ)) = 0 := by
  obtain ⟨U, hU, hdeg⟩ := hr.exists_opens_sum_degree_eq_zero_of_fibre_of_restrict E hE π M
    (hr.exists_opens_restrict_maximal_fibre E hE π hπ M.support) hvan
  obtain ⟨D₁, D₂, h₁, h₂, e, hsupp⟩ :=
    hr.exists_isEffective_iso_pullback_sheaf_sub E hE HY U hU
  exact sum_sheafIntersectionNumber_eq_zero_of_iso_sheaf_sub ℂ _ hd π M _ D₁ D₂ h₁ h₂ e
    (fun C hC ↦ hdeg C (hsupp _ hC).1 (hsupp _ hC).2) A

open Classical in
/-- **The fibre vanishing as intersection numbers.** On a component `E` over a curve, a
`ℚ`-divisor `M = ∑ c_P P` whose curve classes vanish on the components of the general fibres
satisfies `M · r^*H_Y · A = 0` and `M² · r^*H_Y = 0`. -/
theorem IsCurvePointExceptionalModel.sheafIntersectionNumber_pullback_eq_zero_of_fibre
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support)
    (hE : topologicalKrullDim (r.base '' (E.1.support : Set Z)) = 1)
    [IsProper (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))]
    (hd : topologicalKrullDim E.1.idealSheaf.subscheme ≤ (3 : ℕ))
    (π : MMP.Mori.PrimeDivisor E.1.idealSheaf.subscheme → E.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π P) (Finsupp.single P 1))
    (HY : Y.CartierDivisor) (A : E.1.idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible E.1.idealSheaf.subscheme.presheaf
      E.1.idealSheaf.subscheme.ringCatSheaf.2 A]
    (M : QDivisor E.1.idealSheaf.subscheme)
    (hvan : ∃ U : Y.Opens, ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty ∧
      ∀ y ∈ (U : Set Y) ∩ r.base '' (E.1.support : Set Z), IsClosed {y} →
        ∀ G : {V : MMP.Intersection.Scheme.Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          M.sum (fun P c ↦ c •
            ∑ᶠ (x : {x : G.1.toScheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (G.1.toScheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
              (_ : Maximal (fun A ↦ IsIrreducible A ∧
                  A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) = 0) :
    (M.sum fun P c ↦ c * (@sheafIntersectionNumber ℂ _ _ _
        (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) _ (𝟙 _) _ 3 hd
        ![MMP.CartierDivisor.sheaf (π P),
          (Scheme.Modules.pullback (E.1.idealSheaf.subschemeι ≫ r)).obj
            (MMP.CartierDivisor.sheaf HY), A]
        (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ)) = 0 ∧
    (M.sum fun P c ↦ M.sum fun Q c' ↦ c * c' * (@sheafIntersectionNumber ℂ _ _ _
        (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) _ (𝟙 _) _ 3 hd
        ![MMP.CartierDivisor.sheaf (π P), MMP.CartierDivisor.sheaf (π Q),
          (Scheme.Modules.pullback (E.1.idealSheaf.subschemeι ≫ r)).obj
            (MMP.CartierDivisor.sheaf HY)]
        (fun t ↦ by fin_cases t <;> dsimp <;> infer_instance) : ℚ)) = 0 := by
  exact ⟨hr.sum_sheafIntersectionNumber_pullback_eq_zero_of_fibre E hE hd π hπ HY A M hvan,
    sum_sum_sheafIntersectionNumber_eq_zero_of_forall ℂ _ hd π M _ fun L _ ↦
      hr.sum_sheafIntersectionNumber_pullback_eq_zero_of_fibre E hE hd π hπ HY L M hvan⟩

open Classical in
/-- **The fibre vanishing on a curve component, in the intersection forms**: for `M` with
vanishing curve classes on the general fibre components of `Fᵢ → r(Fᵢ)`, `M · H · A = 0` and
`M² · H = 0`. -/
theorem IsCurvePointExceptionalModel.lin_bGA_eq_zero_and_bilin_bB_eq_zero_of_fibre
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) [IsProper (Z ↘ Spec (.of ℂ))] [IsIntegral Z]
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (hdim : topologicalKrullDim Z = 4) (Hc Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor)
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)))
    (E : F.support) (hE : topologicalKrullDim (r.base '' (E.1.support : Set Z)) = 1)
    (M : QDivisor E.1.idealSheaf.subscheme)
    (hvan : ∃ U : Y.Opens, ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty ∧
      ∀ y ∈ (U : Set Y) ∩ r.base '' (E.1.support : Set Z), IsClosed {y} →
        ∀ G : {V : MMP.Intersection.Scheme.Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          M.sum (fun P c ↦ c •
            ∑ᶠ (x : {x : G.1.toScheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (G.1.toScheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
              (_ : Maximal (fun A ↦ IsIrreducible A ∧
                  A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) = 0) :
    Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc E) M = 0 ∧
      bilin (bB π Hh E) M M = 0 ∧
      ∀ L : E.1.idealSheaf.subscheme.Modules,
        [SheafOfModules.IsInvertible E.1.idealSheaf.subscheme.presheaf
          E.1.idealSheaf.subscheme.ringCatSheaf.2 L] →
        Finsupp.linearCombination ℚ (fun P => num3 E.1.idealSheaf.subscheme
          (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) (MMP.CartierDivisor.sheaf (π E P))
          ((Scheme.Modules.pullback E.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
          L) M = 0 := by
  have hd :=
    (MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.topologicalKrullDim_component hdim E).le
  have eHi : Nonempty ((Scheme.Modules.pullback E.1.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ (Scheme.Modules.pullback (E.1.idealSheaf.subschemeι ≫ r)).obj
        (MMP.CartierDivisor.sheaf HYc)) :=
    ⟨(Scheme.Modules.pullback _).mapIso eH.some ≪≫ (Scheme.Modules.pullbackComp _ _).app _⟩
  have hlin : ∀ L : E.1.idealSheaf.subscheme.Modules,
      [SheafOfModules.IsInvertible E.1.idealSheaf.subscheme.presheaf
        E.1.idealSheaf.subscheme.ringCatSheaf.2 L] →
      Finsupp.linearCombination ℚ (fun P => num3 E.1.idealSheaf.subscheme
          (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) (MMP.CartierDivisor.sheaf (π E P))
          ((Scheme.Modules.pullback E.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
          L) M = 0 := by
    intro L _
    rw [Finsupp.linearCombination_apply]
    refine Eq.trans ?_
      (hr.sheafIntersectionNumber_pullback_eq_zero_of_fibre E hE hd (π E) (hπ E) HYc L M hvan).1
    refine Finsupp.sum_congr fun P _ => ?_
    rw [smul_eq_mul, num3_congr _ _ _ _ _ _ _ ⟨Iso.refl _⟩ eHi ⟨Iso.refl _⟩, num3_eq _ _ _ _ hd]
  refine ⟨?_, ?_, hlin⟩
  · refine Eq.trans ?_ (hlin
      ((Scheme.Modules.pullback E.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
    unfold bGA
    exact congrArg (fun b => Finsupp.linearCombination ℚ b M) (funext fun P => num3_comm23 _ _ _ _)
  · rw [bilin_apply]
    refine Eq.trans ?_ (hr.sheafIntersectionNumber_pullback_eq_zero_of_fibre E hE hd (π E) (hπ E)
      HYc ((Scheme.Modules.pullback E.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hh)) M
      hvan).2
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => ?_
    unfold bB
    rw [num3_congr _ _ _ _ _ _ _ ⟨Iso.refl _⟩ ⟨Iso.refl _⟩ eHi, num3_eq _ _ _ _ hd]

end Fibre

section Assembly

variable {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}

/-- The standing geometry of a curve-and-point exceptional model: `Z` is a smooth projective
fourfold and `F` an snc divisor on it. -/
theorem IsCurvePointExceptionalModel.isVariety_and_isSmoothScheme
    (hr : IsCurvePointExceptionalModel sY r F D) :
    MMP.Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ)) ∧ MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)) ∧
      IsProjectiveMorphism (Z ↘ Spec (.of ℂ)) ∧ topologicalKrullDim Z = 4 ∧
      F.IsSNC (Z ↘ Spec (.of ℂ)) := by
  have hres := hr.isResolution
  have hcomp := hr.comp_eq
  haveI : MMP.Mori.IsVariety ℂ sY := hres.1
  haveI : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  refine ⟨hcomp ▸ hres.2.1, hcomp ▸ hres.2.2.1, hcomp ▸
    hres.2.2.2.1.comp ((MMP.Mori.isProjectiveVariety_iff _ _).1 hr.isProjectiveVariety).2, ?_,
    hcomp ▸ hr.isSNC⟩
  rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY)
    hres.2.2.2.2]
  exact hr.topologicalKrullDim_eq

/-- **The Cartier divisors of the kernel step.** On a curve-and-point exceptional model there
are Cartier divisors `εᵢ` with Weil divisor `Fᵢ`, Cartier divisors `π_P` on the components with
Weil divisor `P`, an ample Cartier divisor `H_Y` on `Y`, `H` on `Z` with `𝒪_Z(H) ≅ r^*𝒪_Y(H_Y)`,
and `A` on `Z` with `𝒪_Z(A + ∑ₗ mₗ εₗ) ≅ 𝒪_Z(N H)` (`A = N H - D`), ample on every closed
subscheme. -/
theorem IsCurvePointExceptionalModel.exists_cartierDivisor_isAmple
    (hr : IsCurvePointExceptionalModel sY r F D) :
    ∃ (ε : F.support → Z.CartierDivisor)
      (_ : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
      (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
        i.1.idealSheaf.subscheme.CartierDivisor)
      (_ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
      (Hc Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor) (N : ℕ),
      Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf HYc) ∧
      Nonempty (MMP.CartierDivisor.sheaf Hh ≅
        (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)) ∧
      Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, (D.coeff l.1).toNat • ε l) ≅
        MMP.CartierDivisor.sheaf (N • Hh)) ∧
      ∀ {W : Scheme.{0}} (g : W ⟶ Z) [IsClosedImmersion g],
        Stacks.Ample.IsAmple W ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf Hc)) := by
  classical
  obtain ⟨hvarZ, hsmZ, hZp, hdim, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI : IsIntegral Z := hvarZ.toIsIntegral
  haveI : CompactSpace Y := hr.compactSpace
  -- Cartier divisors of the Weil divisors on smooth varieties
  have hWC : ∀ (W : Scheme.{0}) [W.Over (Spec (.of ℂ))], MMP.Mori.IsVariety ℂ (W ↘ Spec (.of ℂ)) →
      MMP.Mori.IsSmoothScheme (W ↘ Spec (.of ℂ)) → ∀ w : Divisor W,
      ∃ A : W.CartierDivisor, MMP.Intersection.IsWeilDivisorOfCartier A w := by
    intro W _ hv hsm w
    haveI := hv
    haveI : IsIntegral W := hv.toIsIntegral
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (W ↘ Spec (.of ℂ))
    obtain ⟨A, hA⟩ := MMP.Resolution.Bridges.exists_isOrderAlong_of_weilDivisor
      (MMP.Intersection.uniqueFactorizationMonoid_stalk_of_isSmoothScheme hsm)
      (⟨⇑w, (mem_weilDivisor_iff _).mpr fun x =>
        ⟨Set.univ, Filter.univ_mem, w.support.finite_toSet.subset fun Z hZ => by
          by_cases h : w Z = 0
          · simp [h] at hZ
          · exact Finsupp.mem_support_iff.mpr h⟩⟩ : WeilDivisor W)
    exact ⟨A, hA⟩
  -- the Weil divisors of sums of Cartier divisors
  have hWadd : ∀ {W : Scheme.{0}} {A B : W.CartierDivisor} {v w : Divisor W},
      MMP.Intersection.IsWeilDivisorOfCartier A v →
      MMP.Intersection.IsWeilDivisorOfCartier B w →
      MMP.Intersection.IsWeilDivisorOfCartier (A + B) (v + w) := fun hA hB P => (hA P).add (hB P)
  have hWsum : ∀ {W : Scheme.{0}} {ι : Type} (s : Finset ι) {A : ι → W.CartierDivisor}
      {w : ι → Divisor W}, (∀ l ∈ s, MMP.Intersection.IsWeilDivisorOfCartier (A l) (w l)) →
      MMP.Intersection.IsWeilDivisorOfCartier (∑ l ∈ s, A l) (∑ l ∈ s, w l) := by
    intro W ι s A w hA
    induction s using Finset.induction_on with
    | empty =>
      intro P
      simpa using MMP.Intersection.isOrderAlong_zero (MMP.Intersection.primeDivisorSubvariety P)
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact hWadd (hA a (Finset.mem_insert_self a s))
        (ih fun l hl => hA l (Finset.mem_insert_of_mem hl))
  have hWnsmul : ∀ {W : Scheme.{0}} {A : W.CartierDivisor} {w : Divisor W} (m : ℕ),
      MMP.Intersection.IsWeilDivisorOfCartier A w →
      MMP.Intersection.IsWeilDivisorOfCartier (m • A) (m • w) := by
    intro W A w m hA
    have := hWsum (Finset.range m) (A := fun _ => A) (w := fun _ => w) fun _ _ => hA
    simpa using this
  choose ε hε using fun i : F.support => hWC Z hvarZ hsmZ (Finsupp.single i.1 1)
  have hXvar : ∀ i : F.support,
      MMP.Mori.IsVariety ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := fun i => by
    haveI := i.1.integral
    exact (⟨⟩ : AlgebraicGeometry.IsVariety ℂ (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)))
  choose π hπ using fun (i : F.support) (P : MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme) =>
    hWC _ (hXvar i) (hB.1 i.1 i.2) (Finsupp.single P 1)
  set n : F.support → ℕ := fun i => (D.coeff i.1).toNat with hn_def
  have hn : ∀ i, 0 < n i := fun i => Int.lt_toNat.2 (hr.coeff_pos i.1 i.2)
  -- `H = r^* H_Y` and `A = N H - D`
  obtain ⟨HY, hHY, hgen, H, -, hHYa, hHpb, N, hN⟩ := hr.exists_isAmple_nsmul_sub
  obtain ⟨hAc, -, hAres⟩ := hN N le_rfl
  haveI := hHY.isInvertibleModule_divisorialSheaf
  obtain ⟨HYc, ⟨eY⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf HY.divisorialSheaf
  obtain ⟨Hh, hHh⟩ := hWC Z hvarZ hsmZ H
  obtain ⟨Hc, hHc⟩ := hWC Z hvarZ hsmZ (N • H - D)
  have hM : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf HYc) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ eY).1 hHYa
  have eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)) :=
    ⟨hHh.nonempty_sheaf_iso_divisorialSheaf.some ≪≫
      Divisor.IsPullback.divisorialSheafIso (hBc := hHY) hHpb ≪≫
      (Scheme.Modules.pullback r).mapIso eY⟩
  have hD : D = ∑ l : F.support, n l • (Finsupp.single l.1 1 : Divisor Z) := by
    refine Finsupp.ext fun P => ?_
    rw [Finsupp.finset_sum_apply]
    by_cases hP : P ∈ F.support
    · rw [Finset.sum_eq_single (⟨P, hP⟩ : F.support) (fun l _ hl => by
        rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (fun h => hl (Subtype.ext h)),
          smul_zero]) (fun h => absurd (Finset.mem_univ _) h)]
      rw [Finsupp.smul_apply, Finsupp.single_eq_same, nsmul_eq_mul, mul_one, hn_def]
      simp only
      rw [Int.toNat_of_nonneg (hr.coeff_pos P hP).le]
      rfl
    · rw [Finset.sum_eq_zero fun l _ => by
        rw [Finsupp.smul_apply, Finsupp.single_apply,
          if_neg (fun (h : l.1 = P) => hP (h ▸ l.2)), smul_zero]]
      exact hr.coeff_eq_zero P hP
  obtain ⟨eHc⟩ := hHc.nonempty_sheaf_iso_divisorialSheaf
  have hAH : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, n l • ε l) ≅
      MMP.CartierDivisor.sheaf (N • Hh)) := by
    have h1 := hWadd hHc (hWsum Finset.univ fun l _ => hWnsmul (n l) (hε l))
    rw [← hD, sub_add_cancel] at h1
    exact ⟨h1.nonempty_sheaf_iso_divisorialSheaf.some ≪≫
      ((hWnsmul N hHh).nonempty_sheaf_iso_divisorialSheaf.some).symm⟩
  refine ⟨ε, hε, π, hπ, Hc, Hh, HYc, N, hM, eH, hAH, fun {W} g _ => ?_⟩
  haveI := hAc.isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((Scheme.Modules.pullback _).mapIso eHc.symm)).1 (hAres g)

/-- **`H` restricted to a component is the sheaf of a Cartier divisor with a Weil divisor.** -/
theorem IsCurvePointExceptionalModel.exists_isWeilDivisorOfCartier_iso_pullback
    (hr : IsCurvePointExceptionalModel sY r F D) (Hh : Z.CartierDivisor) (i : F.support) :
    ∃ (C : i.1.idealSheaf.subscheme.CartierDivisor) (w : Divisor i.1.idealSheaf.subscheme),
      MMP.Intersection.IsWeilDivisorOfCartier C w ∧
      Nonempty ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
        (MMP.CartierDivisor.sheaf Hh) ≅ MMP.CartierDivisor.sheaf C) := by
  obtain ⟨-, -, -, -, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI := i.1.integral
  obtain ⟨h2, h3⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme (hB.1 i.1 i.2)
  haveI : CompactSpace i.1.idealSheaf.subscheme :=
    i.1.idealSheaf.subschemeι.isClosedEmbedding.compactSpace
  obtain ⟨C, ⟨e⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
  haveI : IsNoetherian i.1.idealSheaf.subscheme := ⟨⟩
  obtain ⟨w, hw⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier C
  exact ⟨C, w, hw, ⟨e⟩⟩

/-- An element of `WithBot ℕ∞` at most `1` and different from `1` is at most `0`. -/
theorem withBot_enat_le_zero_of_le_one_of_ne_one {x : WithBot ℕ∞} (h1 : x ≤ 1) (h2 : x ≠ 1) :
    x ≤ 0 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe x =>
    have h1' : x ≤ 1 := by exact_mod_cast h1
    have h2' : x ≠ 1 := fun h => h2 (by rw [h]; rfl)
    exact_mod_cast (ENat.lt_one_iff_eq_zero.1 (lt_of_le_of_ne h1' h2')).le

/-- Every component of a curve-and-point exceptional model maps to a set of dimension at most
one. -/
theorem IsCurvePointExceptionalModel.topologicalKrullDim_range_le_one
    (hr : IsCurvePointExceptionalModel sY r F D) (i : F.support) :
    topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) ≤ 1 := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι]
  exact hr.topologicalKrullDim_image_le i.1 i.2

omit [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsComplexScheme Z] in
/-- A double surface maps into the image of its first component. -/
theorem topologicalKrullDim_range_dsIdeal_le (σ : DoubleSurface F) :
    topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤
      topologicalKrullDim (Set.range (σ.fstComponent.1.idealSheaf.subschemeι ≫ r).base) := by
  refine (Topology.IsEmbedding.inclusion ?_).isInducing.topologicalKrullDim_le
  rw [← sι_comp σ, Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact Set.image_subset_range _ _

/-- On a component over a point, the forms `x · H · A` and `x² · H` vanish. -/
theorem IsCurvePointExceptionalModel.lin_bGA_eq_zero_and_bilin_bB_eq_zero
    (hr : IsCurvePointExceptionalModel sY r F D) [IsProper (Z ↘ Spec (.of ℂ))]
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (Hc Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor)
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)))
    (i : F.support)
    (hi : ¬ topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) = 1)
    (x : QDivisor i.1.idealSheaf.subscheme) :
    Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) x = 0 ∧
      bilin (bB π Hh i) x x = 0 := by
  haveI := i.1.integral
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  obtain ⟨x₀⟩ := (inferInstance : Nonempty i.1.idealSheaf.subscheme)
  exact lin_bGA_eq_zero_and_bilin_bB_eq_zero_of_forall_eq π Hc Hh i _ _
    (exists_forall_base_eq_of_topologicalKrullDim_range_le_zero _
      (i.1.idealSheaf.subschemeι ≫ r).isClosedMap.isClosed_range
      (withBot_enat_le_zero_of_le_one_of_ne_one (hr.topologicalKrullDim_range_le_one i) hi) x₀)
    _ ⟨(Scheme.Modules.pullback _).mapIso eH.some ≪≫ (Scheme.Modules.pullbackComp _ _).app _⟩ x

/-- The rational `c₁` of `H|_{Fᵢ}` is that of its Weil divisor. -/
theorem IsCurvePointExceptionalModel.linearCombination_mapCoeff_eq
    (hr : IsCurvePointExceptionalModel sY r F D)
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hh : Z.CartierDivisor) (i : F.support) {C : i.1.idealSheaf.subscheme.CartierDivisor}
    {w : Divisor i.1.idealSheaf.subscheme} (hC : MMP.Intersection.IsWeilDivisorOfCartier C w)
    (e : Nonempty ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ MMP.CartierDivisor.sheaf C)) :
    Finsupp.linearCombination ℚ (fun Q =>
        singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (algebraicFirstChernClass (MMP.CartierDivisor.sheaf (π i Q)))) (Divisor.toQDivisor w) =
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
        ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (CartierDivisor.sheaf Hh))) := by
  obtain ⟨-, -, -, -, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI := i.1.integral
  obtain ⟨h2, h3⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme (hB.1 i.1 i.2)
  rw [algebraicFirstChernClass_eq_of_iso e.some]
  exact linearCombination_mapCoeff_algebraicFirstChernClass_toQDivisor (π i) (hπ i) hC

/-- `H|_{Fᵢ} · A² > 0` and `(H|_{Fᵢ})² · A = 0` on a component over a curve. -/
theorem IsCurvePointExceptionalModel.lin_bLam_pos_and_lin_bGA_eq_zero
    (hr : IsCurvePointExceptionalModel sY r F D) [IsProper (Z ↘ Spec (.of ℂ))]
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hc Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor)
    (hM : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf HYc))
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)))
    (hAmpW : ∀ {W : Scheme.{0}} (g : W ⟶ Z) [IsClosedImmersion g],
      Stacks.Ample.IsAmple W ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf Hc)))
    (i : F.support) {C : i.1.idealSheaf.subscheme.CartierDivisor}
    {w : Divisor i.1.idealSheaf.subscheme} (hC : MMP.Intersection.IsWeilDivisorOfCartier C w)
    (e : Nonempty ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ MMP.CartierDivisor.sheaf C))
    (hi : topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) = 1) :
    0 < Finsupp.linearCombination ℚ (bLam π Hc i) (Divisor.toQDivisor w) ∧
      Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) (Divisor.toQDivisor w) = 0 := by
  obtain ⟨hvarZ, -, -, hdim, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI : IsIntegral Z := hvarZ.toIsIntegral
  haveI := i.1.integral
  obtain ⟨h2, h3⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme (hB.1 i.1 i.2)
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY
    ((MMP.Mori.isProjectiveVariety_iff _ _).1 hr.isProjectiveVariety).2
  have eHi : Nonempty ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ (Scheme.Modules.pullback (i.1.idealSheaf.subschemeι ≫ r)).obj
        (MMP.CartierDivisor.sheaf HYc)) :=
    ⟨(Scheme.Modules.pullback _).mapIso eH.some ≪≫ (Scheme.Modules.pullbackComp _ _).app _⟩
  refine ⟨lin_bLam_toQDivisor_pos π sY r hr.comp_eq _ hM Hc i (hπ i) hC
      ⟨e.some.symm ≪≫ eHi.some⟩ (hAmpW _)
      (MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.topologicalKrullDim_component hdim i)
      (by rw [hi]; exact zero_lt_one),
    lin_bGA_toQDivisor_eq_zero π sY r hr.comp_eq _ Hc Hh i (hπ i) hC
      ⟨e.some.symm ≪≫ eHi.some⟩ eHi (hAmpW _)
      (MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.topologicalKrullDim_component hdim i)
      hi.le⟩

/-- `H|_{Fᵢ}|_S · A|_S = H|_S · A|_S ≥ 0` on every double surface `S` with first component
`Fᵢ`. -/
theorem IsCurvePointExceptionalModel.lin_bUA_eq_and_nonneg
    (hr : IsCurvePointExceptionalModel sY r F D) [IsProper (Z ↘ Spec (.of ℂ))]
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hc Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor)
    (hM : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf HYc))
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)))
    (hAmpW : ∀ {W : Scheme.{0}} (g : W ⟶ Z) [IsClosedImmersion g],
      Stacks.Ample.IsAmple W ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf Hc)))
    (σ : DoubleSurface F) {C : σ.fst.idealSheaf.subscheme.CartierDivisor}
    {w : Divisor σ.fst.idealSheaf.subscheme} (hC : MMP.Intersection.IsWeilDivisorOfCartier C w)
    (e : Nonempty ((Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ MMP.CartierDivisor.sheaf C)) :
    Finsupp.linearCombination ℚ (bUA π Hc σ) (Divisor.toQDivisor w) =
      num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
        ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)) ∧
    0 ≤ num2 (dsIdeal σ).subscheme ((dsIdeal σ).subschemeι ≫ Z ↘ Spec (.of ℂ))
        ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
        ((Scheme.Modules.pullback (dsIdeal σ).subschemeι).obj (MMP.CartierDivisor.sheaf Hc)) := by
  obtain ⟨hvarZ, -, -, hdim, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI : IsIntegral Z := hvarZ.toIsIntegral
  haveI := σ.fst.integral
  obtain ⟨h2, h3⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    (hB.1 σ.fst σ.fst_mem)
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY
    ((MMP.Mori.isProjectiveVariety_iff _ _).1 hr.isProjectiveVariety).2
  exact ⟨lin_bUA_toQDivisor_eq π Hc Hh σ (hπ _) hC e,
    num2_dsIdeal_pullback_nonneg sY r hr.comp_eq _ hM Hc Hh σ
      ⟨(Scheme.Modules.pullback _).mapIso eH.some ≪≫ (Scheme.Modules.pullbackComp _ _).app _⟩
      (hAmpW _) (topologicalKrullDim_dsIdeal hB hdim σ).le⟩

/-- `H|_S` is trivial on a double surface `S` over a point: `x|_S · H|_S = 0`. -/
theorem IsCurvePointExceptionalModel.lin_bUA_eq_zero_of_le_zero
    (hr : IsCurvePointExceptionalModel sY r F D) [IsProper (Z ↘ Spec (.of ℂ))]
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor)
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)))
    (σ : DoubleSurface F)
    (hσ : topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0)
    (x : QDivisor σ.fst.idealSheaf.subscheme) :
    Finsupp.linearCombination ℚ (bUA π Hh σ) x = 0 := by
  obtain ⟨-, -, -, -, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI := isIntegral_dsIdeal hB σ
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (dsIdeal σ).subscheme)
  have h0 : bUA π Hh σ = fun _ => 0 := funext fun P => by
    unfold bUA
    exact num2_eq_zero_of_forall_eq _ ((dsIdeal σ).subschemeι ≫ r) _
      (exists_forall_base_eq_of_topologicalKrullDim_range_le_zero _
        ((dsIdeal σ).subschemeι ≫ r).isClosedMap.isClosed_range hσ x₀) _ _ _
      ⟨(Scheme.Modules.pullback _).mapIso eH.some ≪≫ (Scheme.Modules.pullbackComp _ _).app _⟩
  rw [h0]
  simp [Finsupp.linearCombination_apply]

/-- `S · A · H = 0` on the first component of a double surface `S` over a point. -/
theorem IsCurvePointExceptionalModel.bGA_rho_eq_zero_of_le_zero
    (hr : IsCurvePointExceptionalModel sY r F D) [IsProper (Z ↘ Spec (.of ℂ))]
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hc Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor)
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)))
    (σ : DoubleSurface F) {C : σ.fst.idealSheaf.subscheme.CartierDivisor}
    {w : Divisor σ.fst.idealSheaf.subscheme} (hC : MMP.Intersection.IsWeilDivisorOfCartier C w)
    (e : Nonempty ((Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ MMP.CartierDivisor.sheaf C))
    (hσ : topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0) :
    bGA π (fun _ => Hh) Hc σ.fstComponent (rho hr.isVariety_and_isSmoothScheme.2.2.2.2 σ) = 0 := by
  obtain ⟨hvarZ, -, -, hdim, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI : IsIntegral Z := hvarZ.toIsIntegral
  haveI := σ.fst.integral
  obtain ⟨h2, h3⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    (hB.1 σ.fst σ.fst_mem)
  haveI := isIntegral_dsIdeal hB σ
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (dsIdeal σ).subscheme)
  have h1 := linearCombination_num3_toQDivisor (π σ.fstComponent) (hπ _) hC
    (σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
    (MMP.CartierDivisor.sheaf (π σ.fstComponent (rho hB σ)))
    ((Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc))
  have h2 : Finsupp.linearCombination ℚ (fun Q => num3 σ.fst.idealSheaf.subscheme
      (σ.fst.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) (CartierDivisor.sheaf (π σ.fstComponent Q))
      (MMP.CartierDivisor.sheaf (π σ.fstComponent (rho hB σ)))
      ((Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hc)))
      (Divisor.toQDivisor w) = Finsupp.linearCombination ℚ (bUA π Hc σ) (Divisor.toQDivisor w) :=
    congrArg (fun b => Finsupp.linearCombination ℚ b (Divisor.toQDivisor w))
      (funext fun P => (bUA_eq_bB hB hdim π hπ Hc σ P).symm)
  rw [h2, lin_bUA_toQDivisor_eq π Hc Hh σ (hπ _) hC e, num2_comm] at h1
  unfold bGA
  rw [num3_congr _ _ _ _ _ _ _ ⟨Iso.refl _⟩ ⟨Iso.refl _⟩ e, num3_comm23, num3_comm12, ← h1]
  exact num2_eq_zero_of_forall_eq _ ((dsIdeal σ).subschemeι ≫ r) _
    (exists_forall_base_eq_of_topologicalKrullDim_range_le_zero _
      ((dsIdeal σ).subschemeι ≫ r).isClosedMap.isClosed_range hσ x₀) _ _ _
    ⟨(Scheme.Modules.pullback _).mapIso eH.some ≪≫ (Scheme.Modules.pullbackComp _ _).app _⟩

omit [Z.Over (Spec (.of ℂ))] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
  [IsComplexScheme Z] in
/-- The form `x · y · H` is symmetric. -/
theorem bilin_bB_comm [Z.Over (Spec (.of ℂ))] [IsProper (Z ↘ Spec (.of ℂ))]
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor) (H : Z.CartierDivisor) (i : F.support)
    (x y : QDivisor i.1.idealSheaf.subscheme) :
    bilin (bB π H i) x y = bilin (bB π H i) y x := by
  rw [bilin_apply, bilin_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => ?_
  unfold bB
  rw [num3_comm12]
  ring

open Classical in
/-- **A point-edge system is invisible to `H`**: for `a` supported on the double surfaces over
points, `Zᵢ(a) · A · H = 0` and `x · Zᵢ(a) · H = 0`, given the expansion of linear forms on the
`Zᵢ(a)` along the double surfaces. -/
theorem IsCurvePointExceptionalModel.lin_bGA_eq_zero_and_bilin_bB_eq_zero_of_pointEdges
    (hr : IsCurvePointExceptionalModel sY r F D) [IsProper (Z ↘ Spec (.of ℂ))]
    [Fintype (DoubleSurface F)]
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hc Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor)
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)))
    (CH : ∀ i : F.support, i.1.idealSheaf.subscheme.CartierDivisor)
    (wH : ∀ i : F.support, Divisor i.1.idealSheaf.subscheme)
    (hwH : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (CH i) (wH i))
    (eCH : ∀ i, Nonempty ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ MMP.CartierDivisor.sheaf (CH i)))
    (hZlin : ∀ (f : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme →ₗ[ℚ] ℚ)
      (a : DoubleSurface F → ℚ),
      ∑ i, f i (surfaceCoefficientDivisor a i.1) =
        ∑ σ : DoubleSurface F, a σ * f σ.fstComponent
          (Finsupp.single (rho hr.isVariety_and_isSmoothScheme.2.2.2.2 σ) 1))
    (a : DoubleSurface F → ℚ)
    (hapt : ∀ σ, ¬ topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 →
      a σ = 0) :
    (∀ i : F.support, Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i)
      (surfaceCoefficientDivisor a i.1) = 0) ∧
    ∀ (i : F.support) (x : QDivisor i.1.idealSheaf.subscheme),
      bilin (bB π Hh i) x (surfaceCoefficientDivisor a i.1) = 0 := by
  obtain ⟨-, -, -, hdim, hB⟩ := hr.isVariety_and_isSmoothScheme
  have hvar := hr.isVariety_and_isSmoothScheme.1
  haveI : IsIntegral Z := hvar.toIsIntegral
  have hpt' : ∀ σ, a σ ≠ 0 →
      topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 :=
    fun σ h => by_contra fun h' => h (hapt σ h')
  refine ⟨fun i => ?_, fun i x => ?_⟩
  · have h := hZlin (fun j => if j = i then
      Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc j) else 0) a
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg hj, LinearMap.zero_apply])
      (fun h => absurd (Finset.mem_univ i) h), if_pos rfl] at h
    rw [h]
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases ha : a σ = 0
    · rw [ha, zero_mul]
    · split_ifs with h'
      · subst h'
        rw [Finsupp.linearCombination_single, one_smul,
          hr.bGA_rho_eq_zero_of_le_zero π hπ Hc Hh HYc eH σ (hwH σ.fstComponent)
            (eCH σ.fstComponent) (hpt' σ ha), mul_zero]
      · rw [LinearMap.zero_apply, mul_zero]
  · have h := hZlin (fun j => bilin (bB π Hh j)
      (@Pi.single _ (fun j : F.support => QDivisor j.1.idealSheaf.subscheme) _ _ i x j)) a
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero,
      LinearMap.zero_apply]) (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same] at h
    rw [h]
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases ha : a σ = 0
    · rw [ha, zero_mul]
    · have e : ∀ y : QDivisor σ.fst.idealSheaf.subscheme, bilin (bB π Hh σ.fstComponent) y
          (Finsupp.single (rho hB σ) 1) = Finsupp.linearCombination ℚ (bUA π Hh σ) y := by
        intro y
        have e1 : bilin (bB π Hh σ.fstComponent) y (Finsupp.single (rho hB σ) 1) =
            Finsupp.linearCombination ℚ (fun P => bB π Hh σ.fstComponent P (rho hB σ)) y := by
          simp [bilin, Finsupp.linearCombination_apply, Finsupp.sum]
        rw [e1]
        exact congrArg (fun b => Finsupp.linearCombination ℚ b y)
          (funext fun P => (bUA_eq_bB hB hdim π hπ Hh σ P).symm)
      rw [e, hr.lin_bUA_eq_zero_of_le_zero π Hh HYc eH σ (hpt' σ ha), mul_zero]

open Classical in
/-- **The vanishing on the general fibres, in the intersection forms.** If the curve classes of
the `L'ᵢ` vanish on the general fibre components over every singular curve, then for every
oriented system `a` on the point edges, `(L' - Z(a))ᵢ · H · A = 0` and `(L' - Z(a))ᵢ² · H = 0` on
the curve components, and `(L' - Z(a))ᵢ|_S · H|_S = 0` on the double surfaces over curves. -/
theorem IsCurvePointExceptionalModel.forall_lin_bGA_sub_eq_zero_of_fibre
    (hr : IsCurvePointExceptionalModel sY r F D) [IsProper (Z ↘ Spec (.of ℂ))]
    [Fintype (DoubleSurface F)]
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hc Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor)
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)))
    (CH : ∀ i : F.support, i.1.idealSheaf.subscheme.CartierDivisor)
    (wH : ∀ i : F.support, Divisor i.1.idealSheaf.subscheme)
    (hwH : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (CH i) (wH i))
    (eCH : ∀ i, Nonempty ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ MMP.CartierDivisor.sheaf (CH i)))
    (hZlin : ∀ (f : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme →ₗ[ℚ] ℚ)
      (a : DoubleSurface F → ℚ),
      ∑ i, f i (surfaceCoefficientDivisor a i.1) =
        ∑ σ : DoubleSurface F, a σ * f σ.fstComponent
          (Finsupp.single (rho hr.isVariety_and_isSmoothScheme.2.2.2.2 σ) 1))
    (L' : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme)
    (hfib : ∀ T : IrreducibleCloseds Y, (T : Set Y) ⊆ (singularLocus sY : Set Y) →
      topologicalKrullDim (T : Set Y) = 1 →
      ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, IsClosed {y} →
        ∀ (E : F.support)
          (G : {V : MMP.Intersection.Scheme.Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          (L' E).sum (fun P c ↦ c •
            ∑ᶠ (x : {x : G.1.toScheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (G.1.toScheme ↘ Spec (.of ℂ)) x = ((1 : ℕ) : ℤ)})
              (_ : Maximal (fun A ↦ IsIrreducible A ∧
                  A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) = 0) :
    ∀ a ∈ orientedSurfaceCoefficients F,
      (∀ σ, ¬ topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 → a σ = 0) →
      (∀ i, topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) = 1 →
        Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i)
          (L' i - surfaceCoefficientDivisor a i.1) = 0 ∧
        bilin (bB π Hh i) (L' i - surfaceCoefficientDivisor a i.1)
          (L' i - surfaceCoefficientDivisor a i.1) = 0) ∧
      ∀ σ, ¬ topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 →
        Finsupp.linearCombination ℚ (bUA π Hh σ)
          (L' σ.fstComponent - surfaceCoefficientDivisor a σ.fst) = 0 := by
  intro a _ hapt
  obtain ⟨hvarZ, -, -, hdim, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI : IsIntegral Z := hvarZ.toIsIntegral
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  obtain ⟨hZ1, hZ2⟩ := hr.lin_bGA_eq_zero_and_bilin_bB_eq_zero_of_pointEdges π hπ Hc Hh HYc eH
    CH wH hwH eCH hZlin a hapt
  -- the fibre vanishing on a curve component
  have hEf : ∀ i : F.support,
      topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) = 1 →
      Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i) (L' i) = 0 ∧
      bilin (bB π Hh i) (L' i) (L' i) = 0 ∧
      ∀ L : i.1.idealSheaf.subscheme.Modules,
        [SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
          i.1.idealSheaf.subscheme.ringCatSheaf.2 L] →
        Finsupp.linearCombination ℚ (fun P => num3 i.1.idealSheaf.subscheme
          (i.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) (MMP.CartierDivisor.sheaf (π i P))
          ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj (MMP.CartierDivisor.sheaf Hh))
          L) (L' i) = 0 := by
    intro i hi
    have hrange : Set.range (i.1.idealSheaf.subschemeι ≫ r).base =
        r.base '' (i.1.support : Set Z) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.IdealSheafData.range_subschemeι]
    have hirr : IsIrreducible (r.base '' (i.1.support : Set Z)) := by
      refine IsIrreducible.image ?_ _ r.base.hom.continuous.continuousOn
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    have hcl : IsClosed (r.base '' (i.1.support : Set Z)) :=
      hrange ▸ (i.1.idealSheaf.subschemeι ≫ r).isClosedMap.isClosed_range
    let T : IrreducibleCloseds Y := ⟨r.base '' (i.1.support : Set Z), hirr, hcl⟩
    have hTs : (T : Set Y) ⊆ (singularLocus sY : Set Y) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ (F.supp : Set Z) :=
        MMP.Mori.DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 i.2) hx
      rw [hr.supp_eq_preimage_singularLocus] at hx'
      exact hx'
    have hE : topologicalKrullDim (r.base '' (i.1.support : Set Z)) = 1 := hrange ▸ hi
    obtain ⟨U, hU, h⟩ := hfib T hTs hE
    exact hr.lin_bGA_eq_zero_and_bilin_bB_eq_zero_of_fibre π hπ hdim Hc Hh HYc eH i hE (L' i)
      ⟨U, hU, fun y hy hyc G hG => h y hy hyc i G hG⟩
  refine ⟨fun i hi => ?_, fun σ hσ => ?_⟩
  · obtain ⟨f1, f2, -⟩ := hEf i hi
    refine ⟨by rw [map_sub, f1, hZ1, sub_zero], ?_⟩
    rw [map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply,
      bilin_bB_comm π Hh i (surfaceCoefficientDivisor a i.1) (L' i)]
    simp only [f2, hZ2, sub_zero]
  · have hcur : topologicalKrullDim
        (Set.range (σ.fstComponent.1.idealSheaf.subschemeι ≫ r).base) = 1 := by
      by_contra h
      exact hσ ((topologicalKrullDim_range_dsIdeal_le σ).trans
        (withBot_enat_le_zero_of_le_one_of_ne_one (hr.topologicalKrullDim_range_le_one _) h))
    obtain ⟨-, -, f3⟩ := hEf σ.fstComponent hcur
    have e : ∀ y, Finsupp.linearCombination ℚ (bUA π Hh σ) y =
        bilin (bB π Hh σ.fstComponent) y (Finsupp.single (rho hB σ) 1) := by
      intro y
      have e1 : bilin (bB π Hh σ.fstComponent) y (Finsupp.single (rho hB σ) 1) =
          Finsupp.linearCombination ℚ (fun P => bB π Hh σ.fstComponent P (rho hB σ)) y := by
        simp [bilin, Finsupp.linearCombination_apply, Finsupp.sum]
      rw [e1]
      exact congrArg (fun b => Finsupp.linearCombination ℚ b y)
        (funext fun P => bUA_eq_bB hB hdim π hπ Hh σ P)
    rw [map_sub, e, e, bilin_bB_comm π Hh σ.fstComponent (surfaceCoefficientDivisor a σ.fst),
      hZ2, sub_zero]
    have f := f3 (MMP.CartierDivisor.sheaf (π σ.fstComponent (rho hB σ)))
    refine Eq.trans ?_ f
    rw [← e]
    refine congrArg (fun b => Finsupp.linearCombination ℚ b _) (funext fun P => ?_)
    rw [bUA_eq_bB hB hdim π hπ Hh σ P]
    unfold bB
    exact num3_comm23 _ _ _ _

open Classical in
/-- **The Hodge index argument on a curve-and-point exceptional model.** With the Cartier
divisors of `MMP.Fourfold.IsCurvePointExceptionalModel.exists_cartierDivisor_isAmple`, a family
`L` of `ℚ`-divisors on the components with zero ambient class whose intersection numbers with `H`
vanish on the curve components and the double surfaces over curves (after subtracting any
oriented system on the point edges) is, up to divisors of class zero, `Z(a)` for an oriented
system `a`. -/
theorem IsCurvePointExceptionalModel.exists_mem_orientedSurfaceCoefficients_forall_sub_mem
    (hr : IsCurvePointExceptionalModel sY r F D) [IsProper (Z ↘ Spec (.of ℂ))]
    [Fintype (DoubleSurface F)]
    (ε : F.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : F.support, MMP.Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (Hc Hh : Z.CartierDivisor) (HYc : Y.CartierDivisor) (N : ℕ)
    (hM : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf HYc))
    (eH : Nonempty (MMP.CartierDivisor.sheaf Hh ≅
      (Scheme.Modules.pullback r).obj (MMP.CartierDivisor.sheaf HYc)))
    (hAH : Nonempty (MMP.CartierDivisor.sheaf (Hc + ∑ l : F.support, (D.coeff l.1).toNat • ε l) ≅
      MMP.CartierDivisor.sheaf (N • Hh)))
    (hAmpW : ∀ {W : Scheme.{0}} (g : W ⟶ Z) [IsClosedImmersion g],
      Stacks.Ample.IsAmple W ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf Hc)))
    (CH : ∀ i : F.support, i.1.idealSheaf.subscheme.CartierDivisor)
    (wH : ∀ i : F.support, Divisor i.1.idealSheaf.subscheme)
    (hwH : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (CH i) (wH i))
    (eCH : ∀ i, Nonempty ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf Hh) ≅ MMP.CartierDivisor.sheaf (CH i)))
    (hZlin : ∀ (f : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme →ₗ[ℚ] ℚ)
      (a : DoubleSurface F → ℚ),
      ∑ i, f i (surfaceCoefficientDivisor a i.1) =
        ∑ σ : DoubleSurface F, a σ * f σ.fstComponent
          (Finsupp.single (rho hr.isVariety_and_isSmoothScheme.2.2.2.2 σ) 1))
    (L' : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme)
    (hL' : ∑ i : F.support, componentHomologyMap i.1 4
      (MMP.Chow.divisorClass i.1.idealSheaf.subscheme (L' i)) = 0)
    (hvan : ∀ a ∈ orientedSurfaceCoefficients F,
      (∀ σ, ¬ topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 → a σ = 0) →
      (∀ i, topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) = 1 →
        Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i)
          (L' i - surfaceCoefficientDivisor a i.1) = 0 ∧
        bilin (bB π Hh i) (L' i - surfaceCoefficientDivisor a i.1)
          (L' i - surfaceCoefficientDivisor a i.1) = 0) ∧
      ∀ σ, ¬ topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 →
        Finsupp.linearCombination ℚ (bUA π Hh σ)
          (L' σ.fstComponent - surfaceCoefficientDivisor a σ.fst) = 0) :
    ∃ a ∈ orientedSurfaceCoefficients F,
      ∀ i, L' i - surfaceCoefficientDivisor a i.1 ∈
        LinearMap.ker (MMP.Chow.divisorClass i.1.idealSheaf.subscheme) := by
  obtain ⟨hvarZ, hsmZ, hZp, hdim, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI : IsIntegral Z := hvarZ.toIsIntegral
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY
    ((MMP.Mori.isProjectiveVariety_iff _ _).1 hr.isProjectiveVariety).2
  have hBred : ∀ E ∈ F.support, F E = 1 := fun E hE =>
    (hr.isReducedEffective E).resolve_left (Finsupp.mem_support_iff.1 hE)
  have hn : ∀ i : F.support, 0 < (D.coeff i.1).toNat := fun i =>
    Int.lt_toNat.2 (hr.coeff_pos i.1 i.2)
  let Zl : (DoubleSurface F → ℚ) →ₗ[ℚ]
      (∀ i : F.support, MMP.Mori.QDivisor i.1.idealSheaf.subscheme) :=
    LinearMap.pi fun i => surfaceCoefficientDivisorLinearMap F i.1
  have hZl : ∀ a i, Zl a i = surfaceCoefficientDivisor a i.1 := fun _ _ => rfl
  have hRA : ∀ (σ : DoubleSurface F) x, Finsupp.linearCombination ℚ (bUA π Hc σ) x =
      bilin (bB π Hc σ.fstComponent) x (Finsupp.single (rho hB σ) 1) := by
    intro σ x
    have e : bilin (bB π Hc σ.fstComponent) x (Finsupp.single (rho hB σ) 1) =
        Finsupp.linearCombination ℚ (fun P => bB π Hc σ.fstComponent P (rho hB σ)) x := by
      simp [bilin, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [e]
    exact congrArg (fun b => Finsupp.linearCombination ℚ b x)
      (funext fun P => bUA_eq_bB hB hdim π hπ Hc σ P)
  have hptc : ∀ σ : DoubleSurface F,
      ¬ topologicalKrullDim (Set.range (σ.fstComponent.1.idealSheaf.subschemeι ≫ r).base) = 1 →
      topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 := fun σ h =>
    (topologicalKrullDim_range_dsIdeal_le σ).trans
      (withBot_enat_le_zero_of_le_one_of_ne_one (hr.topologicalKrullDim_range_le_one _) h)
  have hcurS : ∀ σ : DoubleSurface F,
      ¬ topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 →
      topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) = 1 := fun σ h => by
    by_contra h'
    exact h (withBot_enat_le_zero_of_le_one_of_ne_one
      ((topologicalKrullDim_range_dsIdeal_le σ).trans (hr.topologicalKrullDim_range_le_one _)) h')
  obtain ⟨a, ha, -, hK⟩ := exists_mem_orientedSurfaceCoefficients_forall_sub_mem_of_isotropic hB
    hdim hvarZ hsmZ hZp hBred ε hε π hπ Hc Hh (fun i => (D.coeff i.1).toNat) hn N hAH
    (fun i => hAmpW _) (fun σ => hAmpW _) sY r hr.comp_eq (MMP.CartierDivisor.sheaf HYc) hM eH
    (fun i => topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) = 1)
    (fun σ => topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0)
    (fun _ => Iff.rfl) hptc (fun _ h => h) hcurS (fun _ h => h)
    (fun i => Divisor.toQDivisor (wH i))
    (fun i _ => hr.linearCombination_mapCoeff_eq π hπ Hh i (hwH i) (eCH i))
    Zl hZl (fun σ => Finsupp.single (rho hB σ) 1) hZlin hRA
    (fun i hi x => hr.lin_bGA_eq_zero_and_bilin_bB_eq_zero π Hc Hh HYc eH i hi x)
    (fun i _ x hx => by
      obtain ⟨h1, h2⟩ := MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.threefold_index
        hB hdim π hπ hZp Hc i (hAmpW _) x hx
      exact ⟨h1, fun h => LinearMap.mem_ker.2 (h2 h)⟩)
    (fun σ _ x y hxy => MMP.Fold06.ThmMmpConductorIsolatedPointAlgebraicKernel.surface_index
      hB hdim π hZp Hc σ (hAmpW _) x y hxy)
    (fun i hi => (hr.lin_bLam_pos_and_lin_bGA_eq_zero π hπ Hc Hh HYc hM eH hAmpW i (hwH i)
      (eCH i) hi).1)
    (fun i hi => (hr.lin_bLam_pos_and_lin_bGA_eq_zero π hπ Hc Hh HYc hM eH hAmpW i (hwH i)
      (eCH i) hi).2)
    (fun σ => ((hr.lin_bUA_eq_and_nonneg π hπ Hc Hh HYc hM eH hAmpW σ (hwH σ.fstComponent)
        (eCH σ.fstComponent)).1).trans
      ((hr.lin_bUA_eq_and_nonneg π hπ Hc Hh HYc hM eH hAmpW σ.swap
        (hwH σ.sndComponent) (eCH σ.sndComponent)).1).symm)
    (fun σ => by
      rw [(hr.lin_bUA_eq_and_nonneg π hπ Hc Hh HYc hM eH hAmpW σ (hwH σ.fstComponent)
        (eCH σ.fstComponent)).1]
      exact (hr.lin_bUA_eq_and_nonneg π hπ Hc Hh HYc hM eH hAmpW σ (hwH σ.fstComponent)
        (eCH σ.fstComponent)).2)
    L' hL' hvan
  exact ⟨a, ha, hK⟩

open Classical in
/-- **The kernel step.** Let `r : Z ⟶ Y` be a curve-and-point exceptional model and `Lᵢ`
`ℚ`-divisors on the components `Fᵢ` of `F` with `∑ᵢ (ιᵢ)_*[Lᵢ] = 0` in `H_4(Z, ℚ)`, such that for
every singular curve `T ⊆ Y` the fibre cycle `∑ᵢ ∑_P c_P [P ×_Y t]` has class zero in the homology
of the fibre over every point `t` of a dense open of `T`. Then `([Lᵢ])ᵢ` lies in the space
`B(r)` of class tuples of oriented double-surface systems. -/
theorem IsCurvePointExceptionalModel.mem_orientedSurfaceClasses_of_fibre_vanishing
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) :
    (∀ L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme,
      ∑ E : F.support, componentHomologyMap E.1 4 (MMP.Chow.divisorClass _ (L E)) = 0 →
      (∀ T : IrreducibleCloseds Y, (T : Set Y) ⊆ (singularLocus sY : Set Y) →
          topologicalKrullDim (T : Set Y) = 1 →
        ∃ U : (curveScheme T).Opens, Dense (U : Set (curveScheme T)) ∧
          ∀ (t : ComplexPoints (U.ι ≫ curveι T ≫ sY))
            [IsComplexScheme (pointFibre sY r U t)],
            Chow.rationalCycleClass (pointFibre sY r U t) 1
              (∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
                (1 : ℚ) ⊗ₜ[ℤ] @Stacks.Chow.cycleAssociatedToClosedSubscheme
                  (Stacks.Chow.fieldChowSituation ℂ) _ _ (pointFibre sY r U t ↘ Spec (.of ℂ)) _
                  (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r)
                    (t.hom ≫ U.ι ≫ curveι T) r (t.hom ≫ U.ι ≫ curveι T)
                    (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
                    ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
                    ((Category.comp_id _).trans (Category.id_comp _).symm))
                  (isClosedImmersion_pullback_map_of_comp_eq
                    (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _)
                    (t.hom ≫ U.ι ≫ curveι T)) ((1 : ℕ) : ℤ)) = 0) →
      (fun E => MMP.Chow.divisorClass E.1.idealSheaf.subscheme (L E) : ComponentHomology F) ∈
        orientedSurfaceClasses F) := by
  intro L hL hfib
  classical
  obtain ⟨hvarZ, hsmZ, hZp, hdim, hB⟩ := hr.isVariety_and_isSmoothScheme
  haveI : IsIntegral Z := hvarZ.toIsIntegral
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := isProper_of_isProjectiveMorphism _ hZp
  haveI : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  haveI : Fintype (DoubleSurface F) := @Fintype.ofFinite _ (DoubleSurface.finite (B := F))
  obtain ⟨ε, hε, π, hπ, Hc, Hh, HYc, N, hM, eH, hAH, hAmpW⟩ := hr.exists_cartierDivisor_isAmple
  choose CH wH hwH eCH using hr.exists_isWeilDivisorOfCartier_iso_pullback Hh
  -- remove the generic classes
  have hw := fun T hTs hT1 ↦ hr.exists_opens_sum_rationalCycleClass_eq_zero L T hT1 (hfib T hTs hT1)
  have hLK : (fun E ↦ MMP.Chow.divisorClass E.1.idealSheaf.subscheme (L E) : ComponentHomology F) ∈
      algebraicKernel F :=
    (mem_exceptionalKernel F).2 ⟨fun E => LinearMap.mem_range_self _ _, hL⟩
  obtain ⟨a₀, ha₀, -, ha₀K, ha₀van⟩ := hr.exists_mem_orientedSurfaceCoefficients_sub L hLK hw
  set L' : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme :=
    fun E => L E - surfaceCoefficientDivisor a₀ E.1 with hL'_def
  have hL' : ∑ i : F.support, componentHomologyMap i.1 4
      (MMP.Chow.divisorClass i.1.idealSheaf.subscheme (L' i)) = 0 :=
    ((mem_exceptionalKernel F).1 ha₀K).2
  have hZlin : ∀ (f : ∀ i : F.support, QDivisor i.1.idealSheaf.subscheme →ₗ[ℚ] ℚ)
      (a : DoubleSurface F → ℚ),
      ∑ i, f i (surfaceCoefficientDivisor a i.1) =
        ∑ σ : DoubleSurface F, a σ * f σ.fstComponent
          (Finsupp.single (rho hr.isVariety_and_isSmoothScheme.2.2.2.2 σ) 1) :=
    fun f a => sum_apply_surfaceCoefficientDivisor hB f a
  -- the vanishing on the general fibres, as intersection numbers
  have hvan : ∀ a ∈ orientedSurfaceCoefficients F,
      (∀ σ, ¬ topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 → a σ = 0) →
      (∀ i, topologicalKrullDim (Set.range (i.1.idealSheaf.subschemeι ≫ r).base) = 1 →
        Finsupp.linearCombination ℚ (bGA π (fun _ => Hh) Hc i)
          (L' i - surfaceCoefficientDivisor a i.1) = 0 ∧
        bilin (bB π Hh i) (L' i - surfaceCoefficientDivisor a i.1)
          (L' i - surfaceCoefficientDivisor a i.1) = 0) ∧
      ∀ σ, ¬ topologicalKrullDim (Set.range ((dsIdeal σ).subschemeι ≫ r).base) ≤ 0 →
        Finsupp.linearCombination ℚ (bUA π Hh σ)
          (L' σ.fstComponent - surfaceCoefficientDivisor a σ.fst) = 0 :=
    hr.forall_lin_bGA_sub_eq_zero_of_fibre π hπ Hc Hh HYc eH CH wH hwH eCH hZlin L' ha₀van
  obtain ⟨a, ha, hK⟩ := hr.exists_mem_orientedSurfaceCoefficients_forall_sub_mem ε hε π hπ Hc Hh
    HYc N hM eH hAH hAmpW CH wH hwH eCH hZlin L' hL' hvan
  -- the class tuple is that of the oriented system `a₀ + a`
  refine (mem_orientedSurfaceClasses F).2 ⟨a₀ + a, add_mem ha₀ ha, fun E => ?_⟩
  have h := LinearMap.mem_ker.1 (hK E)
  rw [hL'_def] at h
  simp only [map_sub] at h
  rw [show surfaceCoefficientDivisor (a₀ + a) E.1 = surfaceCoefficientDivisor a₀ E.1 +
    surfaceCoefficientDivisor a E.1 from (surfaceCoefficientDivisorLinearMap F E.1).map_add a₀ a,
    map_add]
  rw [sub_sub, sub_eq_zero] at h
  exact h

end Assembly

end MMP.Fourfold
