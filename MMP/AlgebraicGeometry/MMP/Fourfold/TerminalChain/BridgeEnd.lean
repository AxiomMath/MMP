module

public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas

/-!
# The bridge from the decreased pair to the next model of a terminal chain

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt tail of fourfolds with stable
low-discrepancy set `I_∞`, let `(p_i, Θ_i)`, `p_i : Y_i ⟶ X_i`, be a crepant junction of
`(X_i, B_i)` extracting `I_∞`, and let `Θ_i'` be its decreased boundary. Run a finite relative
program over `Z_i` (via `f_i ∘ p_i`) from `(Y_i, Θ_i')`, with end `(V_m, Θ_m)` and composite
birational map `ψ : Y_i ⤏ V_m`, and suppose that `K_{V_m} + Θ_m` is nef over `Z_i`.

* The birational map `V_m ⤏ X_{i+1}` is a morphism `p̂ : V_m ⟶ X_{i+1}`, and it is crepant:
  `K_{V_m} + Θ_m = p̂^*(K_{X_{i+1}} + B_{i+1})`. Write `q_k : W ⟶ V_k` and `r : W ⟶ X_{i+1}` for
  a common resolution. The pull-back `q_0^*(K_{Y_i} + Θ_i')` exceeds both
  `q_m^*(K_{V_m} + Θ_m)` and `r^*(K_{X_{i+1}} + B_{i+1})` by effective divisors that are
  exceptional over `V_m` and `X_{i+1}` respectively. Since `K_{X_{i+1}} + B_{i+1}` is ample over
  `Z_i`, the comparison of two nef ends produces `p̂` with `r = p̂ ∘ q_m`.
* Every contraction `g_k : V_k ⟶ T_k`, `k < m`, of the program is small. If some `g_k` were
  divisorial, it would contract a prime `P` of `V_k` that is the strict transform of a prime `P₀`
  of `Y_i`. If `P₀ = E_{i,s}`, the log discrepancy of `s` increases strictly at step `k` from its
  starting value `a_{i+1}(s)`, while the crepant morphism `p̂` forces the final value to be
  `a_{i+1}(s)`. Otherwise `ord_{P₀}` is the valuation of a prime of `X_{i+1}`, so its centre on
  `V_m`, and hence on `V_{k+1}`, is a divisor.
* `(p̂, Θ_m)` is a crepant junction of `(X_{i+1}, B_{i+1})` extracting `I_∞`. Every step of the
  program is small, so strict transform is a bijection between the primes of `Y_i` and those of
  `V_m`, and `Θ_m` is the strict transform of `Θ_i'`. The primes of `Y_i` are the `E_{i,s}`,
  `s ∈ I_∞`, which are exceptional over `X_{i+1}`, and the strict transforms of primes of `X_i`,
  which are not. Hence `s ↦ c_{V_m}(s)` is a bijection from `I_∞` onto the `p̂`-exceptional
  primes, and `Θ_m = p̂⁻¹_* B_{i+1} + ∑_s (1 - a_{i+1}(s)) c_{V_m}(s)`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.IsDecreasedBoundary.exists_isPullback_of_isRelativelyNef`:
  the morphism `p̂ : V_m ⟶ X_{i+1}` and the crepant identity.
* `MMP.Fourfold.StabilizedSmallKltTail.IsDecreasedBoundary.isSmallMorphism_of_isRelativelyNef`:
  every contraction of the program is a small morphism.
* `MMP.Fourfold.StabilizedSmallKltTail.IsDecreasedBoundary.exists_fourfoldCrepantJunction_of_isPullback`:
  `(p̂, Θ_m)` is a crepant junction of `(X_{i+1}, B_{i+1})` extracting `I_∞`.

## Implementation notes

* The birational map `V_m ⤏ X_{i+1}` is `(f_i⁺)⁻¹ ∘ f_i ∘ p_i ∘ ψ⁻¹`. That `p̂` represents it is
  stated as `f_i⁺ ∘ p̂ ∘ ψ = f_i ∘ p_i` as rational maps `Y_i ⤏ Z_i`, the convention of
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalBridge`; this is equivalent because `f_i⁺` is
  birational.
* The canonical divisor `K_{X_{i+1}}` is the push-forward `p̂_* K_{V_m}` of the canonical
  divisor of the end of the program. This is the canonical divisor of `X_{i+1}` cut out by the
  same rational top form as `K_{V_m}`, which is the compatible choice the identity requires.
* The crepant identity is the `ℚ`-Cartier pull-back `MMP.Mori.QDivisor.IsPullback`. The support
  condition of the pull-back is part of the conclusion.
* A crepant junction `MMP.Fourfold.FourfoldCrepantJunction` bundles its source. That `(p̂, Θ_m)`
  is one is therefore stated up to isomorphism: there is a junction `(p', Θ')`,
  `p' : Y' ⟶ X_{i+1}`, extracting a finite set `I'` equal to the image of `I_∞` in the valuations
  of `k(X_{i+1})`, and an isomorphism `e : V_m ≅ Y'` over `ℂ` with `p' ∘ e = p̂` and
  `Θ_m = e⁻¹_* Θ'`.
* The general lemmas on curves, prime divisors, negativity, common models and finite programs
  that these proofs share with the decrease and terminal results are in
  `MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas`, in the namespace
  `MMP.Fourfold.Oai4C1`.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][oai4]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail

open MMP.Mori MMP.Fourfold.Oai4C1

/-! ### The end morphism -/

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold TopologicalSpace

universe u

section Pullback

variable {k : Type u} [Field k] {V T : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} [IsSeparated sT] [LocallyOfFiniteType sT]

variable [QuasiCompact sV] [QuasiCompact sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsLocallyNoetherian T] [IsNormal T]

/-- A morphism over `k` which is non-constant on a proper curve has positive residue degree at
the generic point of the curve: `k(C)` is a finite extension of the function field of the image
curve. -/
private theorem residueFieldDegree_pos_of_not_constant (u : V ⟶ T) (hu : u ≫ sT = sV)
    (Γ : ProperCurve sV) (hnc : ¬ ∃ t : T, Set.range (Γ.ι ≫ u) = {t}) :
    0 < residueFieldDegree u Γ.point := by
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree u Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι u (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sT φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

end Pullback

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori

universe u

namespace TwoEnds

open MMP.Fourfold.Oai4C1.TwoEnds

/-- One half of the comparison: `q₂^* D₂ ≤ q₁^* D₁`. -/
private theorem le_of_isPullback (k : Type u) [Field k] {Z V₁ V₂ W : Scheme.{u}}
    (sV₁ : V₁ ⟶ Spec (.of k)) (sV₂ : V₂ ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [QuasiCompact sV₁] [IsLocallyNoetherian V₁] [IsNormal V₁]
    [QuasiCompact sV₂] [IsLocallyNoetherian V₂] [IsNormal V₂] [AlgebraicGeometry.IsVariety k sV₂]
    [QuasiCompact sW] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hV₁ : IsNormalVariety k sV₁) (hW : IsNormalVariety k sW)
    (π₁ : V₁ ⟶ Z) (π₂ : V₂ ⟶ Z) (q₁ : W ⟶ V₁) (q₂ : W ⟶ V₂) [IsProper q₁]
    (hq₁ : IsBirationalMorphism q₁) (hs₁ : q₁ ≫ sV₁ = sW) (hs₂ : q₂ ≫ sV₂ = sW)
    (hcomp : q₁ ≫ π₁ = q₂ ≫ π₂)
    {D₁ : QDivisor V₁} {D₂ : QDivisor V₂} (hD₁ : D₁.IsQCartier) (hD₂ : D₂.IsQCartier)
    (hn₂ : D₂.IsRelativelyNef sV₂ π₂) {A₁ A₂ : QDivisor W}
    {hA₁₀ : ∀ T : irreducibleComponents W, q₁ (componentGenericPoint W T) ∉ D₁.supp}
    {hA₂₀ : ∀ T : irreducibleComponents W, q₂ (componentGenericPoint W T) ∉ D₂.supp}
    (hA₁ : D₁.IsPullback q₁ hA₁₀ A₁) (hA₂ : D₂.IsPullback q₂ hA₂₀ A₂)
    {F₁ F₂ : QDivisor W} (hF₂ : 0 ≤ F₂)
    (hF₁₀ : RationalMap.transformDivisor (X := W) q₁.toRationalMap F₁ = 0)
    (heq : A₁ + F₁ = A₂ + F₂) :
    A₂ ≤ A₁ := by
  haveI : AlgebraicGeometry.IsVariety k sV₁ := hV₁.1
  have hA₁q := hA₁.isQCartier hD₁
  have hA₂q := hA₂.isQCartier hD₂
  have hEq : (A₁ - A₂).IsQCartier := by
    rw [sub_eq_add_neg]; exact hA₁q.add (isQCartier_neg hA₂q)
  have hnE := isQCartier_neg hEq
  have hE : A₁ - A₂ = F₂ - F₁ := by
    rw [sub_eq_sub_iff_add_eq_add, heq, add_comm]
  refine sub_nonneg.mp <| Negativity.nonneg_of_transformDivisor_nonneg k sV₁ sW hV₁ hW q₁ hs₁ hq₁
    (MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sW hnE fun Γ hΓ => by
      have h1 := QDivisor.intersectionNumber_add' k sW Γ.ι Γ.dim_le (-(A₁ - A₂)) A₁ hnE hA₁q
        (hnE.add hA₁q)
      rw [MMP.Fourfold.intersectionNumber_congr sW Γ.ι Γ.dim_le (hnE.add hA₁q) hA₂q (by abel),
        intersectionNumber_isPullback_eq_zero q₁ hs₁ hD₁ hA₁ Γ hΓ, add_zero] at h1
      exact h1 ▸ intersectionNumber_isPullback_nonneg q₂ hs₂ π₂ hD₂ hn₂ hA₂ Γ
        (hcomp ▸ fun x hx => by simp only [Scheme.Hom.comp_apply, hΓ x hx]))
    (by rw [hE, map_sub, hF₁₀, sub_zero]; exact RationalMap.transformDivisor_nonneg _ hF₂)

/-- **Two ends agree upstairs.** Let `π_j : V_j ⟶ Z` be projective with `D_j` `π_j`-nef, and
`q_j : W ⟶ V_j` birational from a smooth projective `W` with `q₁ ≫ π₁ = q₂ ≫ π₂`. If
`q₁^* D₁ + F₁ = q₂^* D₂ + F₂` with `F_j ≥ 0` and `q_{j*} F_j = 0`, then `q₁^* D₁ = q₂^* D₂`:
the negativity lemma applied along each `q_j` gives both inequalities. -/
private theorem pullback_eq_of_add_eq
    (k : Type u) [Field k] {Z V₁ V₂ W : Scheme.{u}}
    (sV₁ : V₁ ⟶ Spec (.of k)) (sV₂ : V₂ ⟶ Spec (.of k))
    [QuasiCompact sV₁] [IsLocallyNoetherian V₁] [IsNormal V₁]
    [QuasiCompact sV₂] [IsLocallyNoetherian V₂] [IsNormal V₂]
    [IsLocallyNoetherian W] [IsNormal W]
    (hV₁ : IsNormalVariety k sV₁) (hV₂ : IsNormalVariety k sV₂) (π₁ : V₁ ⟶ Z) (π₂ : V₂ ⟶ Z)
    {D₁ : QDivisor V₁} {D₂ : QDivisor V₂} (hD₁ : D₁.IsQCartier) (hD₂ : D₂.IsQCartier)
    (hn₁ : D₁.IsRelativelyNef sV₁ π₁) (hn₂ : D₂.IsRelativelyNef sV₂ π₂)
    (q₁ : W ⟶ V₁) (q₂ : W ⟶ V₂)
    (hWp : MMP.Mori.IsProjectiveVariety k (q₁ ≫ sV₁))
    (hq₁ : IsBirationalMorphism q₁) (hq₂ : IsBirationalMorphism q₂)
    (hsq : q₁ ≫ sV₁ = q₂ ≫ sV₂) (hcomp : q₁ ≫ π₁ = q₂ ≫ π₂)
    {A₁ A₂ : QDivisor W}
    (hA₁₀ : ∀ T : irreducibleComponents W, q₁ (componentGenericPoint W T) ∉ D₁.supp)
    (hA₂₀ : ∀ T : irreducibleComponents W, q₂ (componentGenericPoint W T) ∉ D₂.supp)
    (hA₁ : D₁.IsPullback q₁ hA₁₀ A₁) (hA₂ : D₂.IsPullback q₂ hA₂₀ A₂)
    {F₁ F₂ : QDivisor W} (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂)
    (hF₁₀ : RationalMap.transformDivisor (X := W) q₁.toRationalMap F₁ = 0)
    (hF₂₀ : RationalMap.transformDivisor (X := W) q₂.toRationalMap F₂ = 0)
    (heq : A₁ + F₁ = A₂ + F₂) :
    A₁ = A₂ := by
  haveI : AlgebraicGeometry.IsVariety k sV₁ := hV₁.1
  haveI : AlgebraicGeometry.IsVariety k sV₂ := hV₂.1
  haveI : AlgebraicGeometry.IsProjectiveVariety k (q₁ ≫ sV₁) := hWp
  haveI : IsIntegral W := hWp.toIsVariety.toIsIntegral
  have hW : IsNormalVariety k (q₁ ≫ sV₁) := ⟨hWp.toIsVariety, inferInstance⟩
  haveI : IsProper (q₁ ≫ sV₁) := isProper_of_isProjectiveMorphism _ hWp.isProjective
  haveI : IsProper q₁ := IsProper.of_comp q₁ sV₁
  haveI : IsProper (q₂ ≫ sV₂) := hsq ▸ inferInstance
  haveI : IsProper q₂ := IsProper.of_comp q₂ sV₂
  exact le_antisymm
    (le_of_isPullback k sV₂ sV₁ (q₁ ≫ sV₁) hV₂ hW π₂ π₁ q₂ q₁ hq₂ hsq.symm rfl hcomp.symm hD₂
      hD₁ hn₁ hA₂ hA₁ hF₁ hF₂₀ heq.symm)
    (le_of_isPullback k sV₁ sV₂ (q₁ ≫ sV₁) hV₁ hW π₁ π₂ q₁ q₂ hq₁ rfl hsq.symm hcomp hD₁ hD₂
      hn₂ hA₁ hA₂ hF₂ hF₁₀ heq)

end TwoEnds

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori Topology TopologicalSpace

universe u

namespace TwoEnds

open MMP.Fourfold.Oai4C1.TwoEnds

/-! ### Curves contracted by one end are contracted by the other -/

/-- **Contracted curves.** Let `u_j : V ⟶ T_j` be morphisms over `k` with `u₁ ≫ π₁ = u₂ ≫ π₂`,
and let `A` be both `u₁^* L₁` and `u₂^* L₂`, where `L₂` is positive on every proper curve
contracted by `π₂`. Then `u₂` contracts every proper curve that `u₁` contracts: otherwise the
image curve is contracted by `π₂`, and the projection formula makes `0 = (A · C)` a positive
multiple of `(L₂ · u₂(C)) > 0`. -/
private theorem isContractedBy_of_isPullback_eq {k : Type u} [Field k] {V T₁ T₂ S : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} {s₁ : T₁ ⟶ Spec (.of k)} {s₂ : T₂ ⟶ Spec (.of k)}
    [QuasiCompact sV] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [IsSeparated s₁] [LocallyOfFiniteType s₁] [QuasiCompact s₁] [IsLocallyNoetherian T₁]
    [IsNormal T₁] [IsSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂]
    [IsLocallyNoetherian T₂] [IsNormal T₂]
    {u₁ : V ⟶ T₁} {u₂ : V ⟶ T₂} (hu₁ : u₁ ≫ s₁ = sV) (hu₂ : u₂ ≫ s₂ = sV)
    {π₁ : T₁ ⟶ S} {π₂ : T₂ ⟶ S} (hcomp : u₁ ≫ π₁ = u₂ ≫ π₂)
    {L₁ : QDivisor T₁} {L₂ : QDivisor T₂} (hL₁ : L₁.IsQCartier) (hL₂ : L₂.IsQCartier)
    (hpos : ∀ Γ : ProperCurve s₂, Γ.IsContractedBy π₂ →
      0 < L₂.intersectionNumber k s₂ Γ.ι Γ.dim_le hL₂)
    {hB₁ : ∀ Z : irreducibleComponents V, u₁ (componentGenericPoint V Z) ∉ L₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents V, u₂ (componentGenericPoint V Z) ∉ L₂.supp}
    {A : QDivisor V} (h₁ : L₁.IsPullback u₁ hB₁ A) (h₂ : L₂.IsPullback u₂ hB₂ A)
    (C : ProperCurve sV) (hC : C.IsContractedBy u₁) : C.IsContractedBy u₂ := by
  by_contra hc
  have hC₂ : C.IsContractedBy (u₂ ≫ π₂) := by
    rw [← hcomp]
    intro x hx
    simp only [Scheme.Hom.comp_apply, hC x hx]
  have h0 := intersectionNumber_isPullback_eq_zero u₁ hu₁ hL₁ h₁ C hC
  rw [intersectionNumber_isPullback_eq_mul u₂ hu₂ hL₂ h₂ C ⟨_, isProperCurve_map u₂ hu₂ C hc⟩
    rfl] at h0
  have h3 := residueFieldDegree_pos_of_not_constant u₂ hu₂ C (not_exists_range_eq_singleton u₂ C hc)
  have := mul_pos (show (0 : ℚ) < residueFieldDegree u₂ C.point by exact_mod_cast h3)
    (hpos _ (isContractedBy_map u₂ hu₂ π₂ C hc hC₂))
  linarith

section Fibres

variable {k : Type u} [Field k] {U V Z : Scheme.{u}} {sU : U ⟶ Spec (.of k)} [IsProper sU]
  [IsLocallyNoetherian U] {g : U ⟶ V} {h : U ⟶ Z}
  (hcurve : ∀ C : ProperCurve sU, C.IsContractedBy g → C.IsContractedBy h)
  (hgc : IsClosedMap g) (hhc : IsClosedMap h)

include hcurve hhc in
/-- If `{y}⁻` lies in a fibre of `g`, then `h y = h p` for every closed point `p` of `{y}⁻`. -/
private theorem apply_eq_of_specializes {w : V} {y p : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hyp : y ⤳ p) (hp : IsClosed ({p} : Set U)) :
    h y = h p := by
  by_contra hne
  have hZ : IsClosed (h ⁻¹' {h p}) := by
    simpa only [Set.image_singleton] using (hhc _ hp).preimage h.continuous
  obtain ⟨c, hyc, hcp, hcZ, hc⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sU hyp hp hZ
    rfl hne
  have hcy : closure ({c} : Set U) ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hyc))
      isClosed_closure
  have hgC : (⟨c, hc⟩ : ProperCurve sU).IsContractedBy g := fun x hx => by
    have h1 := hy (hcy hx)
    have h2 := hy (hcy (subset_closure rfl))
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  exact hcZ (hcurve _ hgC p (specializes_iff_mem_closure.mp hcp)).symm

include hcurve hhc in
/-- If `{y}⁻` lies in a fibre of `g`, then `h` is constant on `{y}⁻`. -/
private theorem apply_eq_of_mem_closure [CompactSpace U] {w : V} {y x : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hx : x ∈ closure ({y} : Set U)) : h x = h y := by
  obtain ⟨p, hp, hpc⟩ := (isClosed_closure (s := ({x} : Set U))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have hxy : closure ({x} : Set U) ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure
  rw [apply_eq_of_specializes hcurve hhc (hxy.trans hy) (specializes_iff_mem_closure.mpr hp) hpc,
    apply_eq_of_specializes hcurve hhc hy (specializes_iff_mem_closure.mpr (hxy hp)) hpc]

include hcurve hgc hhc in
/-- Two closed points in the same fibre of `g` have the same image under `h`, when the fibres of
`g` are connected. -/
private theorem apply_eq_of_isClosed [CompactSpace U] [NoetherianSpace U]
    (hconn : ∀ v : V, _root_.IsPreconnected (g ⁻¹' {v})) {p q : U}
    (hp : IsClosed ({p} : Set U)) (hpq : g p = g q) : h p = h q := by
  classical
  have hw : IsClosed ({g p} : Set V) := by simpa only [Set.image_singleton] using hgc _ hp
  set F := g ⁻¹' {g p} with hFdef
  have hF : IsClosed F := hw.preimage g.continuous
  obtain ⟨S, hS, hFS⟩ := NoetherianSpace.exists_finset_irreducible ⟨F, hF⟩
  have hFS' : F = ⋃ t ∈ S, (t : Set U) := by
    have := congrArg (fun T : Closeds U => (T : Set U)) hFS
    rwa [Closeds.coe_finset_sup, Finset.sup_eq_iSup] at this
  have hgen : ∀ t ∈ S, ∃ y : U, closure {y} = (t : Set U) := fun t ht =>
    QuasiSober.sober (hS ⟨t, ht⟩) t.isClosed
  haveI : Nonempty U := ⟨p⟩
  choose! η hη using hgen
  have htF : ∀ t ∈ S, closure {η t} ⊆ F := fun t ht => by
    rw [hη t ht, hFS']
    exact Set.subset_biUnion_of_mem (u := fun t : Closeds U => (t : Set U)) ht
  let vals : Set Z := (fun t => h (η t)) '' (S : Set (Closeds U))
  have hvals : vals.Finite := S.finite_toSet.image _
  have hvalc : ∀ z ∈ vals, IsClosed ({z} : Set Z) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨p', hp', hp'c⟩ := (isClosed_closure (s := ({η t} : Set U))).exists_closed_singleton
      ⟨η t, subset_closure rfl⟩
    have := hhc _ hp'c
    rwa [Set.image_singleton, apply_eq_of_mem_closure hcurve hhc (htF t ht) hp'] at this
  have hcover : F ⊆ h ⁻¹' {h p} ∪ h ⁻¹' (⋃ z ∈ vals \ {h p}, {z}) := by
    intro x hx
    rw [hFS'] at hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    have hxη : h x = h (η t) :=
      apply_eq_of_mem_closure hcurve hhc (htF t ht) ((hη t ht).symm ▸ hxt)
    by_cases hxp : h x = h p
    · exact Or.inl hxp
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨h x, ⟨⟨t, ht, hxη.symm⟩, hxp⟩, rfl⟩)
  have hu : IsClosed (h ⁻¹' {h p}) := by
    simpa only [Set.image_singleton] using (hhc _ hp).preimage h.continuous
  have hv : IsClosed (h ⁻¹' (⋃ z ∈ vals \ {h p}, {z})) :=
    ((hvals.diff).isClosed_biUnion fun z hz => hvalc z hz.1).preimage h.continuous
  have hpF : p ∈ F := rfl
  have hdisj : F ∩ (h ⁻¹' {h p} ∩ h ⁻¹' (⋃ z ∈ vals \ {h p}, {z})) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro - hx ⟨z, ⟨-, hz⟩, rfl⟩
    exact hz hx
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp (hconn (g p)) _ _ hu hv hcover hdisj
    with hsub | hsub
  · exact (hsub (show q ∈ F from hpq.symm)).symm
  · have := hsub hpF
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff] at this
    obtain ⟨z, ⟨-, hz⟩, rfl⟩ := this
    exact absurd rfl hz

include hcurve hgc hhc in
/-- `h` is constant on every fibre of `g`, when the fibres of `g` are connected. -/
private theorem apply_eq_of_apply_eq [CompactSpace U] [NoetherianSpace U] [JacobsonSpace U]
    (hconn : ∀ v : V, _root_.IsPreconnected (g ⁻¹' {v})) {x x' : U} (hxx : g x = g x') :
    h x = h x' := by
  suffices H : ∀ x x' : U, g x = g x' → h x ⤳ h x' from
    (H x x' hxx).antisymm (H x' x hxx.symm) |>.eq
  intro x x' hxx
  by_contra hn
  have hC : IsClosed (h ⁻¹' closure {h x}) := isClosed_closure.preimage h.continuous
  have hx'O : x' ∈ (h ⁻¹' closure {h x})ᶜ := fun H => hn (specializes_iff_mem_closure.mpr H)
  have hx' : x' ∈ closure (closure {x'} ∩ closedPoints U) := by
    rw [JacobsonSpace.closure_inter_closedPoints isClosed_closure]
    exact subset_closure rfl
  obtain ⟨p, hpO, hpx', hpc⟩ := mem_closure_iff.mp hx' _ hC.isOpen_compl hx'O
  rw [mem_closedPoints_iff] at hpc
  have hgp : g p ∈ g '' closure {x} := by
    have hsub : closure {g x} ⊆ g '' closure {x} :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩)
        (hgc _ isClosed_closure)
    refine hsub (specializes_iff_mem_closure.mp ?_)
    rw [hxx]
    exact (specializes_iff_mem_closure.mpr hpx').map g.continuous
  obtain ⟨q₀, hq₀, hgq₀⟩ := hgp
  have hwc : IsClosed ({g p} : Set V) := by
    have := hgc _ hpc
    rwa [Set.image_singleton] at this
  obtain ⟨q, ⟨hqx, hgq⟩, hqc⟩ := (isClosed_closure.inter (hwc.preimage g.continuous) :
    IsClosed (closure {x} ∩ g ⁻¹' {g p})).exists_closed_singleton ⟨q₀, hq₀, hgq₀⟩
  have hpq : h q = h p := apply_eq_of_isClosed hcurve hgc hhc hconn hqc hgq
  have hqC : h q ∈ closure {h x} :=
    specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hqx).map h.continuous)
  exact hpO (show h p ∈ closure {h x} from hpq ▸ hqC)

end Fibres

/-- **The two ends.** In the setting of `pullback_eq_of_add_eq`, if moreover `D₂` has a
`π₂`-ample multiple, then `q₂` factors as `q₁ ≫ h` through a morphism `h : V₁ ⟶ V₂` over `Z`
with `D₁ = h^* D₂`: `q₂` contracts every curve that `q₁` contracts, hence is constant on the
connected fibres of `q₁`. -/
private theorem exists_hom_isPullback
    (k : Type u) [Field k] {Z V₁ V₂ W : Scheme.{u}}
    (sV₁ : V₁ ⟶ Spec (.of k)) (sV₂ : V₂ ⟶ Spec (.of k))
    [QuasiCompact sV₁] [IsLocallyNoetherian V₁] [IsNormal V₁]
    [CompactSpace V₂] [IsLocallyNoetherian V₂] [IsNormal V₂]
    [IsLocallyNoetherian W] [IsNormal W]
    (hV₁ : IsNormalVariety k sV₁) (hV₂ : IsNormalVariety k sV₂) (π₁ : V₁ ⟶ Z) (π₂ : V₂ ⟶ Z)
    {D₁ : QDivisor V₁} {D₂ : QDivisor V₂} (hD₁ : D₁.IsQCartier) (hD₂ : D₂.IsQCartier)
    (hn₁ : D₁.IsRelativelyNef sV₁ π₁) (ha₂ : D₂.HasRelativelyAmpleMultiple π₂)
    (q₁ : W ⟶ V₁) (q₂ : W ⟶ V₂)
    (hWp : MMP.Mori.IsProjectiveVariety k (q₁ ≫ sV₁))
    (hq₁ : IsBirationalMorphism q₁) (hq₂ : IsBirationalMorphism q₂)
    (hsq : q₁ ≫ sV₁ = q₂ ≫ sV₂) (hcomp : q₁ ≫ π₁ = q₂ ≫ π₂)
    {A₁ A₂ : QDivisor W}
    (hA₁₀ : ∀ T : irreducibleComponents W, q₁ (componentGenericPoint W T) ∉ D₁.supp)
    (hA₂₀ : ∀ T : irreducibleComponents W, q₂ (componentGenericPoint W T) ∉ D₂.supp)
    (hA₁ : D₁.IsPullback q₁ hA₁₀ A₁) (hA₂ : D₂.IsPullback q₂ hA₂₀ A₂)
    {F₁ F₂ : QDivisor W} (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂)
    (hF₁₀ : RationalMap.transformDivisor (X := W) q₁.toRationalMap F₁ = 0)
    (hF₂₀ : RationalMap.transformDivisor (X := W) q₂.toRationalMap F₂ = 0)
    (heq : A₁ + F₁ = A₂ + F₂) :
    ∃ h : V₁ ⟶ V₂, q₁ ≫ h = q₂ ∧ h ≫ π₂ = π₁ ∧
      ∃ hD : ∀ T : irreducibleComponents V₁, h (componentGenericPoint V₁ T) ∉ D₂.supp,
        D₂.IsPullback h hD D₁ := by
  haveI : AlgebraicGeometry.IsVariety k sV₁ := hV₁.1
  haveI : AlgebraicGeometry.IsVariety k sV₂ := hV₂.1
  haveI : AlgebraicGeometry.IsProjectiveVariety k (q₁ ≫ sV₁) := hWp
  haveI : IsIntegral W := hWp.toIsVariety.toIsIntegral
  haveI : IsIntegral V₁ := hV₁.1.toIsIntegral
  haveI : IsIntegral V₂ := hV₂.1.toIsIntegral
  have hW : IsNormalVariety k (q₁ ≫ sV₁) := ⟨hWp.toIsVariety, inferInstance⟩
  haveI : IsProper (q₁ ≫ sV₁) := isProper_of_isProjectiveMorphism _ hWp.isProjective
  haveI : IsProper q₁ := IsProper.of_comp q₁ sV₁
  haveI : IsProper (q₂ ≫ sV₂) := hsq ▸ inferInstance
  haveI : IsProper q₂ := IsProper.of_comp q₂ sV₂
  haveI : CompactSpace V₁ := QuasiCompact.compactSpace_of_compactSpace sV₁
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q₁ ≫ sV₁)
  -- `D₂` is positive on curves contracted by `π₂`, hence `π₂`-nef, so `q₁^* D₁ = q₂^* D₂`
  have hpos : ∀ Γ : ProperCurve sV₂, Γ.IsContractedBy π₂ →
      0 < D₂.intersectionNumber k sV₂ Γ.ι Γ.dim_le hD₂ := fun Γ hΓ =>
    intersectionNumber_pos_of_hasRelativelyAmpleMultiple sV₂ hD₂ ha₂ Γ hΓ
  have hn₂ : D₂.IsRelativelyNef sV₂ π₂ :=
    MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV₂ hD₂ fun Γ hΓ =>
      (hpos Γ hΓ).le
  have hA : A₁ = A₂ := pullback_eq_of_add_eq k sV₁ sV₂ hV₁ hV₂ π₁ π₂ hD₁ hD₂ hn₁ hn₂ q₁ q₂ hWp
    hq₁ hq₂ hsq hcomp hA₁₀ hA₂₀ hA₁ hA₂ hF₁ hF₂ hF₁₀ hF₂₀ heq
  -- `q₂` contracts every curve that `q₁` contracts
  have hcurve := isContractedBy_of_isPullback_eq rfl hsq.symm hcomp hD₁ hD₂ hpos
    (hA ▸ hA₁) hA₂
  -- `q₂` is constant on the connected fibres of `q₁`, and rigidity gives `h`
  haveI : IsNoetherian W := (isNoetherian_iff W).mpr ⟨inferInstance, inferInstance⟩
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (q₁ ≫ sV₁)
  obtain ⟨hiso, hconn⟩ := MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    (q₁ ≫ sV₁) sV₁ hWp.toIsVariety hV₁ q₁ hq₁
  haveI : IsIso q₁.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ q₁.c fun U => hiso U.unop
  obtain ⟨h, hh, -⟩ := MMP.existsUnique_comp_eq_of_isIso_c q₁ q₂ fun x x' hxx =>
    apply_eq_of_apply_eq hcurve q₁.isClosedMap q₂.isClosedMap
      (fun v => (hconn v).isPreconnected) hxx
  have hπ : h ≫ π₂ = π₁ := by
    obtain ⟨g, -, hg⟩ := MMP.existsUnique_comp_eq_of_isIso_c q₁ (q₁ ≫ π₁) fun x x' hxx => by
      simp only [Scheme.Hom.comp_apply, hxx]
    rw [hg (h ≫ π₂) (show q₁ ≫ h ≫ π₂ = _ by rw [← Category.assoc, hh, hcomp]), hg π₁ rfl]
  subst hh
  -- `D₁ = q_{1*} q₁^* D₁ = q_{1*} q₁^* h^* D₂ = h^* D₂`
  haveI : IsDominant (q₁ ≫ h) := hq₂.isDominant
  haveI : IsDominant q₁ := hq₁.isDominant
  haveI : IsDominant h := IsDominant.of_comp q₁ h
  have hD : ∀ T : irreducibleComponents V₁, h (componentGenericPoint V₁ T) ∉ D₂.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' h D₂
  have hB := QDivisor.isPullback_pullback (f := h) hD₂ hD
  have hBq := hB.isQCartier hD₂
  have hgen : ∀ T : irreducibleComponents W, q₁ (componentGenericPoint W T) ∉
      (D₂.pullback hD₂ hD).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q₁ _
  have hB' := QDivisor.isPullback_pullback hBq hgen
  obtain ⟨hM', hcompB⟩ := qDivisor_isPullback_comp h q₁ hB hB'
  have hB'A : (D₂.pullback hD₂ hD).pullback hBq hgen = A₂ :=
    (hD₂.existsUnique_isPullback hM').unique hcompB hA₂
  have e1 := MMP.Positivity.transformDivisor_of_isPullback hV₁ hW hq₁ hBq hgen hB'
  have e2 := MMP.Positivity.transformDivisor_of_isPullback hV₁ hW hq₁ hD₁ hA₁₀ hA₁
  have hBD : D₂.pullback hD₂ hD = D₁ := by rw [← e1, ← e2, hB'A, hA]
  exact ⟨h, rfl, hπ, hD, hBD ▸ hB⟩

end TwoEnds

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace ProgramComparison

open MMP.Fourfold.Oai4C1.ProgramComparison

/-- **Finite programs: effective comparison**, for morphisms `q_k : W ⟶ V_k` given for
`k ≤ m`. -/
private theorem pullback_zero_sub_pullback_nonneg (m : ℕ)
    {V : ℕ → Scheme.{0}} (sV : ∀ k, V k ⟶ Spec (.of ℂ)) [∀ k, IsIntegral (V k)]
    [∀ k, CompactSpace (V k)] [∀ k, IsLocallyNoetherian (V k)] [∀ k, IsNormal (V k)]
    (K : ∀ k, Divisor (V k)) (Θ : ∀ k, QDivisor (V k))
    {T : ℕ → Scheme.{0}} (sT : ∀ k, T k ⟶ Spec (.of ℂ))
    (g : ∀ k, V k ⟶ T k) (gp : ∀ k, V (k + 1) ⟶ T k)
    (hstep : ∀ k < m,
      IsFourfoldStepDiagram (sV k) (sT k) (sV (k + 1)) (K k) (Θ k) (g k) (gp k))
    (hK : ∀ k < m, K (k + 1) = flipTransform (g k) (gp k) (K k))
    (hΘ : ∀ k < m, Θ (k + 1) = flipTransform (g k) (gp k) (Θ k))
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (sW : W ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWn : IsNormalVariety ℂ sW)
    (q : ∀ k, k ≤ m → (W ⟶ V k)) (hqs : ∀ k (hk : k ≤ m), q k hk ≫ sV k = sW)
    (hq : ∀ k (hk : k ≤ m), IsBirationalMorphism (q k hk))
    (hcomp : ∀ k (hk : k < m), q k (Nat.le_of_lt hk) ≫ g k = q (k + 1) hk ≫ gp k)
    (hD₀ : (Divisor.toQDivisor (K 0) + Θ 0).IsQCartier)
    (hDₘ : (Divisor.toQDivisor (K m) + Θ m).IsQCartier)
    (h₀ : ∀ Z : irreducibleComponents W,
      q 0 m.zero_le (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K 0) + Θ 0).supp)
    (hₘ : ∀ Z : irreducibleComponents W,
      q m le_rfl (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K m) + Θ m).supp) :
    0 ≤ (Divisor.toQDivisor (K 0) + Θ 0).pullback hD₀ h₀ -
      (Divisor.toQDivisor (K m) + Θ m).pullback hDₘ hₘ := by
  have hgen : ∀ k (hk : k ≤ m), ∀ Z : irreducibleComponents W,
      q k hk (componentGenericPoint W Z) ∉ (Divisor.toQDivisor (K k) + Θ k).supp := fun k hk => by
    haveI := (hq k hk).isDominant
    exact MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hQ : ∀ k ≤ m, (Divisor.toQDivisor (K k) + Θ k).IsQCartier := fun k hk => by
    rcases hk.lt_or_eq with h | rfl
    · exact (hstep k h).isQCartier_minus
    · exact hDₘ
  have key : ∀ j (hj : j ≤ m), 0 ≤ (Divisor.toQDivisor (K 0) + Θ 0).pullback hD₀ h₀ -
      (Divisor.toQDivisor (K j) + Θ j).pullback (hQ j hj) (hgen j hj) := by
    intro j
    induction j with
    | zero => exact fun _ => (sub_self _).ge
    | succ j ih =>
      intro hj
      have h := add_nonneg (ih (by omega)) (pullback_sub_pullback_succ_nonneg sV K Θ sT g gp j
        (hstep j hj) (hK j hj) (hΘ j hj) sW hW hWn (q j (Nat.le_of_lt hj)) (q (j + 1) hj)
        (hqs j (Nat.le_of_lt hj)) (hqs (j + 1) hj) (hq j (Nat.le_of_lt hj)) (hq (j + 1) hj)
        (hcomp j hj)
        (hQ j (by omega)) (hQ (j + 1) hj) (hgen j (Nat.le_of_lt hj)) (hgen (j + 1) hj))
      rwa [sub_add_sub_cancel] at h
  exact key m le_rfl

end ProgramComparison

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace BridgeComparison

open MMP.Fourfold.Oai4C1.BridgeComparison

section DecreasedBoundary

variable {T : StabilizedSmallKltTail} {i : ℕ}
  {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
  {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {a : I → ℚ} {Θ' : QDivisor J.Y}

/-- At a prime divisor `Q` of `Y_i` which is not marked, lying over the prime divisor `Q₀` of
`X_i`, the decreased boundary has the coefficient of `B_i` at `Q₀`. -/
private theorem decreasedBoundary_apply_of_notMem_range
    (hΘ' : Θ' = inverseTransformDivisor J.p (T.B i) + ∑ s : I, Finsupp.single (J.E s) (1 - a s))
    {Q : MMP.Mori.PrimeDivisor J.Y} (hQE : Q ∉ Set.range J.E) {Q₀ : MMP.Mori.PrimeDivisor (T.X i)}
    (hQ₀ : J.p Q.genericPoint = Q₀.genericPoint) : Θ' Q = T.B i Q₀ := by
  haveI : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  rw [hΘ', Finsupp.add_apply, inverseTransformDivisor_apply_of_map_genericPoint hQ₀
    (genericPoint_mem_biregularLocus J.p J.isBirationalMorphism Q₀),
    Finsupp.finset_sum_apply, Finset.sum_eq_zero (fun t _ => ?_), add_zero]
  exact Finsupp.single_eq_of_ne fun h => hQE ⟨t, h.symm⟩

end DecreasedBoundary

/-- **The bridge comparison.** For `q : W ⟶ Y_i` and `r : W ⟶ X_{i+1}` birational with
`q ≫ p_i ≫ f_i = r ≫ f_i⁺`, and compatible canonical divisors, the divisor
`q^*(K_Y + Θ_i') - r^*(K_X + B_{i+1})` is effective, by the negativity lemma along `q`: its
push-forward to `Y_i` vanishes, the marked divisors having log discrepancy `a(s)` on `W`. -/
private theorem pullback_sub_pullback_nonneg {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}
    (hWp : MMP.Mori.IsProjectiveVariety ℂ (q ≫ J.sY)) (hWs : IsSmoothScheme (q ≫ J.sY))
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (q ≫ J.sY) 4)
    {KY : Divisor J.Y} (hKY : RationalMap.transformDivisor q.toRationalMap KW = KY)
    {KX : Divisor (T.X (i + 1))} (hKXc : KX.IsCanonicalDivisor (T.sX (i + 1)) 4)
    (hXQ : (Divisor.toQDivisor KX + T.B (i + 1)).IsQCartier)
    (hamp : (Divisor.toQDivisor KX + T.B (i + 1)).HasRelativelyAmpleMultiple (T.fp i))
    (hKX : RationalMap.transformDivisor r.toRationalMap KW = KX)
    (A R : QDivisor W)
    (hA₀ : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor KY + Θ').supp)
    (hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor KX + T.B (i + 1)).supp)
    (hA : (Divisor.toQDivisor KY + Θ').IsPullback q hA₀ A)
    (hR : (Divisor.toQDivisor KX + T.B (i + 1)).IsPullback r hR₀ R) :
    0 ≤ A - R := by
  have hSi := T.isFourfoldStepDiagram i
  have hY : IsNormalVariety ℂ J.sY := J.isQFactorial.1
  have hWn : IsNormalVariety ℂ (q ≫ J.sY) := ⟨hWp.toIsVariety, inferInstance⟩
  haveI : IsProper (q ≫ J.sY) := isProper_of_isProjectiveMorphism _ hWp.isProjective
  haveI : IsSeparated J.sY := hY.1.toIsSeparated
  haveI : IsSeparated (T.sX (i + 1)) := hSi.isNormalVariety_plus.1.toIsSeparated
  have hrs : r ≫ T.sX (i + 1) = q ≫ J.sY := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, ← hcomp, FourfoldCrepantJunction.sY]
    simp only [Category.assoc, hSi.comp_eq_minus]
  haveI : IsProper q := IsProper.of_comp q J.sY
  haveI : IsProper (r ≫ T.sX (i + 1)) := hrs ▸ inferInstance
  haveI : IsProper r := IsProper.of_comp r (T.sX (i + 1))
  have hYQ : (Divisor.toQDivisor KY + Θ').IsQCartier :=
    isQCartier_of_isQFactorial J.sY J.isQFactorial _
  have hpush : RationalMap.transformDivisor (X := W) q.toRationalMap (A - R) = 0 := by
    have hXi := hSi.isNormalVariety_minus
    have hXi1 := hSi.isNormalVariety_plus
    have hZ := hSi.isNormalVariety_target
    haveI := hq.isDominant
    haveI := hr.isDominant
    haveI := J.isBirationalMorphism.isDominant
    haveI := isSeparated_toTerminal_of_isNormalVariety hY
    haveI := isSeparated_toTerminal_of_isNormalVariety hXi1
    haveI := isSeparated_toTerminal_of_isNormalVariety hZ
    haveI : IsNormal (T.Z i) := hZ.2
    haveI : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
    haveI := hXi1.1.toLocallyOfFiniteType
    have hfs : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
      T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
    have hfps := hSi.isSmallMorphism_plus
    haveI : IsProper (T.f i) := hfs.isProper
    haveI : IsProper (T.fp i) := hfps.isProper
    have hWn' : IsNormalVariety ℂ (r ≫ T.sX (i + 1)) := hrs ▸ hWn
    haveI : LocallyOfFiniteType (r ≫ T.sX (i + 1)) := hWn'.1.toLocallyOfFiniteType
    obtain ⟨a, ha, hΘ'eq⟩ := hΘ'
    rw [RationalMap.transformDivisor]
    refine mapPrimeDivisors_eq_zero_of_forall _ fun P Q hPQ => ?_
    have hPQ' := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q P Q).mp hPQ
    haveI := isIso_stalkMap_of_map_eq_genericPoint hq hPQ'
    rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor P Q hPQ' hYQ hA]
    change ((KY Q : ℤ) : ℚ) + Θ' Q - R P = 0
    rw [← hKY, transformDivisor_apply_of_map_genericPoint hq hPQ' KW, sub_eq_zero]
    by_cases hQE : Q ∈ Set.range J.E
    · -- at a marked divisor, `(W, r, P)` computes the log discrepancy `a_{i+1}(s)`
      obtain ⟨s, rfl⟩ := hQE
      rw [decreasedBoundary_apply_E hΘ'eq]
      obtain ⟨s', hts, n, D', -, hD'v, hD'log⟩ := ha s
      have hval : D'.valuation =
          (⟨W, r, hWn', hr, P⟩ : DivisorOver ℂ (T.sX (i + 1))).valuation := by
        rw [hD'v]
        refine valuation_eq_of_comap_eq
          hfps.isBirationalMorphism.functionFieldMap_bijective.2 (hts.trans ?_)
        refine Valuation.ext fun t => ?_
        rw [Valuation.comap_apply, Valuation.comap_apply]
        change _ = P.divisorialValuation (functionFieldMap r (functionFieldMap (T.fp i) t))
        rw [functionFieldMap_comp_apply r (T.fp i) hcomp.symm,
          ← functionFieldMap_comp_apply q (J.p ≫ T.f i) rfl,
          ← functionFieldMap_comp_apply J.p (T.f i) rfl,
          ← PrimeDivisor.valuationOver_apply, valuationOver_eq_of_isIso q P (J.E s) hPQ',
          ← J.valuation_eq s]
        rfl
      have := coeff_isPullback_eq_of_isLogDiscrepancy hXi1 hKXc hXQ hr
        hWn' (hrs ▸ hKW) hKX hR P hD'log hval
      exact_mod_cast (show (((KW P : ℚ) + (1 - a s) : ℚ) : ℝ) = ((R P : ℚ) : ℝ) by
        push_cast; linarith)
    · -- otherwise `Q` lies over a prime `Q₀` of `X_i`, whose strict transform `Q₁` on
      -- `X_{i+1}` is the image of `P`, the step being small
      obtain ⟨Q₀, hv₀⟩ :=
        MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXi
          (⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, Q⟩ : DivisorOver ℂ (T.sX i))
          fun h => hQE ((J.isExceptional_iff Q).mp h)
      have hQ₀ : J.p Q.genericPoint = Q₀.genericPoint :=
        MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXi.1 hv₀
      have hco : Order.coheight (T.f i Q₀.genericPoint) = 1 := by
        rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _
          (map_genericPoint_mem_biregularLocus hfs.two_le_codimension Q₀), Q₀.coheight_genericPoint]
      have hQZ : T.f i Q₀.genericPoint = (PrimeDivisor.ofCoheightOne _ hco).genericPoint :=
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
      obtain ⟨Q₁, hQ₁, -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
        hZ (by rwa [hSi.comp_eq_plus]) hfps.isBirationalMorphism
          (PrimeDivisor.ofCoheightOne _ hco)
      have hrP : r P.genericPoint = Q₁.genericPoint := by
        refine eq_of_map_eq_genericPoint hfps.isBirationalMorphism ?_ hQ₁
        rw [← Scheme.Hom.comp_apply, ← hcomp]
        simp only [Scheme.Hom.comp_apply, hPQ', hQ₀]; exact hQZ
      haveI := isIso_stalkMap_of_map_eq_genericPoint hr hrP
      rw [coeff_eq_of_isPullback_qDivisor P Q₁ hrP hXQ hR, decreasedBoundary_apply_of_notMem_range
        hΘ'eq hQE hQ₀]
      change _ = ((KX Q₁ : ℤ) : ℚ) + T.B (i + 1) Q₁
      rw [← hKX, transformDivisor_apply_of_map_genericPoint hr hrP, T.B_eq i]
      simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
      rw [inverseTransformDivisor_apply_of_map_genericPoint hQ₁
        (hQ₁ ▸ map_genericPoint_mem_biregularLocus hfps.two_le_codimension Q₁),
        transformDivisor_apply_of_map_genericPoint hfs.isBirationalMorphism hQZ]
  haveI := hSi.isNormalVariety_plus.1.toLocallyOfFiniteType
  haveI := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact J.sY := hY.1.toQuasiCompact
  haveI := hq.isDominant
  exact Negativity.nonneg_of_transformDivisor_nonneg ℂ J.sY (q ≫ J.sY) hY hWn q rfl hq
    (isRelativelyNef_neg_sub_of_isPullback rfl hrs hcomp hYQ hXQ hamp hA hR) hpush.ge

/-- A prime divisor of the source of a crepant junction lying over a prime divisor of the base
is not one of the extracted divisors `E_s`. -/
private theorem notMem_range_E_of_map_genericPoint {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (J : FourfoldCrepantJunction sX B I) {PY : MMP.Mori.PrimeDivisor J.Y}
    {P₀ : MMP.Mori.PrimeDivisor X} (hpPY : J.p PY.genericPoint = P₀.genericPoint) :
    PY ∉ Set.range J.E := by
  rintro ⟨s, hs⟩
  have := isSeparated_toTerminal_of_isNormalVariety
    ⟨J.isProjectiveVariety_base.toIsVariety, inferInstance⟩
  have hex := (J.isExceptional_iff PY).mpr ⟨s, hs⟩
  rw [MMP.Positivity.isExceptional_toRationalMap_iff] at hex
  have hmem : J.p PY.genericPoint ∈
      (TopologicalSpace.Closeds.closure (J.p '' (PY.idealSheaf.support : Set J.Y)) : Set X) := by
    rw [TopologicalSpace.Closeds.coe_closure]
    refine subset_closure ⟨PY.genericPoint, ?_, rfl⟩
    change PY.genericPoint ∈ PY.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hex _ hmem
  rw [hpPY, P₀.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- **The downstairs comparison is exceptional.** With `q : W ⟶ Y_i`, `r : W ⟶ X_{i+1}`
birational and `q ≫ p_i ≫ f_i = r ≫ f_i⁺`, a divisor `K_W` with `q_* K_W = K_Y` and
`r_* K_W = K_X`, and `A = q^*(K_Y + Θ_i')`, `R = r^*(K_X + B_{i+1})`, the push-forward
`r_*(A - R)` vanishes. -/
private theorem transformDivisor_sub_eq_zero {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}
    (hWp : MMP.Mori.IsProjectiveVariety ℂ (q ≫ J.sY))
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    {KW : Divisor W} {KY : Divisor J.Y} (hKY : RationalMap.transformDivisor q.toRationalMap KW = KY)
    {KX : Divisor (T.X (i + 1))} (hKX : RationalMap.transformDivisor r.toRationalMap KW = KX)
    (hYQ : (Divisor.toQDivisor KY + Θ').IsQCartier)
    (hXQ : (Divisor.toQDivisor KX + T.B (i + 1)).IsQCartier)
    (A R : QDivisor W)
    {hA₀ : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor KY + Θ').supp}
    {hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor KX + T.B (i + 1)).supp}
    (hA : (Divisor.toQDivisor KY + Θ').IsPullback q hA₀ A)
    (hR : (Divisor.toQDivisor KX + T.B (i + 1)).IsPullback r hR₀ R) :
    RationalMap.transformDivisor (X := W) r.toRationalMap (A - R) = 0 := by
  have hSi := T.isFourfoldStepDiagram i
  have hY : IsNormalVariety ℂ J.sY := J.isQFactorial.1
  have hXi1 := hSi.isNormalVariety_plus
  have hZ := hSi.isNormalVariety_target
  haveI : IsProper (q ≫ J.sY) := isProper_of_isProjectiveMorphism _ hWp.isProjective
  haveI : IsSeparated J.sY := hY.1.toIsSeparated
  haveI : IsSeparated (T.sX (i + 1)) := hXi1.1.toIsSeparated
  have hrs : r ≫ T.sX (i + 1) = q ≫ J.sY := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, ← hcomp, FourfoldCrepantJunction.sY]
    simp only [Category.assoc, hSi.comp_eq_minus]
  haveI : IsProper q := IsProper.of_comp q J.sY
  haveI : IsProper (r ≫ T.sX (i + 1)) := hrs ▸ inferInstance
  haveI : IsProper r := IsProper.of_comp r (T.sX (i + 1))
  haveI := hq.isDominant
  haveI := hr.isDominant
  haveI := J.isBirationalMorphism.isDominant
  haveI := isSeparated_toTerminal_of_isNormalVariety hY
  haveI := isSeparated_toTerminal_of_isNormalVariety hXi1
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsNormal (T.Z i) := hZ.2
  haveI : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  have hfs : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
  have hfps := hSi.isSmallMorphism_plus
  haveI : IsProper (T.f i) := hfs.isProper
  haveI : IsProper (T.fp i) := hfps.isProper
  haveI : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have hbf := hfs.isBirationalMorphism
  obtain ⟨a, -, hΘ'eq⟩ := hΘ'
  rw [RationalMap.transformDivisor]
  refine mapPrimeDivisors_eq_zero_of_forall _ fun P P₁ hP₁ => ?_
  have hrP : r P.genericPoint = P₁.genericPoint :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff r P P₁).mp hP₁
  have hV₁ := map_genericPoint_mem_biregularLocus hfps.two_le_codimension P₁
  have hζ : Order.coheight (T.fp i P₁.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _ hV₁, P₁.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor (T.Z i) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
  have hQ : T.fp i P₁.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
  have hzQ : T.f i (J.p (q P.genericPoint)) = Q.genericPoint := by
    have := congrArg (fun g : W ⟶ T.Z i => g P.genericPoint) hcomp
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, hrP, hQ]
  obtain ⟨P₀, hP₀, -⟩ := exists_primeDivisor_of_map_eq_genericPoint hbf hzQ
  obtain ⟨PY, hPY, -⟩ := exists_primeDivisor_of_map_eq_genericPoint J.isBirationalMorphism
    hP₀.symm
  have hqP : q P.genericPoint = PY.genericPoint := hPY.symm
  have hfP₀ : T.f i P₀.genericPoint = Q.genericPoint := by rwa [hP₀]
  have hpPY : J.p PY.genericPoint = P₀.genericPoint := by rw [hPY, hP₀]
  haveI := isIso_stalkMap_of_map_eq_genericPoint hq hqP
  haveI := isIso_stalkMap_of_map_eq_genericPoint hr hrP
  rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor P PY hqP hYQ hA,
    coeff_eq_of_isPullback_qDivisor P P₁ hrP hXQ hR]
  change ((KY PY : ℤ) : ℚ) + Θ' PY - (((KX P₁ : ℤ) : ℚ) + T.B (i + 1) P₁) = 0
  rw [← hKY, ← hKX, transformDivisor_apply_of_map_genericPoint hq hqP KW,
    transformDivisor_apply_of_map_genericPoint hr hrP KW,
    decreasedBoundary_apply_of_notMem_range hΘ'eq
      (notMem_range_E_of_map_genericPoint J hpPY) hpPY, T.B_eq i]
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [inverseTransformDivisor_apply_of_map_genericPoint hQ (hQ ▸ hV₁),
    transformDivisor_apply_of_map_genericPoint hbf hfP₀, sub_self]

end BridgeComparison

end

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold MMP.Positivity in
private theorem isCanonicalDivisor_four {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y} {K : Divisor J.Y}
    (P : RelativeFourfoldProgram J.sY (T.sZ i) (J.p ≫ T.f i) K Θ') :
    K.IsCanonicalDivisor J.sY 4 := by
  obtain ⟨n, hKn⟩ := P.isCanonicalDivisor
  have h4 := hKn.topologicalKrullDim_eq
  rw [J.dim_eq] at h4
  obtain rfl : n = 4 := by exact_mod_cast h4.symm
  exact hKn

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold MMP.Positivity in
/-- **The nef end of a program from the decreased pair maps crepantly to the next model.**
Let `T` be a stabilized small klt tail and `J = (p_i, Θ_i)` a crepant junction of `(X_i, B_i)`
extracting the stable low-discrepancy set `I_∞`, with decreased boundary `Θ'`. Let `P` be a
finite relative program over `Z_i` (via `f_i ∘ p_i`) from `(Y_i, Θ')` with canonical divisor `K`.
If its end `(V_m, Θ_m)` has `K_{V_m} + Θ_m` nef over `Z_i`, then there is a morphism
`p̂ : V_m ⟶ X_{i+1}` representing the birational map `V_m ⤏ X_{i+1}`, in the sense that
`f_i⁺ ∘ p̂ ∘ ψ = f_i ∘ p_i` for the composite birational map `ψ : Y_i ⤏ V_m` of `P`, such that
`K_{V_m} + Θ_m = p̂^*(K_{X_{i+1}} + B_{i+1})` with `K_{X_{i+1}} = p̂_* K_{V_m}`. -/
@[mmp "lem_oai4_c1_bridge_end_morphism"]
public theorem IsDecreasedBoundary.exists_isPullback_of_isRelativelyNef
    {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') {K : Divisor J.Y}
    (P : RelativeFourfoldProgram J.sY (T.sZ i) (J.p ≫ T.f i) K Θ')
    (hnef : QDivisor.IsRelativelyNef (P.modelStructure P.m) (P.toBase P.m)
      (Divisor.toQDivisor (P.canonical P.m) + P.endBoundary)) :
    ∃ (q : P.endModel ⟶ T.X (i + 1)),
      (P.compositeMap.compHom q).compHom (T.fp i) = (J.p ≫ T.f i).toRationalMap ∧
      ∃ hB, (Divisor.toQDivisor (RationalMap.transformDivisor q.toRationalMap (P.canonical P.m)) +
          T.B (i + 1)).IsPullback q hB
        (Divisor.toQDivisor (P.canonical P.m) + P.endBoundary) := by
  have hSi := T.isFourfoldStepDiagram i
  have hZ := hSi.isNormalVariety_target
  have hZp := hSi.isProjectiveVariety_target
  have hX1 := hSi.isNormalVariety_plus
  have hY : IsNormalVariety ℂ J.sY := J.isQFactorial.1
  have hfs : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
  have hfps := hSi.isSmallMorphism_plus
  haveI : IsIntegral (T.Z i) := hZ.1.toIsIntegral
  haveI : IsNormal (T.Z i) := hZ.2
  haveI : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  haveI : IsSeparated (T.sZ i) := hZ.1.toIsSeparated
  haveI : IsSeparated (T.sX (i + 1)) := hX1.1.toIsSeparated
  haveI : LocallyOfFiniteType (T.sX (i + 1)) := hX1.1.toLocallyOfFiniteType
  haveI : IsSeparated J.sY := hY.1.toIsSeparated
  haveI : LocallyOfFiniteType J.sY := hY.1.toLocallyOfFiniteType
  haveI : IsProper (T.f i) := hfs.isProper
  haveI : IsProper (T.fp i) := hfps.isProper
  haveI : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have hVn := fun k (hk : k ≤ P.m) => Main.isNormalVariety_modelStructure P hY hk
  have hπs := fun k (hk : k ≤ P.m) => Main.toBase_comp P hk
  have hπb := fun k (hk : k ≤ P.m) => Main.isBirationalMorphism_toBase P
    (CommonModel.isBirationalMorphism_comp J.isBirationalMorphism hfs.isBirationalMorphism) hk
  -- a smooth projective `W` with birational morphisms to every `V_k` and to `X_{i+1}`
  let Xs : Option (Fin (P.m + 1)) → Scheme.{0} := fun o => o.elim (T.X (i + 1)) fun k => P.model k
  let fs : ∀ o, Xs o ⟶ T.Z i := fun o => match o with
    | none => T.fp i
    | some k => P.toBase k
  haveI : ∀ o, IsProper (fs o) := fun o => match o with
    | none => (inferInstance : IsProper (T.fp i))
    | some k => Main.isProper_toBase P hY (Nat.lt_succ_iff.mp k.2)
  haveI : AlgebraicGeometry.IsVariety ℂ (T.sZ i) := hZ.1
  obtain ⟨W, w, hWn, hwb, gW, hWs, -, hgW, -, hWp⟩ :=
    CommonModel.exists_smooth_projective_model (k := ℂ) (T.sZ i) fs
      (fun o => match o with
        | none => hfps.isBirationalMorphism
        | some k => hπb k (Nat.lt_succ_iff.mp k.2))
      (fun o => match o with
        | none => by
          change IsNormalVariety ℂ (T.fp i ≫ T.sZ i)
          rw [hSi.comp_eq_plus]
          exact hX1
        | some k => by
          change IsNormalVariety ℂ (P.toBase k ≫ T.sZ i)
          rw [hπs k (Nat.lt_succ_iff.mp k.2)]
          exact (hVn k (Nat.lt_succ_iff.mp k.2)).1)
      (κ := Empty) (fun j => j.elim) (fun j => j.elim)
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType (w ≫ T.sZ i) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ T.sZ i)
  haveI : QuasiCompact (w ≫ T.sZ i) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ T.sZ i)
  have hWp' : MMP.Mori.IsProjectiveVariety ℂ (w ≫ T.sZ i) := hWp hZp
  haveI : IsProper (w ≫ T.sZ i) := isProper_of_isProjectiveMorphism _ hWp'.isProjective
  haveI := hwb.isDominant
  let q : ∀ k, k ≤ P.m → (W ⟶ P.model k) := fun k hk => gW (some ⟨k, Nat.lt_succ_of_le hk⟩)
  let q0 : W ⟶ J.Y := q 0 P.m.zero_le
  let r : W ⟶ T.X (i + 1) := gW none
  have hq : ∀ k (hk : k ≤ P.m), q k hk ≫ P.toBase k = w := fun k hk =>
    (hgW (some ⟨k, Nat.lt_succ_of_le hk⟩)).1
  have hqb : ∀ k (hk : k ≤ P.m), IsBirationalMorphism (q k hk) := fun k hk =>
    (hgW (some ⟨k, Nat.lt_succ_of_le hk⟩)).2.2
  have hr : r ≫ T.fp i = w := (hgW none).1
  have hrb : IsBirationalMorphism r := (hgW none).2.2
  have hqs : ∀ k (hk : k ≤ P.m), q k hk ≫ P.modelStructure k = w ≫ T.sZ i := fun k hk =>
    (congrArg (q k hk ≫ ·) (hπs k hk)).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ T.sZ i) (hq k hk)))
  have hrs : r ≫ T.sX (i + 1) = w ≫ T.sZ i := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, hr]
  have hqp : ∀ k (hk : k ≤ P.m), IsProper (q k hk) := fun k hk =>
    isProper_of_isProjectiveMorphism _ (hgW (some ⟨k, Nat.lt_succ_of_le hk⟩)).2.1
  haveI : IsProper r := isProper_of_isProjectiveMorphism _ (hgW none).2.1
  have hcomp := Main.comp_g_eq_comp_gp P
    (CommonModel.isBirationalMorphism_comp J.isBirationalMorphism hfs.isBirationalMorphism) q hq
  have hcomp0 : q0 ≫ J.p ≫ T.f i = r ≫ T.fp i := (hq 0 P.m.zero_le).trans hr.symm
  have hq0s : q0 ≫ J.sY = w ≫ T.sZ i := hqs 0 P.m.zero_le
  have hq0b : IsBirationalMorphism q0 := hqb 0 P.m.zero_le
  -- canonical divisors: `K_W` with `q_{0*} K_W = K`, and `K' = r_* K_W` on `X_{i+1}`
  have hdimW : topologicalKrullDim W = ((4 : ℕ) : WithBot ℕ∞) := by
    haveI : MMP.Mori.IsVariety ℂ (w ≫ T.sZ i) := hWn.1
    haveI : MMP.Mori.IsVariety ℂ (T.sX (i + 1)) := hX1.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (T.sX (i + 1))
      (w ≫ T.sZ i) hrb, hSi.dim_plus]
    rfl
  haveI : MMP.Mori.IsVariety ℂ (w ≫ T.sZ i) := hWn.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (w ≫ T.sZ i) hWs hdimW
  have hK := isCanonicalDivisor_four P
  haveI : IsProper q0 := hqp 0 P.m.zero_le
  haveI := hq0b.isDominant
  haveI := hrb.isDominant
  have hWn0 : IsNormalVariety ℂ (q0 ≫ J.sY) := by rwa [hq0s]
  haveI : LocallyOfFiniteType (q0 ≫ J.sY) := hWn0.1.toLocallyOfFiniteType
  obtain ⟨KW, hKW, hKWY⟩ := Main.exists_isCanonicalDivisor_transformDivisor_eq hY hWn0
    hq0b hK (K₀ := K₀) (by rwa [hq0s])
  have hWnr : IsNormalVariety ℂ (r ≫ T.sX (i + 1)) := by rwa [hrs]
  haveI : LocallyOfFiniteType (r ≫ T.sX (i + 1)) := hWnr.1.toLocallyOfFiniteType
  have hKWr : KW.IsCanonicalDivisor (r ≫ T.sX (i + 1)) 4 := by rwa [hrs, ← hq0s]
  have hTK := BridgeComparison.isCanonicalDivisor_K (T := T) (i + 1)
  have hK'c := Main.isCanonicalDivisor_transformDivisor hX1 hWnr hrb hTK hKWr
  set K' : Divisor (T.X (i + 1)) := RationalMap.transformDivisor (X := W) r.toRationalMap KW
    with hK'def
  have hlin : (T.K (i + 1)).LinearlyEquivalent K' :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (T.sX (i + 1)) hX1 hTK hK'c
  have hXQ : (Divisor.toQDivisor K' + T.B (i + 1)).IsQCartier :=
    (T.isFourfoldStepDiagram (i + 1)).isQCartier_minus.add_of_linearlyEquivalent hlin
  have hamp : (Divisor.toQDivisor K' + T.B (i + 1)).HasRelativelyAmpleMultiple (T.fp i) := by
    refine Main.hasRelativelyAmpleMultiple_add_of_linearlyEquivalent ?_ hlin
    rw [T.K_eq i, T.B_eq i]
    exact hSi.hasRelativelyAmpleMultiple_plus
  -- the three pull-backs `A = q_0^*(K + Θ')`, `A₁ = q_m^*(K_m + Θ_m)`, `R = r^*(K' + B_{i+1})`
  have hYQ : (Divisor.toQDivisor K + Θ').IsQCartier :=
    isQCartier_of_isQFactorial J.sY J.isQFactorial _
  obtain ⟨hDm, -⟩ := id hnef
  have h₀ : ∀ Z : irreducibleComponents W,
      q0 (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + Θ').supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  haveI := (hqb P.m le_rfl).isDominant
  have hₘ : ∀ Z : irreducibleComponents W, q P.m le_rfl (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor (P.canonical P.m) + P.endBoundary).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K' + T.B (i + 1)).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hA := QDivisor.isPullback_pullback hYQ h₀
  have hA₁ := QDivisor.isPullback_pullback hDm hₘ
  have hR := QDivisor.isPullback_pullback hXQ hR₀
  set A := (Divisor.toQDivisor K + Θ').pullback hYQ h₀
  set A₁ := (Divisor.toQDivisor (P.canonical P.m) + P.endBoundary).pullback hDm hₘ
  set R := (Divisor.toQDivisor K' + T.B (i + 1)).pullback hXQ hR₀
  -- `A = A₁ + F₁` with `F₁ ≥ 0`, `q_{m*} F₁ = 0`
  have hF₁ : 0 ≤ A - A₁ :=
    ProgramComparison.pullback_zero_sub_pullback_nonneg P.m P.modelStructure P.canonical
      P.boundary P.sT P.g P.gp (fun k hk => P.isFourfoldStepDiagram k hk) P.KY_eq P.ΘY_eq
      (w ≫ T.sZ i) hWp' hWn q hqs hqb hcomp hYQ hDm h₀ hₘ
  have hF₁₀ : RationalMap.transformDivisor (X := W) (q P.m le_rfl).toRationalMap (A - A₁) = 0 :=
    StepChain.transformDivisor_pullback_sub_pullback_eq_zero P.m P.modelStructure P.canonical
      P.boundary P.sT P.g P.gp (fun k hk => P.isFourfoldStepDiagram k hk) P.KY_eq P.ΘY_eq
      q hqb hcomp hYQ hDm h₀ hₘ
  -- `A = R + F₂` with `F₂ ≥ 0`, `r_* F₂ = 0`
  have hWp0 : MMP.Mori.IsProjectiveVariety ℂ (q0 ≫ J.sY) := by rwa [hq0s]
  have hF₂ : 0 ≤ A - R :=
    BridgeComparison.pullback_sub_pullback_nonneg hΘ' hWp0 (by rwa [hq0s])
      hq0b hrb hcomp0 hKW hKWY hK'c hXQ hamp rfl A R h₀ hR₀ hA hR
  have hF₂₀ : RationalMap.transformDivisor (X := W) r.toRationalMap (A - R) = 0 :=
    BridgeComparison.transformDivisor_sub_eq_zero hΘ' hWp0
      hq0b hrb hcomp0 hKWY rfl hYQ hXQ A R hA hR
  -- the two ends
  haveI : QuasiCompact (P.modelStructure P.m) := (hVn P.m le_rfl).1.1.toQuasiCompact
  obtain ⟨h, hqh, hhπ, hD, hpb⟩ := TwoEnds.exists_hom_isPullback ℂ
    (P.modelStructure P.m) (T.sX (i + 1)) (hVn P.m le_rfl).1 hX1 (P.toBase P.m) (T.fp i)
    hDm hXQ hnef hamp (q P.m le_rfl) r (by rwa [hqs P.m le_rfl]) (hqb P.m le_rfl) hrb
    ((hqs P.m le_rfl).trans hrs.symm) ((hq P.m le_rfl).trans hr.symm) hₘ hR₀ hA₁ hR hF₁ hF₂
    hF₁₀ hF₂₀ (by abel)
  -- `p̂ = h` represents `V_m ⤏ X_{i+1}`, and `K' = p̂_* K_m`
  haveI : IsSeparated (P.modelStructure P.m) := (hVn P.m le_rfl).1.1.toIsSeparated
  have hhs : h ≫ T.sX (i + 1) = P.modelStructure P.m := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, hhπ, hπs P.m le_rfl]
  haveI : LocallyOfFiniteType (P.modelStructure P.m) := (hVn P.m le_rfl).1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (h ≫ T.sX (i + 1)) := by rw [hhs]; infer_instance
  haveI : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h (T.sX (i + 1))
  haveI : IsSeparated (h ≫ T.sX (i + 1)) := by rw [hhs]; infer_instance
  haveI : IsSeparated h := IsSeparated.of_comp h (T.sX (i + 1))
  have hhb' : IsBirationalMorphism h :=
    Main.isBirationalMorphism_of_comp_left (q P.m le_rfl) h (hqb P.m le_rfl) (hqh ▸ hrb)
  haveI := isSeparated_toTerminal_of_isNormalVariety hX1
  haveI := isSeparated_toTerminal_of_isNormalVariety hY
  have hKh : RationalMap.transformDivisor h.toRationalMap (P.canonical P.m) = K' := by
    refine Finsupp.ext fun Q => ?_
    obtain ⟨E, hE, -, htrE⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX1 hWnr hrb Q
    rw [hK'def, htrE]
    have hx : h (q P.m le_rfl E.genericPoint) = Q.genericPoint := by
      rw [← Scheme.Hom.comp_apply, hqh, hE]
    obtain ⟨Pm, hPm, -⟩ :=
      BridgeComparison.exists_primeDivisor_of_map_eq_genericPoint hhb' hx
    rw [transformDivisor_apply_of_map_genericPoint hhb'
      (show h Pm.genericPoint = Q.genericPoint by rwa [hPm])]
    obtain ⟨P₀, hP₀, hB⟩ := StepChain.exists_primeDivisor_zero_forall_coeff_eq
      (fun k hk => P.isFourfoldStepDiagram k hk) hcomp E.genericPoint P.m le_rfl Pm hPm.symm
    rw [hB P.canonical P.KY_eq]
    change K P₀ = KW E
    rw [← hKWY, transformDivisor_apply_of_map_genericPoint
      hq0b (show q0 E.genericPoint = P₀.genericPoint from hP₀)]
  refine ⟨h, ?_, ?_⟩
  · rw [Main.compHom_compHom, hhπ, P.compHom_compositeMap]
  · rw [hKh]
    exact ⟨hD, hpb⟩

/-! ### No divisor is lost -/

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold TopologicalSpace

namespace Lost

section NotSmall

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- Over a point `y` of codimension one of `Z` lies at most one point of `X⁻` of codimension
one: both define divisorial valuations of `k(Z) = k(X⁻)` dominating the discrete valuation ring
`𝒪_{Z,y}`. -/
private theorem eq_of_coheight_eq_one
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) {x₁ x₂ : Xm}
    (h₁ : Order.coheight x₁ = 1) (h₂ : Order.coheight x₂ = 1) (he : fm x₁ = fm x₂)
    (hy : Order.coheight (fm x₂) = 1) : x₁ = x₂ := by
  haveI := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  let P₁ : MMP.Mori.PrimeDivisor Xm := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x₁ h₁
  let P₂ : MMP.Mori.PrimeDivisor Xm := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x₂ h₂
  let Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (fm x₂) hy
  have hnZ : IsNormalVariety ℂ (fm ≫ sZ) := by rw [h.comp_eq_minus]; exact h.isNormalVariety_minus
  let D₁ : MMP.Mori.DivisorOver ℂ sZ :=
    ⟨Xm, fm, hnZ, h.isBirationalMorphism_minus, P₁⟩
  let D₂ : MMP.Mori.DivisorOver ℂ sZ :=
    ⟨Xm, fm, hnZ, h.isBirationalMorphism_minus, P₂⟩
  have hv₁ := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq
    h.isNormalVariety_target D₁ Q (by
      simp [D₁, P₁, Q, MMP.Mori.PrimeDivisor.genericPoint,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, he])
  have hv₂ := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq
    h.isNormalVariety_target D₂ Q (by
      simp [D₂, P₂, Q, MMP.Mori.PrimeDivisor.genericPoint,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne])
  have hbij := MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective
    h.isBirationalMorphism_minus
  let F₁ := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus P₁
  let F₂ := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus P₂
  have hF : F₁.valuation = F₂.valuation := by
    ext g
    obtain ⟨g', rfl⟩ := hbij.2 g
    have := DFunLike.congr_fun (hv₁.trans hv₂.symm) g'
    change P₁.divisorialValuation (functionFieldMap (𝟙 Xm) (functionFieldMap fm g')) =
      P₂.divisorialValuation (functionFieldMap (𝟙 Xm) (functionFieldMap fm g'))
    rwa [MMP.Mori.functionFieldMap_id_apply]
  have h' : P₁.genericPoint = P₂.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq h.isNormalVariety_minus.1 hF
  simpa [F₁, F₂, P₁, P₂, MMP.Mori.PrimeDivisor.genericPoint,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] using h'

/-- **A non-small `f⁻` contracts a prime divisor.** In a step diagram in which `f⁻` is not
small, some prime divisor `E` of `X⁻` has image `f⁻(E)` of codimension at least two. -/
private theorem exists_primeDivisor_two_le_coheight_map
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hfm : ¬ IsSmallMorphism sXm sZ fm) :
    ∃ E : MMP.Mori.PrimeDivisor Xm, 2 ≤ Order.coheight (fm E.genericPoint) := by
  haveI := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI : IsNormal Z := h.isNormalVariety_target.2
  haveI := h.isNormalVariety_target.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_minus
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    h.isBirationalMorphism_minus
  have hcod : ¬ 2 ≤ MMP.Mori.closedsCodimension (exceptionalSet fm) := fun h2 =>
    hfm ⟨h.isNormalVariety_minus, h.isNormalVariety_target, h.comp_eq_minus, inferInstance,
      h.isBirationalMorphism_minus, h2⟩
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at hcod
  push Not at hcod
  obtain ⟨x, hxE, hx2⟩ := hcod
  have hfin : ∀ y : Z, (fm ⁻¹' {y}).Finite → y ∈ biregularLocus fm := fun y hy => by
    obtain ⟨hU, hiso⟩ :=
      (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso fm hb).1 inferInstance
    exact le_biregularLocus hiso hy
  have hgen : fm x ≠ genericPoint Z := by
    intro hg
    refine mem_exceptionalSet.mp hxE (hfin _ ?_)
    rw [hg, preimage_genericPoint fm hb]
    exact Set.finite_singleton _
  have hone : ∀ p : Xm, Order.coheight p ≤ 1 → fm p ≠ genericPoint Z → Order.coheight p = 1 := by
    intro p hp hpg
    refine le_antisymm hp (ENat.one_le_iff_ne_zero.mpr fun h0 => hpg ?_)
    have hmax : IsMax p := Order.coheight_eq_zero.mp h0
    have hgp : p = genericPoint Xm :=
      (Specializes.antisymm (hmax (genericPoint_specializes p)) (genericPoint_specializes p)).eq
    rw [hgp]
    exact MMP.Positivity.map_genericPoint_eq_of_isDominant fm
  have hx1 : Order.coheight x = 1 :=
    hone x (Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using hx2)) hgen
  have hdim : topologicalKrullDim Xm = topologicalKrullDim Z :=
    haveI := h.isNormalVariety_minus.1
    haveI := h.isNormalVariety_target.1
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sXm
      h.isBirationalMorphism_minus).symm
  have hmono : ∀ p : Xm, Order.coheight p ≤ Order.coheight (fm p) :=
    MMP.Flips.coheight_le_coheight_map sZ sXm h.isNormalVariety_target.1
      h.isNormalVariety_minus.1 fm h.comp_eq_minus hdim
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1, ?_⟩
  have hgx : MMP.Mori.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1) = x := by
    simp [MMP.Mori.PrimeDivisor.genericPoint,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  rw [hgx]
  by_contra! hlt
  have hy1 : Order.coheight (fm x) = 1 :=
    le_antisymm (Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using hlt)) (hx1 ▸ hmono x)
  refine mem_exceptionalSet.mp hxE (hfin _ ((Set.finite_singleton x).subset fun p hp => ?_))
  have hp : fm p = fm x := hp
  have hp1 : Order.coheight p = 1 :=
    hone p (hy1 ▸ hp ▸ hmono p) (hp ▸ hgen)
  exact eq_of_coheight_eq_one h hp1 hx1 hp hy1

end NotSmall

section Ray

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Intersection numbers depend only on numerical classes: if `[C] = c [C₀]` in `N₁(X)`, then
`(D · C) = c (D · C₀)` for every `ℚ`-Cartier `ℚ`-divisor `D`. -/
private theorem intersectionNumber_eq_mul_of_numericalClass_eq {D : QDivisor X}
    (hD : D.IsQCartier) (C C₀ : ProperCurve sX) {c : ℝ}
    (h : OneCycle.numericalClass sX (C.cycle ℝ) =
      c • OneCycle.numericalClass sX (C₀.cycle ℝ)) :
    (D.intersectionNumber k sX C.ι C.dim_le hD : ℝ) =
      c * D.intersectionNumber k sX C₀.ι C₀.dim_le hD := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  have hF := QDivisor.isCartierDivisor_cartierIndex_smul hD
  haveI := hF.isCartier_toDivisor.isInvertibleModule_divisorialSheaf
  rw [← map_smul] at h
  have h1 := (OneCycle.numericalClass_eq_iff.mp h) hF.toDivisor.divisorialSheaf
  rw [map_smul, OneCycle.degree_cycle, OneCycle.degree_cycle] at h1
  have e1 : C.degree k hF.toDivisor.divisorialSheaf =
      hF.toDivisor.degreeOn k sX C.ι C.dim_le hF.isCartier_toDivisor := rfl
  have e2 : C₀.degree k hF.toDivisor.divisorialSheaf =
      hF.toDivisor.degreeOn k sX C₀.ι C₀.dim_le hF.isCartier_toDivisor := rfl
  rw [e1, e2, smul_eq_mul] at h1
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD _
      hF.isCartier_toDivisor hF.toQDivisor_toDivisor,
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C₀.ι C₀.dim_le D hD _
      hF.isCartier_toDivisor hF.toQDivisor_toDivisor]
  push_cast
  rw [h1]
  ring

/-- **Perturbing along a divisor.** Let `g : X ⟶ T` contract exactly the curves whose classes
lie in the ray `R = ℝ_{≥0} [C₀]`, and let `-D` have a `g`-ample multiple. For every `ℚ`-Cartier
`ℚ`-divisor `E` there is `ε > 0` such that `-(D - εE)` is `g`-nef: on the ray, both are
multiples of their values at `C₀`, and `(-D · C₀) > 0`. -/
private theorem exists_isRelativelyNef_neg_sub_smul {X T : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {g : X ⟶ T}
    (C₀ : ProperCurve sX) {R : Set (NumericalCurveClasses sX)}
    (hR : R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C₀.cycle ℝ) = u})
    (hcon : ∀ C : ProperCurve sX,
      C.IsContractedBy g ↔ OneCycle.numericalClass sX (C.cycle ℝ) ∈ R)
    {D : QDivisor X} (hD : D.IsQCartier) (hamp : (-D).HasRelativelyAmpleMultiple g)
    {E : QDivisor X} (hE : E.IsQCartier) :
    ∃ ε : ℚ, 0 < ε ∧ (-(D - ε • E)).IsRelativelyNef sX g := by
  have hnD := isQCartier_neg hD
  have hC₀ : C₀.IsContractedBy g :=
    (hcon C₀).mpr (by rw [hR]; exact ⟨1, zero_le_one, one_smul _ _⟩)
  set δ := (-D).intersectionNumber ℂ sX C₀.ι C₀.dim_le hnD with hδdef
  have hδ : 0 < δ :=
    TwoEnds.intersectionNumber_pos_of_hasRelativelyAmpleMultiple sX hnD hamp C₀ hC₀
  set π := E.intersectionNumber ℂ sX C₀.ι C₀.dim_le hE with hπdef
  have hp : 0 < |π| + 1 := by positivity
  refine ⟨δ / (|π| + 1), by positivity, ?_⟩
  set ε := δ / (|π| + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hsE := MMP.Flips.QDivisor.IsQCartier.qsmul hE ε
  have hDε : (-(D - ε • E)).IsQCartier := by
    rw [show -(D - ε • E) = -D + ε • E by abel]
    exact hnD.add hsE
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hDε
    fun C hC => ?_
  have hmem := (hcon C).mp hC
  rw [hR] at hmem
  obtain ⟨c, hc, hcC⟩ := hmem
  have e1 : (-(D - ε • E)).intersectionNumber ℂ sX C.ι C.dim_le hDε =
      (-D).intersectionNumber ℂ sX C.ι C.dim_le hnD +
        ε * E.intersectionNumber ℂ sX C.ι C.dim_le hE := by
    rw [MMP.Fourfold.intersectionNumber_congr sX C.ι C.dim_le hDε (hnD.add hsE) (by abel),
      QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le _ _ hnD hsE,
      MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le E hE ε hsE]
  have h1 := intersectionNumber_eq_mul_of_numericalClass_eq hnD C C₀ hcC.symm
  have h2 := intersectionNumber_eq_mul_of_numericalClass_eq hE C C₀ hcC.symm
  have hb : 0 ≤ δ + ε * π := by
    have h3 : ε * |π| ≤ δ := by
      rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ hp]
      nlinarith [abs_nonneg π]
    nlinarith [neg_abs_le π, mul_le_mul_of_nonneg_left (neg_abs_le π) hε.le]
  have hb' : (0 : ℝ) ≤ (δ : ℝ) + (ε : ℝ) * (π : ℝ) := by exact_mod_cast hb
  have key : (0 : ℝ) ≤ (((-D).intersectionNumber ℂ sX C.ι C.dim_le hnD +
      ε * E.intersectionNumber ℂ sX C.ι C.dim_le hE : ℚ) : ℝ) := by
    push_cast
    rw [h1, h2]
    nlinarith [mul_nonneg hc hb']
  rw [e1]
  exact_mod_cast key

end Ray

end Lost

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold TopologicalSpace

namespace Lost

/-! ### A lost divisor improves strictly -/

/-- **A lost divisor improves strictly.** Let `(X⁻, Θ⁻) → T ← (X⁺, Θ⁺)` be a step diagram with
`K⁺ + Θ⁺` the strict transform of `K⁻ + Θ⁻`, `X⁻` `ℚ`-factorial and `g` contracting exactly the
curves with class on a ray `ℝ_{≥0} [C₀]`, and let `q : W ⟶ X⁻`, `p : W ⟶ X⁺` be birational with
`q ≫ g = p ≫ g⁺`. If a prime divisor `P` of `X⁻` has image of codimension at least two in `T`,
then `q^*(K⁻ + Θ⁻) - p^*(K⁺ + Θ⁺)` is positive along the strict transform `E` of `P`: for small
`ε > 0`, `-(K⁻ + Θ⁻ - εP)` is still `g`-nef, so the negativity lemma along `p` makes
`q^*(K⁻ + Θ⁻ - εP) - p^*(K⁺ + Θ⁺)` effective, and its coefficient at `E` is that of the
comparison divisor minus `ε`. -/
private theorem pullback_sub_pullback_pos
    {Xm Xp T W : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {Θ : QDivisor Xm} {g : Xm ⟶ T} {gp : Xp ⟶ T}
    (hS : IsFourfoldStepDiagram sXm sT sXp K Θ g gp) {Kp : Divisor Xp} {Θp : QDivisor Xp}
    (hK : Kp = flipTransform g gp K) (hΘ : Θp = flipTransform g gp Θ)
    (hQf : IsQFactorial sXm) (C₀ : ProperCurve sXm) {R : Set (NumericalCurveClasses sXm)}
    (hR : R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C₀.cycle ℝ) = u})
    (hcon : ∀ C : ProperCurve sXm,
      C.IsContractedBy g ↔ OneCycle.numericalClass sXm (C.cycle ℝ) ∈ R)
    (sW : W ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWn : IsNormalVariety ℂ sW) (q₁ : W ⟶ Xm) (q₂ : W ⟶ Xp) (hqs₁ : q₁ ≫ sXm = sW)
    (hqs₂ : q₂ ≫ sXp = sW) (hq₁ : IsBirationalMorphism q₁)
    (hq₂ : IsBirationalMorphism q₂) (hcomp : q₁ ≫ g = q₂ ≫ gp)
    (P : MMP.Mori.PrimeDivisor Xm) (hP : 2 ≤ Order.coheight (g P.genericPoint))
    (E : MMP.Mori.PrimeDivisor W) (hE : q₁ E.genericPoint = P.genericPoint)
    (hD₁ : (Divisor.toQDivisor K + Θ).IsQCartier)
    (hD₂ : (Divisor.toQDivisor Kp + Θp).IsQCartier)
    (h₁ : ∀ Z : irreducibleComponents W,
      q₁ (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + Θ).supp)
    (h₂ : ∀ Z : irreducibleComponents W,
      q₂ (componentGenericPoint W Z) ∉ (Divisor.toQDivisor Kp + Θp).supp) :
    0 < ((Divisor.toQDivisor K + Θ).pullback hD₁ h₁ -
      (Divisor.toQDivisor Kp + Θp).pullback hD₂ h₂) E := by
  subst hK hΘ
  haveI : IsProper sW := isProper_of_isProjectiveMorphism _ hW.isProjective
  haveI := hS.isNormalVariety_minus.1
  haveI := hS.isNormalVariety_plus.1
  haveI := ProgramComparison.isProper_of_comp_eq q₁ hqs₁
  haveI := ProgramComparison.isProper_of_comp_eq q₂ hqs₂
  haveI := hq₁.isDominant
  haveI := hq₂.isDominant
  haveI := isSeparated_toTerminal_of_isNormalVariety hS.isNormalVariety_plus
  set D := Divisor.toQDivisor K + Θ with hDdef
  set Pd : QDivisor Xm := Finsupp.single P 1 with hPd
  obtain ⟨ε, hε, hnef⟩ := exists_isRelativelyNef_neg_sub_smul C₀ hR hcon hD₁
    hS.hasRelativelyAmpleMultiple_minus (isQCartier_of_isQFactorial sXm hQf Pd)
  set D' := D - ε • Pd with hD'def
  have hD' : D'.IsQCartier := isQCartier_of_isQFactorial sXm hQf D'
  have h₁' : ∀ Z : irreducibleComponents W, q₁ (componentGenericPoint W Z) ∉ D'.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hp₁ := QDivisor.isPullback_pullback hD₁ h₁
  have hp₁' := QDivisor.isPullback_pullback hD' h₁'
  have hp₂ := QDivisor.isPullback_pullback hD₂ h₂
  have hP₁' := hp₁'.isQCartier hD'
  have hP₂ := hp₂.isQCartier hD₂
  -- no prime divisor over a divisor of `T` is `P`
  have hne : ∀ (Pm : MMP.Mori.PrimeDivisor Xm) (Q : MMP.Mori.PrimeDivisor Xp),
      g Pm.genericPoint = gp Q.genericPoint → Pm ≠ P := by
    rintro Pm Q he rfl
    have h1 : Order.coheight (gp Q.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _
        (map_genericPoint_mem_biregularLocus hS.isSmallMorphism_plus.two_le_codimension Q),
        Q.coheight_genericPoint]
    rw [he, h1] at hP
    exact absurd hP (by decide)
  -- `F = q^*(D - εP) - p^*D⁺` is effective
  have hF : 0 ≤ D'.pullback hD' h₁' -
      (Divisor.toQDivisor (flipTransform g gp K) + flipTransform g gp Θ).pullback hD₂ h₂ := by
    refine Negativity.nonneg_of_transformDivisor_nonneg ℂ sXp sW hS.isNormalVariety_plus hWn
      q₂ hqs₂ hq₂ ?_ ?_
    · rw [show -(D'.pullback hD' h₁' -
          (Divisor.toQDivisor (flipTransform g gp K) + flipTransform g gp Θ).pullback hD₂ h₂) =
          (Divisor.toQDivisor (flipTransform g gp K) + flipTransform g gp Θ).pullback hD₂ h₂ +
            -D'.pullback hD' h₁' by abel]
      have hnA := isQCartier_neg hP₁'
      refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sW
        (hP₂.add hnA) fun C hC => ?_
      rw [QDivisor.intersectionNumber_add' ℂ sW C.ι C.dim_le _ _ hP₂ hnA]
      refine add_nonneg (intersectionNumber_nonneg_of_isPullback q₂ hqs₂
        hS.hasRelativelyAmpleMultiple_plus hp₂ hP₂ C fun x hx => by
          simp only [Scheme.Hom.comp_apply, hC x hx]) ?_
      exact intersectionNumber_isPullback_nonneg q₁ hqs₁ g (isQCartier_neg hD') hnef
        (isPullback_neg hp₁'
          (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _))
        C (by rw [hcomp]; intro x hx; simp only [Scheme.Hom.comp_apply, hC x hx])
    · refine le_of_eq (Eq.symm ?_)
      rw [RationalMap.transformDivisor]
      refine mapPrimeDivisors_eq_zero_of_forall _ fun E₀ Q hEQ => ?_
      have hE₀ := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q₂ E₀ Q).mp hEQ
      have hx : g (q₁ E₀.genericPoint) = gp Q.genericPoint := by
        rw [← hE₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]
      obtain ⟨Pm, hPm, hfl⟩ := StepChain.exists_eq_genericPoint_flipTransform_apply hS Q
        (q₁ E₀.genericPoint) hx
      have hPm' : q₁ E₀.genericPoint = Pm.genericPoint := hPm
      haveI := isIso_stalkMap_of_map_eq_genericPoint hq₁ hPm'
      haveI := isIso_stalkMap_of_map_eq_genericPoint hq₂ hE₀
      rw [Finsupp.sub_apply, coeff_eq_of_isPullback_qDivisor E₀ Pm hPm' hD' hp₁',
        coeff_eq_of_isPullback_qDivisor E₀ Q hE₀ hD₂ hp₂]
      have hPmP : Pm ≠ P := hne Pm Q (by rw [← hPm', hx])
      have hPd0 : Pd Pm = 0 := Finsupp.single_eq_of_ne hPmP
      change ((K Pm : ℤ) : ℚ) + Θ Pm - ε * Pd Pm -
        (((flipTransform g gp K Q : ℤ) : ℚ) + flipTransform g gp Θ Q) = 0
      rw [hfl K, hfl Θ, hPd0]
      ring
  -- read off the coefficient at `E`
  have h1 := hF E
  haveI := isIso_stalkMap_of_map_eq_genericPoint hq₁ hE
  have e1 := coeff_eq_of_isPullback_qDivisor E P hE hD' hp₁'
  have e2 := coeff_eq_of_isPullback_qDivisor E P hE hD₁ hp₁
  rw [Finsupp.sub_apply, e2]
  rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply, e1] at h1
  have hPP : Pd P = 1 := Finsupp.single_eq_same
  have : D' P = D P - ε := by
    rw [hD'def, Finsupp.sub_apply, Finsupp.smul_apply, hPP, smul_eq_mul, mul_one]
  linarith

end Lost

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold TopologicalSpace

namespace Lost

/-! ### The marked divisors are crepant over the next model -/

/-- **The marked divisors are crepant.** With `q : W ⟶ Y_i`, `r : W ⟶ X_{i+1}` birational,
`q ≫ p_i ≫ f_i = r ≫ f_i⁺`, a canonical divisor `K_W` with `q_* K_W = K_Y` and `r_* K_W = K_X`,
`A = q^*(K_Y + Θ_i')` and `R = r^*(K_X + B_{i+1})`: at a prime divisor `P` of `W` over a marked
divisor `E_{i,s}` the two pull-backs agree, since the coefficient `1 - a_{i+1}(s)` of `Θ_i'` at
`E_{i,s}` is the one `(W, r, P)` computes from `a(s; X_{i+1}, B_{i+1}) = a_{i+1}(s)`. -/
private theorem coeff_pullback_eq_of_map_genericPoint_eq_E {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ')
    {W : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {q : W ⟶ J.Y} {r : W ⟶ T.X (i + 1)}
    (hWp : MMP.Mori.IsProjectiveVariety ℂ (q ≫ J.sY))
    (hq : IsBirationalMorphism q) (hr : IsBirationalMorphism r)
    (hcomp : q ≫ J.p ≫ T.f i = r ≫ T.fp i)
    {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (q ≫ J.sY) 4)
    {KY : Divisor J.Y} (hKY : RationalMap.transformDivisor q.toRationalMap KW = KY)
    {KX : Divisor (T.X (i + 1))} (hKXc : KX.IsCanonicalDivisor (T.sX (i + 1)) 4)
    (hXQ : (Divisor.toQDivisor KX + T.B (i + 1)).IsQCartier)
    (hKX : RationalMap.transformDivisor r.toRationalMap KW = KX)
    (hYQ : (Divisor.toQDivisor KY + Θ').IsQCartier) {A R : QDivisor W}
    {hA₀ : ∀ Z : irreducibleComponents W,
      q (componentGenericPoint W Z) ∉ (Divisor.toQDivisor KY + Θ').supp}
    {hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor KX + T.B (i + 1)).supp}
    (hA : (Divisor.toQDivisor KY + Θ').IsPullback q hA₀ A)
    (hR : (Divisor.toQDivisor KX + T.B (i + 1)).IsPullback r hR₀ R)
    (P : MMP.Mori.PrimeDivisor W) (s : I) (hPQ' : q P.genericPoint = (J.E s).genericPoint) :
    A P = R P := by
  have hSi := T.isFourfoldStepDiagram i
  have hY : IsNormalVariety ℂ J.sY := J.isQFactorial.1
  have hWn : IsNormalVariety ℂ (q ≫ J.sY) := ⟨hWp.toIsVariety, inferInstance⟩
  haveI : IsProper (q ≫ J.sY) := isProper_of_isProjectiveMorphism _ hWp.isProjective
  haveI : IsSeparated J.sY := hY.1.toIsSeparated
  haveI : IsSeparated (T.sX (i + 1)) := hSi.isNormalVariety_plus.1.toIsSeparated
  have hrs : r ≫ T.sX (i + 1) = q ≫ J.sY := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, ← hcomp, FourfoldCrepantJunction.sY]
    simp only [Category.assoc, hSi.comp_eq_minus]
  haveI : IsProper q := IsProper.of_comp q J.sY
  haveI : IsProper (r ≫ T.sX (i + 1)) := hrs ▸ inferInstance
  haveI : IsProper r := IsProper.of_comp r (T.sX (i + 1))
  have hXi1 := hSi.isNormalVariety_plus
  have hZ := hSi.isNormalVariety_target
  haveI := hq.isDominant
  haveI := hr.isDominant
  haveI := J.isBirationalMorphism.isDominant
  haveI := isSeparated_toTerminal_of_isNormalVariety hY
  haveI := isSeparated_toTerminal_of_isNormalVariety hXi1
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsNormal (T.Z i) := hZ.2
  haveI : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  haveI := hXi1.1.toLocallyOfFiniteType
  have hfs : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
  have hfps := hSi.isSmallMorphism_plus
  haveI : IsProper (T.f i) := hfs.isProper
  haveI : IsProper (T.fp i) := hfps.isProper
  have hWn' : IsNormalVariety ℂ (r ≫ T.sX (i + 1)) := hrs ▸ hWn
  haveI : LocallyOfFiniteType (r ≫ T.sX (i + 1)) := hWn'.1.toLocallyOfFiniteType
  obtain ⟨a, ha, hΘ'eq⟩ := hΘ'
  haveI := isIso_stalkMap_of_map_eq_genericPoint hq hPQ'
  rw [coeff_eq_of_isPullback_qDivisor P (J.E s) hPQ' hYQ hA]
  change ((KY (J.E s) : ℤ) : ℚ) + Θ' (J.E s) = R P
  rw [← hKY, transformDivisor_apply_of_map_genericPoint hq hPQ' KW,
    BridgeComparison.decreasedBoundary_apply_E hΘ'eq]
  obtain ⟨s', hts, n, D', -, hD'v, hD'log⟩ := ha s
  have hval : D'.valuation =
      (⟨W, r, hWn', hr, P⟩ : DivisorOver ℂ (T.sX (i + 1))).valuation := by
    rw [hD'v]
    refine valuation_eq_of_comap_eq
      hfps.isBirationalMorphism.functionFieldMap_bijective.2 (hts.trans ?_)
    refine Valuation.ext fun t => ?_
    rw [Valuation.comap_apply, Valuation.comap_apply]
    change _ = P.divisorialValuation (functionFieldMap r (functionFieldMap (T.fp i) t))
    rw [functionFieldMap_comp_apply r (T.fp i) hcomp.symm,
      ← functionFieldMap_comp_apply q (J.p ≫ T.f i) rfl,
      ← functionFieldMap_comp_apply J.p (T.f i) rfl,
      ← PrimeDivisor.valuationOver_apply, valuationOver_eq_of_isIso q P (J.E s) hPQ',
      ← J.valuation_eq s]
    rfl
  have := BridgeComparison.coeff_isPullback_eq_of_isLogDiscrepancy hXi1 hKXc hXQ hr
    hWn' (hrs ▸ hKW) hKX hR P hD'log hval
  exact_mod_cast (show (((KW P : ℚ) + (1 - a s) : ℚ) : ℝ) = ((R P : ℚ) : ℝ) by
    push_cast; linarith)

/-! ### The end morphism lies over the base -/

/-- Pull-backs of equal `ℚ`-Cartier divisors along equal morphisms are equal. -/
private theorem eq_of_isPullback {X Y : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f f' : X ⟶ Y} (hf : f = f')
    {D D' : QDivisor Y} (hD : D = D') (hDq : D.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    {hB' : ∀ Z : irreducibleComponents X, f' (componentGenericPoint X Z) ∉ D'.supp}
    {A A' : QDivisor X} (h : D.IsPullback f hB A) (h' : D'.IsPullback f' hB' A') : A = A' := by
  subst hf hD
  exact (hDq.existsUnique_isPullback hB).unique h h'

/-! ### Codimension along the program -/

/-- **A lost divisor stays lost.** In a chain of step diagrams `V_l → T_l ← V_{l+1}` with
compatible `q_l : W ⟶ V_l`, if `g_k(q_k(w))` has codimension at least two, then `q_l(w)` is not
the generic point of a prime divisor for `k < l ≤ m`: over the generic point of a prime divisor
of `V_{l+1}` lies one of `V_l` (`g_l⁺` is small), and `g_k⁺` maps the generic point of a prime
divisor of `V_{k+1}` to a point of codimension one. -/
private theorem ne_genericPoint_of_two_le_coheight {m : ℕ} {V : ℕ → Scheme.{0}}
    {sV : ∀ k, V k ⟶ Spec (.of ℂ)} [∀ k, IsIntegral (V k)] [∀ k, CompactSpace (V k)]
    [∀ k, IsLocallyNoetherian (V k)] [∀ k, IsNormal (V k)] {K : ∀ k, Divisor (V k)}
    {Θ : ∀ k, QDivisor (V k)} {T : ℕ → Scheme.{0}} {sT : ∀ k, T k ⟶ Spec (.of ℂ)}
    {g : ∀ k, V k ⟶ T k} {gp : ∀ k, V (k + 1) ⟶ T k} {W : Scheme.{0}}
    {q : ∀ k, k ≤ m → (W ⟶ V k)}
    (hstep : ∀ k < m, IsFourfoldStepDiagram (sV k) (sT k) (sV (k + 1)) (K k) (Θ k) (g k) (gp k))
    (hcomp : ∀ k (hk : k < m), q k (Nat.le_of_lt hk) ≫ g k = q (k + 1) hk ≫ gp k) (w : W)
    {k : ℕ} (hk : k < m) (hw : 2 ≤ Order.coheight (g k (q k hk.le w))) :
    ∀ l, k + 1 ≤ l → ∀ (hl : l ≤ m) (Q : MMP.Mori.PrimeDivisor (V l)),
      q l hl w ≠ Q.genericPoint := by
  intro l hkl
  induction l, hkl using Nat.le_induction with
  | base =>
    intro hl Q hQ
    have hx : g k (q k hk.le w) = gp k Q.genericPoint := by
      rw [← hQ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp k hk]
    have h1 : Order.coheight (gp k Q.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _
        (map_genericPoint_mem_biregularLocus (hstep k hk).isSmallMorphism_plus.two_le_codimension
          Q), Q.coheight_genericPoint]
    rw [hx, h1] at hw
    exact absurd hw (by decide)
  | succ l hkl ih =>
    intro hl Q hQ
    obtain ⟨Pl, hPl, -⟩ := StepChain.exists_eq_genericPoint_flipTransform_apply
      (hstep l hl) Q (q l (Nat.le_of_lt hl) w)
      (by rw [← hQ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp l hl])
    exact ih (Nat.le_of_lt hl) Pl hPl

end Lost

end

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold MMP.Positivity in
/-- **No divisor is lost in a program from the decreased pair.** Let `T` be a stabilized small
klt tail and `J = (p_i, Θ_i)` a crepant junction of `(X_i, B_i)` extracting the stable
low-discrepancy set `I_∞`, with decreased boundary `Θ'`. Let `P` be a finite relative program
over `Z_i` (via `f_i ∘ p_i`) from `(Y_i, Θ')`. If its end `(V_m, Θ_m)` has `K_{V_m} + Θ_m` nef
over `Z_i`, then each contraction `g_k : V_k ⟶ T_k`, `k < m`, is a small morphism. -/
@[mmp "lem_oai4_c1_bridge_no_divisor_lost"]
public theorem IsDecreasedBoundary.isSmallMorphism_of_isRelativelyNef
    {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') {K : Divisor J.Y}
    (P : RelativeFourfoldProgram J.sY (T.sZ i) (J.p ≫ T.f i) K Θ')
    (hnef : QDivisor.IsRelativelyNef (P.modelStructure P.m) (P.toBase P.m)
      (Divisor.toQDivisor (P.canonical P.m) + P.endBoundary))
    {k : ℕ} (hk : k < P.m) :
    IsSmallMorphism (P.modelStructure k) (P.sT k) (P.g k) := by
  by_contra hns
  -- the crepant morphism `p̂ : V_m ⟶ X_{i+1}` of the nef end
  obtain ⟨ph, hph, hB, hpb⟩ :=
    IsDecreasedBoundary.exists_isPullback_of_isRelativelyNef hΘ' P hnef
  have hSi := T.isFourfoldStepDiagram i
  have hZ := hSi.isNormalVariety_target
  have hZp := hSi.isProjectiveVariety_target
  have hX1 := hSi.isNormalVariety_plus
  have hY : IsNormalVariety ℂ J.sY := J.isQFactorial.1
  have hfs : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
  have hfps := hSi.isSmallMorphism_plus
  haveI : IsIntegral (T.Z i) := hZ.1.toIsIntegral
  haveI : IsNormal (T.Z i) := hZ.2
  haveI : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  haveI : IsSeparated (T.sZ i) := hZ.1.toIsSeparated
  haveI : IsSeparated (T.sX (i + 1)) := hX1.1.toIsSeparated
  haveI : LocallyOfFiniteType (T.sX (i + 1)) := hX1.1.toLocallyOfFiniteType
  haveI : IsSeparated J.sY := hY.1.toIsSeparated
  haveI : LocallyOfFiniteType J.sY := hY.1.toLocallyOfFiniteType
  haveI : IsProper (T.f i) := hfs.isProper
  haveI : IsProper (T.fp i) := hfps.isProper
  haveI : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  have hVn := fun k (hk : k ≤ P.m) => Main.isNormalVariety_modelStructure P hY hk
  have hπs := fun k (hk : k ≤ P.m) => Main.toBase_comp P hk
  have hπb := fun k (hk : k ≤ P.m) => Main.isBirationalMorphism_toBase P
    (CommonModel.isBirationalMorphism_comp J.isBirationalMorphism hfs.isBirationalMorphism) hk
  -- a smooth projective `W` with birational morphisms to every `V_k` and to `X_{i+1}`
  let Xs : Option (Fin (P.m + 1)) → Scheme.{0} := fun o => o.elim (T.X (i + 1)) fun k => P.model k
  let fs : ∀ o, Xs o ⟶ T.Z i := fun o => match o with
    | none => T.fp i
    | some k => P.toBase k
  haveI : ∀ o, IsProper (fs o) := fun o => match o with
    | none => (inferInstance : IsProper (T.fp i))
    | some k => Main.isProper_toBase P hY (Nat.lt_succ_iff.mp k.2)
  haveI : AlgebraicGeometry.IsVariety ℂ (T.sZ i) := hZ.1
  obtain ⟨W, w, hWn, hwb, gW, hWs, -, hgW, -, hWp⟩ :=
    CommonModel.exists_smooth_projective_model (k := ℂ) (T.sZ i) fs
      (fun o => match o with
        | none => hfps.isBirationalMorphism
        | some k => hπb k (Nat.lt_succ_iff.mp k.2))
      (fun o => match o with
        | none => by
          change IsNormalVariety ℂ (T.fp i ≫ T.sZ i)
          rw [hSi.comp_eq_plus]
          exact hX1
        | some k => by
          change IsNormalVariety ℂ (P.toBase k ≫ T.sZ i)
          rw [hπs k (Nat.lt_succ_iff.mp k.2)]
          exact (hVn k (Nat.lt_succ_iff.mp k.2)).1)
      (κ := Empty) (fun j => j.elim) (fun j => j.elim)
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType (w ≫ T.sZ i) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ T.sZ i)
  haveI : QuasiCompact (w ≫ T.sZ i) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ T.sZ i)
  have hWp' : MMP.Mori.IsProjectiveVariety ℂ (w ≫ T.sZ i) := hWp hZp
  haveI : IsProper (w ≫ T.sZ i) := isProper_of_isProjectiveMorphism _ hWp'.isProjective
  haveI := hwb.isDominant
  let q : ∀ k, k ≤ P.m → (W ⟶ P.model k) := fun k hk => gW (some ⟨k, Nat.lt_succ_of_le hk⟩)
  let q0 : W ⟶ J.Y := q 0 P.m.zero_le
  let r : W ⟶ T.X (i + 1) := gW none
  have hq : ∀ k (hk : k ≤ P.m), q k hk ≫ P.toBase k = w := fun k hk =>
    (hgW (some ⟨k, Nat.lt_succ_of_le hk⟩)).1
  have hqb : ∀ k (hk : k ≤ P.m), IsBirationalMorphism (q k hk) := fun k hk =>
    (hgW (some ⟨k, Nat.lt_succ_of_le hk⟩)).2.2
  have hr : r ≫ T.fp i = w := (hgW none).1
  have hrb : IsBirationalMorphism r := (hgW none).2.2
  have hqs : ∀ k (hk : k ≤ P.m), q k hk ≫ P.modelStructure k = w ≫ T.sZ i := fun k hk =>
    (congrArg (q k hk ≫ ·) (hπs k hk)).symm.trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ T.sZ i) (hq k hk)))
  have hrs : r ≫ T.sX (i + 1) = w ≫ T.sZ i := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, hr]
  have hqp : ∀ k (hk : k ≤ P.m), IsProper (q k hk) := fun k hk =>
    isProper_of_isProjectiveMorphism _ (hgW (some ⟨k, Nat.lt_succ_of_le hk⟩)).2.1
  haveI : IsProper r := isProper_of_isProjectiveMorphism _ (hgW none).2.1
  have hcomp := Main.comp_g_eq_comp_gp P
    (CommonModel.isBirationalMorphism_comp J.isBirationalMorphism hfs.isBirationalMorphism) q hq
  have hcomp0 : q0 ≫ J.p ≫ T.f i = r ≫ T.fp i := (hq 0 P.m.zero_le).trans hr.symm
  have hq0s : q0 ≫ J.sY = w ≫ T.sZ i := hqs 0 P.m.zero_le
  have hq0b : IsBirationalMorphism q0 := hqb 0 P.m.zero_le
  -- canonical divisors: `K_W` with `q_{0*} K_W = K`, and `K' = r_* K_W` on `X_{i+1}`
  have hdimW : topologicalKrullDim W = ((4 : ℕ) : WithBot ℕ∞) := by
    haveI : MMP.Mori.IsVariety ℂ (w ≫ T.sZ i) := hWn.1
    haveI : MMP.Mori.IsVariety ℂ (T.sX (i + 1)) := hX1.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (T.sX (i + 1))
      (w ≫ T.sZ i) hrb, hSi.dim_plus]
    rfl
  haveI : MMP.Mori.IsVariety ℂ (w ≫ T.sZ i) := hWn.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (w ≫ T.sZ i) hWs hdimW
  have hK := isCanonicalDivisor_four P
  haveI : IsProper q0 := hqp 0 P.m.zero_le
  haveI := hq0b.isDominant
  haveI := hrb.isDominant
  have hWn0 : IsNormalVariety ℂ (q0 ≫ J.sY) := by rwa [hq0s]
  haveI : LocallyOfFiniteType (q0 ≫ J.sY) := hWn0.1.toLocallyOfFiniteType
  obtain ⟨KW, hKW, hKWY⟩ := Main.exists_isCanonicalDivisor_transformDivisor_eq hY hWn0
    hq0b hK (K₀ := K₀) (by rwa [hq0s])
  have hWnr : IsNormalVariety ℂ (r ≫ T.sX (i + 1)) := by rwa [hrs]
  haveI : LocallyOfFiniteType (r ≫ T.sX (i + 1)) := hWnr.1.toLocallyOfFiniteType
  have hKWr : KW.IsCanonicalDivisor (r ≫ T.sX (i + 1)) 4 := by rwa [hrs, ← hq0s]
  have hTK := BridgeComparison.isCanonicalDivisor_K (T := T) (i + 1)
  have hK'c := Main.isCanonicalDivisor_transformDivisor hX1 hWnr hrb hTK hKWr
  set K' : Divisor (T.X (i + 1)) := RationalMap.transformDivisor (X := W) r.toRationalMap KW
    with hK'def
  have hlin : (T.K (i + 1)).LinearlyEquivalent K' :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (T.sX (i + 1)) hX1 hTK hK'c
  have hXQ : (Divisor.toQDivisor K' + T.B (i + 1)).IsQCartier :=
    (T.isFourfoldStepDiagram (i + 1)).isQCartier_minus.add_of_linearlyEquivalent hlin
  -- the three pull-backs `A = q_0^*(K + Θ')`, `A₁ = q_m^*(K_m + Θ_m)`, `R = r^*(K' + B_{i+1})`
  have hYQ : (Divisor.toQDivisor K + Θ').IsQCartier :=
    isQCartier_of_isQFactorial J.sY J.isQFactorial _
  obtain ⟨hDm, -⟩ := id hnef
  have h₀ : ∀ Z : irreducibleComponents W,
      q0 (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + Θ').supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  haveI := (hqb P.m le_rfl).isDominant
  have hₘ : ∀ Z : irreducibleComponents W, q P.m le_rfl (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor (P.canonical P.m) + P.endBoundary).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K' + T.B (i + 1)).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
  have hA := QDivisor.isPullback_pullback hYQ h₀
  have hA₁ := QDivisor.isPullback_pullback hDm hₘ
  have hR := QDivisor.isPullback_pullback hXQ hR₀
  set A := (Divisor.toQDivisor K + Θ').pullback hYQ h₀
  set A₁ := (Divisor.toQDivisor (P.canonical P.m) + P.endBoundary).pullback hDm hₘ
  set R := (Divisor.toQDivisor K' + T.B (i + 1)).pullback hXQ hR₀
  -- `p̂` lies over `Z_i`, so `r = q_m ≫ p̂`
  have hphπ : ph ≫ T.fp i = P.toBase P.m := comp_eq_toBase_of_compHom_eq P hph
  have hr' : q P.m le_rfl ≫ ph = r := by
    have e : (q P.m le_rfl ≫ ph) ≫ T.fp i = r ≫ T.fp i := by
      rw [Category.assoc, hphπ, hq P.m le_rfl, hr]
    haveI : IsDominant ((q P.m le_rfl ≫ ph) ≫ T.fp i) := by rw [e, hr]; infer_instance
    exact Main.eq_of_comp_eq hfps.isBirationalMorphism e
  haveI : IsSeparated (P.modelStructure P.m) := (hVn P.m le_rfl).1.1.toIsSeparated
  have hhs : ph ≫ T.sX (i + 1) = P.modelStructure P.m := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, hphπ, hπs P.m le_rfl]
  haveI : LocallyOfFiniteType (P.modelStructure P.m) :=
    (hVn P.m le_rfl).1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ph ≫ T.sX (i + 1)) := by rw [hhs]; infer_instance
  haveI : LocallyOfFiniteType ph := locallyOfFiniteType_of_comp ph (T.sX (i + 1))
  have hphb : IsBirationalMorphism ph :=
    Main.isBirationalMorphism_of_comp_left (q P.m le_rfl) ph (hqb P.m le_rfl) (hr' ▸ hrb)
  haveI := isSeparated_toTerminal_of_isNormalVariety hX1
  haveI := isSeparated_toTerminal_of_isNormalVariety hY
  -- the prime divisor `P_k` of `V_k` contracted by `g_k`, and its strict transform `E'` on `W`
  have hSk := P.isFourfoldStepDiagram k hk
  obtain ⟨Pk, hPk⟩ := Lost.exists_primeDivisor_two_le_coheight_map hSk hns
  haveI := hqp k hk.le
  obtain ⟨E', hE', -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} (hVn k hk.le).1
      (by rwa [hqs k hk.le]) (hqb k hk.le) Pk
  -- `q_0(η_{E'})` is the generic point of a prime divisor `P₀` of `Y_i`
  obtain ⟨P₀, hP₀, -⟩ := StepChain.exists_primeDivisor_zero_forall_coeff_eq
    (fun k hk => P.isFourfoldStepDiagram k hk) hcomp E'.genericPoint k hk.le Pk hE'
  -- `q_l(η_{E'})` is not the generic point of a prime divisor for `k < l ≤ m`
  have hnot := Lost.ne_genericPoint_of_two_le_coheight (fun k hk => P.isFourfoldStepDiagram k hk)
    hcomp E'.genericPoint hk (by rwa [hE'])
  by_cases hP₀E : P₀ ∈ Set.range J.E
  · -- `P₀ = E_{i,s}`: the coefficient of `q_0^*(K + Θ') - q_m^*(K_m + Θ_m)` at `E'` is both
    -- positive and zero
    obtain ⟨s, rfl⟩ := hP₀E
    have hgen : ∀ l (hl : l ≤ P.m), ∀ Z : irreducibleComponents W,
        q l hl (componentGenericPoint W Z) ∉
          (Divisor.toQDivisor (P.canonical l) + P.boundary l).supp := fun l hl => by
      haveI := (hqb l hl).isDominant
      exact MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _
    have hQl : ∀ l ≤ P.m, (Divisor.toQDivisor (P.canonical l) + P.boundary l).IsQCartier :=
      fun l hl => by
        rcases hl.lt_or_eq with h | rfl
        · exact (P.isFourfoldStepDiagram l h).isQCartier_minus
        · exact hDm
    let Apb : ∀ l, l ≤ P.m → QDivisor W := fun l hl =>
      (Divisor.toQDivisor (P.canonical l) + P.boundary l).pullback (hQl l hl) (hgen l hl)
    have hstep : ∀ l (hl : l < P.m), 0 ≤ Apb l hl.le - Apb (l + 1) hl := fun l hl =>
      ProgramComparison.pullback_sub_pullback_succ_nonneg P.modelStructure P.canonical
        P.boundary P.sT P.g P.gp l (P.isFourfoldStepDiagram l hl) (P.KY_eq l hl)
        (P.ΘY_eq l hl) (w ≫ T.sZ i) hWp' hWn (q l hl.le) (q (l + 1) hl) (hqs l hl.le)
        (hqs (l + 1) hl) (hqb l hl.le) (hqb (l + 1) hl) (hcomp l hl) (hQl l hl.le)
        (hQl (l + 1) hl) (hgen l hl.le) (hgen (l + 1) hl)
    have hchain : ∀ j j' (hjj : j ≤ j') (hj' : j' ≤ P.m),
        0 ≤ Apb j (hjj.trans hj') - Apb j' hj' := by
      intro j j' hjj
      induction j', hjj using Nat.le_induction with
      | base => exact fun _ => (sub_self _).ge
      | succ j' hjj ih =>
        intro hj'
        have h := add_nonneg (ih (Nat.le_of_lt hj')) (hstep j' hj')
        rwa [sub_add_sub_cancel] at h
    obtain ⟨C₀, -, hR₀k⟩ := P.exists_ray_eq k hk
    have hpos := Lost.pullback_sub_pullback_pos hSk (P.KY_eq k hk) (P.ΘY_eq k hk)
      (P.isQFactorial k hk.le) C₀ hR₀k (fun C => (P.isContractionOfRay k hk).isContractedBy_iff C)
      (w ≫ T.sZ i) hWp' hWn (q k hk.le) (q (k + 1) hk) (hqs k hk.le) (hqs (k + 1) hk)
      (hqb k hk.le) (hqb (k + 1) hk) (hcomp k hk) Pk hPk E' hE' (hQl k hk.le) (hQl (k + 1) hk)
      (hgen k hk.le) (hgen (k + 1) hk)
    have h1 : 0 ≤ (Apb 0 P.m.zero_le - Apb k hk.le) E' := hchain 0 k (Nat.zero_le k) hk.le E'
    have h2 : 0 ≤ (Apb (k + 1) hk - Apb P.m le_rfl) E' := hchain (k + 1) P.m hk le_rfl E'
    have h3 : 0 < (Apb k hk.le - Apb (k + 1) hk) E' := hpos
    have hApos : 0 < (A - A₁) E' := by
      change 0 < (Apb 0 P.m.zero_le - Apb P.m le_rfl) E'
      rw [Finsupp.sub_apply] at h1 h2 h3 ⊢
      linarith
    -- the end morphism is crepant: `q_m^*(K_m + Θ_m) = r^*(K' + B_{i+1})`
    haveI : IsSeparated (ph ≫ T.sX (i + 1)) := by rw [hhs]; infer_instance
    haveI : IsSeparated ph := IsSeparated.of_comp ph (T.sX (i + 1))
    have hWp0 : MMP.Mori.IsProjectiveVariety ℂ (q0 ≫ J.sY) := by rwa [hq0s]
    have hKh : RationalMap.transformDivisor ph.toRationalMap (P.canonical P.m) = K' := by
      refine Finsupp.ext fun Q => ?_
      obtain ⟨E, hE, -, htrE⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX1 hWnr hrb Q
      rw [hK'def, htrE]
      have hx : ph (q P.m le_rfl E.genericPoint) = Q.genericPoint := by
        rw [← Scheme.Hom.comp_apply, hr', hE]
      obtain ⟨Pm, hPm, -⟩ :=
        BridgeComparison.exists_primeDivisor_of_map_eq_genericPoint hphb hx
      rw [transformDivisor_apply_of_map_genericPoint hphb
        (show ph Pm.genericPoint = Q.genericPoint by rwa [hPm])]
      obtain ⟨P₀', hP₀', hB'⟩ := StepChain.exists_primeDivisor_zero_forall_coeff_eq
        (fun k hk => P.isFourfoldStepDiagram k hk) hcomp E.genericPoint P.m le_rfl Pm hPm.symm
      rw [hB' P.canonical P.KY_eq]
      change K P₀' = KW E
      rw [← hKWY, transformDivisor_apply_of_map_genericPoint
        hq0b (show q0 E.genericPoint = P₀'.genericPoint from hP₀')]
    haveI : IsDominant (q P.m le_rfl ≫ ph) := by rw [hr']; infer_instance
    obtain ⟨hM', hcompB⟩ := TwoEnds.qDivisor_isPullback_comp ph (q P.m le_rfl) hpb hA₁
    have hA₁R : A₁ = R := Lost.eq_of_isPullback hr' (by rw [hKh]) (by rwa [hKh])
      hcompB hR
    -- at `E'`, over the marked divisor `E_{i,s}`, `q_0^*(K + Θ')` and `r^*(K' + B_{i+1})` agree
    have hcoef := Lost.coeff_pullback_eq_of_map_genericPoint_eq_E hΘ' hWp0 hq0b hrb hcomp0 hKW
      hKWY hK'c hXQ rfl hYQ hA hR E' s hP₀
    rw [Finsupp.sub_apply, hA₁R, hcoef, sub_self] at hApos
    exact lt_irrefl _ hApos
  · -- `P₀` lies over a prime divisor of `X_i`: then `q_m(η_{E'})` has codimension one
    have hXi := hSi.isNormalVariety_minus
    obtain ⟨Q₀, hv₀⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXi
        (⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, P₀⟩ : DivisorOver ℂ (T.sX i))
        fun h => hP₀E ((J.isExceptional_iff P₀).mp h)
    have hQ₀ : J.p P₀.genericPoint = Q₀.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXi.1 hv₀
    have hco : Order.coheight (T.f i Q₀.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _
        (map_genericPoint_mem_biregularLocus hfs.two_le_codimension Q₀), Q₀.coheight_genericPoint]
    have hQZ : T.f i Q₀.genericPoint = (PrimeDivisor.ofCoheightOne _ hco).genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    have hrw : T.fp i (r E'.genericPoint) = (PrimeDivisor.ofCoheightOne _ hco).genericPoint := by
      rw [← Scheme.Hom.comp_apply, ← hcomp0]
      simp only [Scheme.Hom.comp_apply]
      change T.f i (J.p (q 0 P.m.zero_le E'.genericPoint)) = _
      rw [hP₀, hQ₀]
      exact hQZ
    obtain ⟨Q₁, hQ₁, -⟩ :=
      BridgeComparison.exists_primeDivisor_of_map_eq_genericPoint hfps.isBirationalMorphism hrw
    have hx : ph (q P.m le_rfl E'.genericPoint) = Q₁.genericPoint := by
      rw [← Scheme.Hom.comp_apply, hr', hQ₁]
    obtain ⟨Qm, hQm, -⟩ := BridgeComparison.exists_primeDivisor_of_map_eq_genericPoint hphb hx
    exact hnot P.m hk le_rfl Qm hQm.symm

/-! ### The end junction -/

section EndJunction

open MMP.Fourfold.Oai4C1.CommonModel MMP.Fourfold.Oai4C1.Main
open MMP.Fourfold.Oai4C1.BridgeComparison

universe u

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold TopologicalSpace

section Helpers

variable {X Y : Scheme.{u}}

/-- A sum of singles `∑ t, single (e t) (c t)` along an injective `e` has coefficient `c s` at
`e s`. -/
private theorem sum_single_apply_of_injective {ι α R : Type*} [Fintype ι] [AddCommMonoid R]
    {e : ι → α} (he : Function.Injective e) (c : ι → R) (s : ι) :
    (∑ t, Finsupp.single (e t) (c t)) (e s) = c s := by
  classical
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single s (fun t _ hts => Finsupp.single_eq_of_ne
    fun h => hts (he h).symm) (by simp), Finsupp.single_eq_same]

/-- A sum of singles `∑ t, single (e t) (c t)` has coefficient zero off the range of `e`. -/
private theorem sum_single_apply_of_notMem_range {ι α R : Type*} [Fintype ι] [AddCommMonoid R]
    {e : ι → α} (c : ι → R) {a : α} (h : a ∉ Set.range e) :
    (∑ t, Finsupp.single (e t) (c t)) a = 0 := by
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero fun t _ => Finsupp.single_eq_of_ne fun ht => h ⟨t, ht.symm⟩

/-- A morphism whose exceptional set has codimension at least two maps the generic point of
every prime divisor to a point of codimension one. -/
private theorem coheight_map_genericPoint {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight (f P.genericPoint) = 1 := by
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _
    (map_genericPoint_mem_biregularLocus h2 P), P.coheight_genericPoint]

/-- Restriction of `ord_E` along a composite `f ≫ g` is restriction along `f`, then along `g`. -/
private theorem valuationOver_comp {Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (E : MMP.Mori.PrimeDivisor X) (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsDominant f] [IsDominant g] {c : X ⟶ Z} [IsDominant c] (hc : f ≫ g = c) :
    E.valuationOver c = (E.valuationOver f).comap (functionFieldMap g) := by
  ext t
  simp only [PrimeDivisor.valuationOver_apply, Valuation.comap_apply]
  rw [functionFieldMap_comp_apply f g hc]

/-- On a normal variety, a prime divisor is determined by its valuation seen through a dominant
morphism inducing a surjection of function fields. -/
private theorem eq_of_valuationOver_eq {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (f : X ⟶ Y)
    [IsDominant f] (hf : Function.Surjective (functionFieldMap f))
    {P P' : MMP.Mori.PrimeDivisor X} (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have h1 : P.divisorialValuation = P'.divisorialValuation := valuation_eq_of_comap_eq hf h
  have h2 : (DivisorOver.ofPrimeDivisor ℂ hX P).valuation =
      (DivisorOver.ofPrimeDivisor ℂ hX P').valuation := by
    ext g
    change P.divisorialValuation (functionFieldMap (𝟙 X) g) =
      P'.divisorialValuation (functionFieldMap (𝟙 X) g)
    rw [MMP.Mori.functionFieldMap_id_apply, h1]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 h2)

/-- A prime divisor mapped to the generic point of a prime divisor is not exceptional. -/
private theorem not_isExceptional_of_map_genericPoint [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {f : X ⟶ Y} {P : MMP.Mori.PrimeDivisor X}
    {Q : MMP.Mori.PrimeDivisor Y} (h : f P.genericPoint = Q.genericPoint) :
    ¬ RationalMap.IsExceptional (X := X) f.toRationalMap P := by
  intro hex
  have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
    ((MMP.Positivity.isExceptional_toRationalMap_iff (f := f) P).mp hex) _ <|
      subset_closure ⟨P.genericPoint, by
        change P.genericPoint ∈ P.support
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl, h⟩
  rw [Q.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- The inverse transform of a divisor has coefficient zero at an exceptional prime divisor. -/
private theorem inverseTransformDivisor_apply_eq_zero [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {f : X ⟶ Y} {P : MMP.Mori.PrimeDivisor X}
    (hP : RationalMap.IsExceptional (X := X) f.toRationalMap P) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) : inverseTransformDivisor f D P = 0 := by
  refine mapPrimeDivisors_apply_eq_zero (fun Q hQ => ?_) _
  exact not_isExceptional_of_map_genericPoint
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ).1 hP

/-- Over a point of codimension one of a normal variety `T`, a proper birational morphism
`v : B ⟶ T` from a normal variety has the generic point of a prime divisor. -/
private theorem exists_primeDivisor_map_genericPoint_eq {A B T : Scheme.{0}} [IsIntegral B]
    [IsLocallyNoetherian B] [IsNormal B] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {sT : T ⟶ Spec (.of ℂ)} (hT : IsNormalVariety ℂ sT) {v : B ⟶ T}
    (hB : IsNormalVariety ℂ (v ≫ sT)) [IsProper v] (hv : IsBirationalMorphism v) (u : A ⟶ T)
    (x : A) (hx : Order.coheight (u x) = 1) :
    ∃ (Q : MMP.Mori.PrimeDivisor T) (P' : MMP.Mori.PrimeDivisor B),
      u x = Q.genericPoint ∧ v P'.genericPoint = Q.genericPoint := by
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx, ?_⟩
  obtain ⟨E, hE, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hT hB
    hv (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx)
  exact ⟨E, (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx).symm, hE⟩

end Helpers

/-! ### Birational morphisms -/

/-- If `f ≫ g` is dominant and `g` is a proper birational morphism onto a normal scheme, then
`f` maps the generic point to the generic point, so it is dominant. -/
private theorem isDominant_of_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] [IsNormal Z] (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper g]
    [IsLocallyNoetherian Z] (hg : IsBirationalMorphism g) [IsDominant (f ≫ g)] :
    IsDominant f := by
  have hx : f (genericPoint X) ∈ g ⁻¹' {genericPoint Z} := by
    change g (f (genericPoint X)) = genericPoint Z
    rw [← Scheme.Hom.comp_apply]
    exact map_genericPoint_of_isDominant (f ≫ g)
  rw [preimage_genericPoint g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg)] at hx
  refine ⟨dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)⟩
  have h := (genericPoint_spec Y).def
  rw [← h]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint X, hx⟩)

/-- If `f ≫ g` is birational, `g` a proper birational morphism onto a normal scheme and `f`
locally of finite type, then `f` is birational. -/
private theorem isBirationalMorphism_of_comp_right {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] [IsNormal Z] [IsLocallyNoetherian Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper g]
    [LocallyOfFiniteType f] (hg : IsBirationalMorphism g) (hfg : IsBirationalMorphism (f ≫ g)) :
    IsBirationalMorphism f := by
  haveI := hfg.isDominant
  haveI := hg.isDominant
  haveI : IsDominant f := isDominant_of_comp f g hg
  refine isBirationalMorphism_of_isBirational f
    (AlgebraicGeometry.isBirational_of_surjective_functionFieldMap f fun t => ?_)
  obtain ⟨z, hz⟩ := hfg.functionFieldMap_bijective.2 t
  exact ⟨functionFieldMap g z, by rw [functionFieldMap_comp_apply f g rfl, hz]⟩

end

section Program

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

variable {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} {K : Divisor V} {Θ : QDivisor V}
  (P : RelativeFourfoldProgram sV sZ π K Θ)

/-- Every model `V_k`, `k ≤ m`, of a program from a normal variety is a normal projective
fourfold. -/
private theorem isNormalVariety_modelStructure_and_topologicalKrullDim_eq
    (hV : IsNormalVariety ℂ sV) {k : ℕ}
    (hk : k ≤ P.m) : IsNormalVariety ℂ (P.modelStructure k) ∧
      MMP.Mori.IsProjectiveVariety ℂ (P.modelStructure k) ∧
        topologicalKrullDim (P.model k) = 4 := by
  cases k with
  | zero => exact ⟨hV, P.isProjectiveVariety, P.dim_eq⟩
  | succ k => exact ⟨(P.isFourfoldStepDiagram k hk).isNormalVariety_plus,
      (P.isFourfoldStepDiagram k hk).isProjectiveVariety_plus,
      (P.isFourfoldStepDiagram k hk).dim_plus⟩

/-- **One step of the program.** If `g_k(η_{P_k}) = η_Q = g_k⁺(η_{P_{k+1}})` for a prime
divisor `Q` of `T_k`, then `P_k` and `P_{k+1}` have the same valuation of `k(Z)` and the same
coefficient in `Θ_k`, `Θ_{k+1}`. -/
private theorem step_eq [IsIntegral Z] [IsNormal Z] [IsLocallyNoetherian Z]
    (hπ : IsBirationalMorphism π) {k : ℕ} (hk : k < P.m) (Pk : MMP.Mori.PrimeDivisor (P.model k))
    (Pk1 : MMP.Mori.PrimeDivisor (P.Y k)) (Q : MMP.Mori.PrimeDivisor (P.T k))
    (h1 : P.g k Pk.genericPoint = Q.genericPoint) (h2 : P.gp k Pk1.genericPoint = Q.genericPoint) :
    haveI := (isBirationalMorphism_toBase P hπ hk.le).isDominant
    haveI : IsDominant (P.πY k) := (isBirationalMorphism_toBase P hπ (k := k + 1) hk).isDominant
    Pk1.valuationOver (P.πY k) = Pk.valuationOver (P.toBase k) ∧
      P.ΘY k Pk1 = P.boundary k Pk := by
  have hS := P.isFourfoldStepDiagram k hk
  haveI : IsIntegral (P.T k) := hS.isNormalVariety_target.1.toIsIntegral
  haveI : IsNormal (P.T k) := hS.isNormalVariety_target.2
  haveI : LocallyOfFiniteType (P.sT k) := hS.isNormalVariety_target.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.T k) := LocallyOfFiniteType.isLocallyNoetherian (P.sT k)
  haveI := isSeparated_toTerminal_of_isNormalVariety hS.isNormalVariety_target
  haveI : IsProper (P.g k) := isProper_of_isProjectiveMorphism _ hS.isProjectiveMorphism_minus
  haveI : IsProper (P.gp k) := hS.isProper_plus
  haveI := hS.isBirationalMorphism_minus.isDominant
  haveI := hS.isBirationalMorphism_plus.isDominant
  haveI := (isBirationalMorphism_toBase P hπ hk.le).isDominant
  haveI : IsDominant (P.πY k) := (isBirationalMorphism_toBase P hπ (k := k + 1) hk).isDominant
  haveI : IsDominant (P.h k) := by
    haveI : IsDominant (P.g k ≫ P.h k) := by rw [← P.modelMap_eq k hk]; infer_instance
    exact IsDominant.of_comp (P.g k) (P.h k)
  haveI := isIso_stalkMap_of_map_eq_genericPoint hS.isBirationalMorphism_minus h1
  haveI := isIso_stalkMap_of_map_eq_genericPoint hS.isBirationalMorphism_plus h2
  refine ⟨?_, ?_⟩
  · rw [valuationOver_comp Pk1 (P.gp k) (P.h k)
      (P.πY_eq k hk).symm,
      valuationOver_comp Pk (P.g k) (P.h k) (P.modelMap_eq k hk).symm,
      valuationOver_eq_of_isIso _ Pk1 Q h2, valuationOver_eq_of_isIso _ Pk Q h1]
  · rw [P.ΘY_eq k hk]
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [inverseTransformDivisor_apply_of_map_genericPoint h2
      (genericPoint_mem_biregularLocus _ hS.isBirationalMorphism_plus Q),
      transformDivisor_apply_of_map_genericPoint hS.isBirationalMorphism_minus h1]

/-- **Strict transform forward along the program.** Every prime divisor `E` of `V_0` has a
strict transform on each `V_k`, `k ≤ m`, with the same valuation of `k(Z)` and the same boundary
coefficient, when every `g_k` is small. -/
private theorem exists_forward [IsIntegral Z] [IsNormal Z] [IsLocallyNoetherian Z]
    (hπ : IsBirationalMorphism π)
    (hsmall : ∀ k < P.m, IsSmallMorphism (P.modelStructure k) (P.sT k) (P.g k))
    (E : MMP.Mori.PrimeDivisor V) :
    ∀ (k : ℕ) (hk : k ≤ P.m),
      haveI := (isBirationalMorphism_toBase P hπ hk).isDominant
      haveI := hπ.isDominant
      ∃ Pk : MMP.Mori.PrimeDivisor (P.model k),
        Pk.valuationOver (P.toBase k) = E.valuationOver π ∧ P.boundary k Pk = Θ E
  | 0, _ => ⟨E, rfl, rfl⟩
  | k + 1, hk => by
    obtain ⟨Pk, hv, hb⟩ := exists_forward hπ hsmall E k (Nat.le_of_lt hk)
    have hS := P.isFourfoldStepDiagram k hk
    haveI : IsIntegral (P.T k) := hS.isNormalVariety_target.1.toIsIntegral
    haveI : IsNormal (P.T k) := hS.isNormalVariety_target.2
    haveI : LocallyOfFiniteType (P.sT k) := hS.isNormalVariety_target.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (P.T k) := LocallyOfFiniteType.isLocallyNoetherian (P.sT k)
    haveI : IsProper (P.gp k) := hS.isProper_plus
    obtain ⟨Q, Pk1, hQ, hP1⟩ := exists_primeDivisor_map_genericPoint_eq
      hS.isNormalVariety_target (by rw [hS.comp_eq_plus]; exact hS.isNormalVariety_plus)
      hS.isBirationalMorphism_plus (P.g k) Pk.genericPoint
      (coheight_map_genericPoint (hsmall k hk).two_le_codimension Pk)
    obtain ⟨e1, e2⟩ := step_eq P hπ hk Pk Pk1 Q hQ hP1
    exact ⟨Pk1, e1.trans hv, e2.trans hb⟩

/-- **Strict transform backward along the program.** Every prime divisor of `V_k`, `k ≤ m`, is
the strict transform of a prime divisor of `V_0`, with the same valuation of `k(Z)` and the same
boundary coefficient: each `g_k⁺` is small. -/
private theorem exists_backward [IsIntegral Z] [IsNormal Z] [IsLocallyNoetherian Z]
    (hπ : IsBirationalMorphism π) :
    ∀ (k : ℕ) (hk : k ≤ P.m) (Pk : MMP.Mori.PrimeDivisor (P.model k)),
      haveI := (isBirationalMorphism_toBase P hπ hk).isDominant
      haveI := hπ.isDominant
      ∃ E : MMP.Mori.PrimeDivisor V,
        Pk.valuationOver (P.toBase k) = E.valuationOver π ∧ P.boundary k Pk = Θ E
  | 0, _, Pk => ⟨Pk, rfl, rfl⟩
  | k + 1, hk, Pk1 => by
    have hS := P.isFourfoldStepDiagram k hk
    haveI : IsIntegral (P.T k) := hS.isNormalVariety_target.1.toIsIntegral
    haveI : IsNormal (P.T k) := hS.isNormalVariety_target.2
    haveI : LocallyOfFiniteType (P.sT k) := hS.isNormalVariety_target.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (P.T k) := LocallyOfFiniteType.isLocallyNoetherian (P.sT k)
    haveI : IsProper (P.g k) := isProper_of_isProjectiveMorphism _ hS.isProjectiveMorphism_minus
    obtain ⟨Q, Pk, hQ, hPk⟩ := exists_primeDivisor_map_genericPoint_eq
      hS.isNormalVariety_target (by rw [hS.comp_eq_minus]; exact hS.isNormalVariety_minus)
      hS.isBirationalMorphism_minus (P.gp k) Pk1.genericPoint
      (coheight_map_genericPoint hS.isSmallMorphism_plus.two_le_codimension Pk1)
    obtain ⟨e1, e2⟩ := step_eq P hπ hk Pk Pk1 Q hPk hQ
    obtain ⟨E, hv, hb⟩ := exists_backward hπ k (Nat.le_of_lt hk) Pk
    exact ⟨E, e1.trans hv, e2.trans hb⟩

end Program

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold in
/-- **The nef end of a program from the decreased pair is the next crepant junction.**
Let `T` be a stabilized small klt tail and `J = (p_i, Θ_i)` a crepant junction of `(X_i, B_i)`
extracting the stable low-discrepancy set `I_∞`, with decreased boundary `Θ'`. Let `P` be a
finite relative program over `Z_i` (via `f_i ∘ p_i`) from `(Y_i, Θ')` whose end `(V_m, Θ_m)` has
`K_{V_m} + Θ_m` nef over `Z_i`. Let `q : V_m ⟶ X_{i+1}` represent the birational map
`V_m ⤏ X_{i+1}` (`f_i⁺ ∘ q ∘ ψ = f_i ∘ p_i`), with `K_{V_m} + Θ_m = q^*(q_* K_{V_m} + B_{i+1})`.
Then `(q, Θ_m)` is a crepant junction of `(X_{i+1}, B_{i+1})` extracting `I_∞`. That is, there
is a crepant junction `J'` of `(X_{i+1}, B_{i+1})` extracting a finite set equal to the stable
low-discrepancy set at `i + 1` (the image of `I_∞` in the valuations of `k(X_{i+1})`),
and an isomorphism `e : V_m ≅ J'.Y` over `ℂ` with `J'.p ∘ e = q` and `Θ_m = e⁻¹_* J'.Θ`. -/
@[mmp "lem_oai4_c1_bridge_end_junction"]
public theorem IsDecreasedBoundary.exists_fourfoldCrepantJunction_of_isPullback
    {T : StabilizedSmallKltTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = T.stableLowDiscrepancySetAt i)
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I} {Θ' : QDivisor J.Y}
    (hΘ' : IsDecreasedBoundary J Θ') {K : Divisor J.Y}
    (P : RelativeFourfoldProgram J.sY (T.sZ i) (J.p ≫ T.f i) K Θ')
    (hnef : QDivisor.IsRelativelyNef (P.modelStructure P.m) (P.toBase P.m)
      (Divisor.toQDivisor (P.canonical P.m) + P.endBoundary))
    (q : P.endModel ⟶ T.X (i + 1))
    (hq : (P.compositeMap.compHom q).compHom (T.fp i) = (J.p ≫ T.f i).toRationalMap)
    (hB : ∀ Z : irreducibleComponents P.endModel, q (componentGenericPoint P.endModel Z) ∉
      (Divisor.toQDivisor (RationalMap.transformDivisor q.toRationalMap (P.canonical P.m)) +
        T.B (i + 1)).supp)
    (hpull : (Divisor.toQDivisor (RationalMap.transformDivisor q.toRationalMap (P.canonical P.m)) +
        T.B (i + 1)).IsPullback q hB (Divisor.toQDivisor (P.canonical P.m) + P.endBoundary)) :
    ∃ (I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))))
      (_ : (I' : Set _) = T.stableLowDiscrepancySetAt (i + 1))
      (J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I') (e : P.endModel ≅ J'.Y),
      e.hom ≫ J'.p = q ∧ e.hom ≫ J'.sY = P.modelStructure P.m ∧
        P.endBoundary = inverseTransformDivisor e.hom J'.Θ := by
  /- the step `X_i → Z_i ← X_{i+1}` of the tail -/
  have hSi := T.isFourfoldStepDiagram i
  have hXi := hSi.isNormalVariety_minus
  have hZ := hSi.isNormalVariety_target
  have hX1 := hSi.isNormalVariety_plus
  have hY : IsNormalVariety ℂ J.sY := J.isQFactorial.1
  have hfs : IsSmallMorphism (T.sX i) (T.sZ i) (T.f i) :=
    T.isStabilizedSmallKltTail.isSmallFrom_zero i (Nat.zero_le i)
  have hfps := hSi.isSmallMorphism_plus
  haveI : IsIntegral (T.Z i) := hZ.1.toIsIntegral
  haveI : IsNormal (T.Z i) := hZ.2
  haveI : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI := isSeparated_toTerminal_of_isNormalVariety hX1
  haveI := isSeparated_toTerminal_of_isNormalVariety hXi
  haveI : IsProper (T.fp i) := hfps.isProper
  haveI : IsProper (T.f i) := hfs.isProper
  haveI : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  haveI := J.isBirationalMorphism.isDominant
  haveI := hfs.isBirationalMorphism.isDominant
  haveI := hfps.isBirationalMorphism.isDominant
  have hπ : IsBirationalMorphism (J.p ≫ T.f i) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational (T.f i) J.p
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfs.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism J.isBirationalMorphism)
  haveI := hπ.isDominant
  /- every step of the program is small -/
  have hsmall : ∀ k < P.m, IsSmallMorphism (P.modelStructure k) (P.sT k) (P.g k) :=
    fun k hk => IsDecreasedBoundary.isSmallMorphism_of_isRelativelyNef hΘ' P hnef hk
  have hbm := isBirationalMorphism_toBase P hπ (le_refl P.m)
  haveI := hbm.isDominant
  /- the morphism `p̂ = q : V_m ⟶ X_{i+1}` lies over `Z_i` and is projective and birational -/
  have hqf : q ≫ T.fp i = P.toBase P.m := comp_eq_toBase_of_compHom_eq P hq
  have hqs : q ≫ T.sX (i + 1) = P.modelStructure P.m := by
    rw [← hSi.comp_eq_plus, ← Category.assoc, hqf, toBase_comp P le_rfl]
  obtain ⟨hVmn, hVmp, hVmd⟩ :=
    isNormalVariety_modelStructure_and_topologicalKrullDim_eq P hY (le_refl P.m)
  haveI : LocallyOfFiniteType (q ≫ T.sX (i + 1)) := by
    rw [hqs]; exact hVmn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType q := locallyOfFiniteType_of_comp q (T.sX (i + 1))
  have hqb : IsBirationalMorphism q :=
    isBirationalMorphism_of_comp_right q (T.fp i) hfps.isBirationalMorphism (by rwa [hqf])
  haveI := hqb.isDominant
  haveI : IsSeparated (T.sX (i + 1)) := hX1.1.toIsSeparated
  have hqp : IsProjectiveMorphism q :=
    IsProjectiveMorphism.of_comp q (T.sX (i + 1)) (by rw [hqs]; exact hVmp.isProjective)
  haveI : IsProper q := isProper_of_isProjectiveMorphism _ hqp
  have hqn : IsNormalVariety ℂ (q ≫ T.sX (i + 1)) := by rwa [hqs]
  /- the valuations `s'` of `k(X_{i+1})` transported from `s ∈ I` -/
  have hfpb := hfps.isBirationalMorphism.functionFieldMap_bijective
  obtain ⟨ad, had, hΘ'eq⟩ := id hΘ'
  choose tr htr hlog using had
  have htr_eq : ∀ (s : I)
      {s'' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))},
      T.IsTransportedValuation i s s'' → s'' = tr s :=
    fun s _ h => valuation_eq_of_comap_eq hfpb.2 (h.trans (htr s).symm)
  classical
  let I' := Finset.univ.image tr
  have hmemI' : ∀ s : I, tr s ∈ I' := fun s => Finset.mem_image_of_mem tr (Finset.mem_univ s)
  have hI' : (I' : Set _) = T.stableLowDiscrepancySetAt (i + 1) := by
    ext s''
    simp only [I', Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      have hs : (s : Valuation _ _) ∈ T.stableLowDiscrepancySetAt i := by rw [← hI]; exact s.2
      obtain ⟨ξ, hξ, hc⟩ := hs
      exact ⟨ξ, hξ, s, hc, htr s⟩
    · rintro ⟨ξ, hξ, ζ, hc, ht⟩
      have hζ : ζ ∈ (I : Set _) := by rw [hI]; exact ⟨ξ, hξ, hc⟩
      exact ⟨⟨ζ, hζ⟩, (htr_eq ⟨ζ, hζ⟩ ht).symm⟩
  have hsub : ∀ s' ∈ I', s' ∈ lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1)) := by
    intro s' hs'
    change s' ∈ T.lowDiscrepancySetAt (i + 1)
    rw [T.isStabilizedSmallKltTail.lowDiscrepancySetAt_eq (i + 1)]
    rwa [← Finset.mem_coe, hI'] at hs'
  /- a prime divisor of `V_m` with the valuation of `E_{i,s}` over `Z_i` has valuation `s'` -/
  have hval : ∀ (Pm : MMP.Mori.PrimeDivisor P.endModel) (s : I),
      Pm.valuationOver (P.toBase P.m) = (J.E s).valuationOver (J.p ≫ T.f i) →
        Pm.valuationOver q = tr s := by
    intro Pm s h
    refine valuation_eq_of_comap_eq hfpb.2 ?_
    rw [← valuationOver_comp Pm q (T.fp i) hqf, h, valuationOver_comp (J.E s) J.p (T.f i) rfl,
      show (J.E s).valuationOver J.p = s from J.valuation_eq s]
    exact (htr s).symm
  have hU : ∀ Pa Pb : MMP.Mori.PrimeDivisor P.endModel,
      Pa.valuationOver q = Pb.valuationOver q → Pa = Pb :=
    fun Pa Pb h => eq_of_valuationOver_eq hVmn q hqb.functionFieldMap_bijective.2 h
  /- the divisors `c_{V_m}(s')`: strict transforms of the `E_{i,s}` -/
  have hEx : ∀ s' : I', ∃ Pm : MMP.Mori.PrimeDivisor P.endModel, Pm.valuationOver q = s' ∧
      ∃ s : I, tr s = s' ∧ P.endBoundary Pm = Θ' (J.E s) := fun s' => by
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp s'.2
    obtain ⟨Pm, hv, hb⟩ : ∃ Pm : MMP.Mori.PrimeDivisor P.endModel,
        Pm.valuationOver (P.toBase P.m) = (J.E s).valuationOver (J.p ≫ T.f i) ∧
          P.endBoundary Pm = Θ' (J.E s) :=
      exists_forward P hπ hsmall (J.E s) P.m le_rfl
    exact ⟨Pm, (hval Pm s hv).trans hs, s, hs, hb⟩
  choose E hEv sOf hsOf hEb using hEx
  have hEinj : Function.Injective E := fun a b h => Subtype.ext
    ((hEv a).symm.trans ((congrArg (fun Pm => Pm.valuationOver q) h).trans (hEv b)))
  /- every prime divisor of `V_m` is some `c_{V_m}(s')`, or lies over a prime divisor of
  `X_{i+1}` with the coefficient of `B_{i+1}` -/
  have hcls : ∀ Pm : MMP.Mori.PrimeDivisor P.endModel, (∃ s' : I', E s' = Pm) ∨
      ∃ Q : MMP.Mori.PrimeDivisor (T.X (i + 1)), q Pm.genericPoint = Q.genericPoint ∧
        P.endBoundary Pm = T.B (i + 1) Q := by
    intro Pm
    obtain ⟨E0, hv, hb⟩ : ∃ E0 : MMP.Mori.PrimeDivisor J.Y,
        Pm.valuationOver (P.toBase P.m) = E0.valuationOver (J.p ≫ T.f i) ∧
          P.endBoundary Pm = Θ' E0 :=
      exists_backward P hπ P.m le_rfl Pm
    by_cases hE0 : E0 ∈ Set.range J.E
    · obtain ⟨s, rfl⟩ := hE0
      left
      refine ⟨⟨tr s, hmemI' s⟩, hU _ _ ?_⟩
      rw [hEv, hval Pm s hv]
    · right
      obtain ⟨Q₀, hv₀⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional
        hXi (⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, E0⟩ : DivisorOver ℂ (T.sX i))
        fun h => hE0 ((J.isExceptional_iff E0).mp h)
      have hQ₀ : J.p E0.genericPoint = Q₀.genericPoint :=
        MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXi.1 hv₀
      have hco := coheight_map_genericPoint hfs.two_le_codimension Q₀
      obtain ⟨QZ, hQZ⟩ : ∃ QZ : MMP.Mori.PrimeDivisor (T.Z i),
          T.f i Q₀.genericPoint = QZ.genericPoint :=
        ⟨_, (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩
      have hgen : P.toBase P.m Pm.genericPoint = (J.p ≫ T.f i) E0.genericPoint :=
        MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hZ.1
          (D := ⟨P.endModel, P.toBase P.m, by rwa [toBase_comp P le_rfl], hbm, Pm⟩)
          (D' := ⟨J.Y, J.p ≫ T.f i, by rwa [Category.assoc, hSi.comp_eq_minus], hπ,
            E0⟩) hv
      have hfpq : T.fp i (q Pm.genericPoint) = QZ.genericPoint := by
        rw [← Scheme.Hom.comp_apply, hqf, hgen, Scheme.Hom.comp_apply, hQ₀, hQZ]
      obtain ⟨Q', hQ', -⟩ :=
        exists_primeDivisor_of_map_eq_genericPoint hfps.isBirationalMorphism hfpq
      refine ⟨Q', hQ'.symm, ?_⟩
      rw [hb, hΘ'eq, Finsupp.add_apply, sum_single_apply_of_notMem_range _ hE0, add_zero,
          inverseTransformDivisor_apply_of_map_genericPoint hQ₀
          (genericPoint_mem_biregularLocus J.p J.isBirationalMorphism Q₀), T.B_eq i]
      simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
      rw [inverseTransformDivisor_apply_of_map_genericPoint (hQ' ▸ hfpq)
          (genericPoint_mem_biregularLocus _ hfps.isBirationalMorphism _),
        transformDivisor_apply_of_map_genericPoint hfs.isBirationalMorphism hQZ]
  /- the `p̂`-exceptional prime divisors are the `c_{V_m}(s')` -/
  have hexc : ∀ Pm : MMP.Mori.PrimeDivisor P.endModel,
      RationalMap.IsExceptional (X := P.endModel) q.toRationalMap Pm ↔ Pm ∈ Set.range E := by
    intro Pm
    constructor
    · intro hex
      rcases hcls Pm with ⟨s', hs'⟩ | ⟨Q, hQ, -⟩
      · exact ⟨s', hs'⟩
      · exact absurd hex (not_isExceptional_of_map_genericPoint hQ)
    · rintro ⟨s', rfl⟩
      by_contra hne
      obtain ⟨⟨D, -, hDv, h2⟩, -⟩ := hsub s' s'.2
      obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional
        hX1 (⟨P.endModel, q, hqn, hqb, E s'⟩ : DivisorOver ℂ (T.sX (i + 1))) hne
      have hv : D.valuation = (⟨P.endModel, q, hqn, hqb, E s'⟩ :
          DivisorOver ℂ (T.sX (i + 1))).valuation := hDv.symm.trans (hEv s').symm
      exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX1 D).mp h2 Q (hv.trans hQ)
  /- the boundary -/
  have hΘE : ∀ s : I, Θ' (J.E s) = 1 - ad s := fun s => by
    rw [hΘ'eq, Finsupp.add_apply,
      inverseTransformDivisor_apply_eq_zero ((J.isExceptional_iff _).mpr ⟨s, rfl⟩), zero_add,
      sum_single_apply_of_injective J.injective]
  have hlogE : ∀ s' : I',
      IsValuationLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) s' (ad (sOf s')) := fun s' =>
    hsOf s' ▸ hlog (sOf s')
  have hΘm : P.endBoundary = inverseTransformDivisor q (T.B (i + 1)) +
      ∑ s' : I', Finsupp.single (E s') (1 - ad (sOf s')) := by
    refine Finsupp.ext fun Pm => ?_
    rw [Finsupp.add_apply]
    rcases hcls Pm with ⟨s0, rfl⟩ | ⟨Q, hQ, hb⟩
    · rw [inverseTransformDivisor_apply_eq_zero ((hexc _).mpr ⟨s0, rfl⟩), zero_add,
        sum_single_apply_of_injective hEinj, hEb, hΘE]
    · rw [sum_single_apply_of_notMem_range _
          fun h => not_isExceptional_of_map_genericPoint hQ ((hexc Pm).mpr h), add_zero,
          inverseTransformDivisor_apply_of_map_genericPoint hQ
          (genericPoint_mem_biregularLocus q hqb Q), hb]
  /- the junction `(p̂, Θ_m)` -/
  let J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I' :=
    { Y := P.endModel
      p := q
      E := E
      Θ := P.endBoundary
      isProjectiveVariety_base := hSi.isProjectiveVariety_plus
      dim_base := hSi.dim_plus
      isKltPair := T.isStabilizedSmallKltTail.isKlt (i + 1)
      subset_lowDiscrepancySet := hsub
      isProjectiveVariety := by rwa [hqs]
      isQFactorial := by rw [hqs]; exact P.isQFactorial P.m le_rfl
      dim_eq := hVmd
      isProjectiveMorphism := hqp
      isBirationalMorphism := hqb
      valuation_eq := hEv
      injective := hEinj
      isExceptional_iff := hexc
      Θ_eq := ⟨fun s' => ad (sOf s'), hlogE, hΘm⟩ }
  exact ⟨I', hI', J', Iso.refl _, Category.id_comp _, (Category.id_comp _).trans hqs,
    (inverseTransformDivisor_id _).symm⟩

end EndJunction

end MMP.Fourfold.StabilizedSmallKltTail
