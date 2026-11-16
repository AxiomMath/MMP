module

public import MMP.Attr
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic

/-!
# Complemented nef adjoints over a base of dimension at most one

Let `(X, B)` be an effective `ℚ`-factorial projective dlt threefold pair, `f : X ⟶ Z` a morphism
to a projective variety whose image has dimension at most one, and `D = K_X + B` `f`-nef. If
`A ≥ 0` is a `ℚ`-Cartier divisor with `D + A ∼_ℚ f^*H` for a rational Cartier divisor `H` on `Z`,
then `D` is `f`-semiample.

Write `N(D + A) = L`, a divisor which is principal over a neighbourhood of every point of `Z`
(`MMP.Fourfold.exists_smul_eq_and_isLocalEquation_preimage`); in particular `(D + A) · γ = 0`
for every curve `γ` contracted by `f`. A closed point `x` of a component of `A` and a
generization `ξ ∉ Supp A` of `x` with contracted closure would give a curve `γ ∋ x` inside
`{ξ}⁻`, not contained in `Supp A`, with `(A · γ) > 0` and `(D · γ) ≥ 0`
(`MMP.Fourfold.false_of_forall_intersectionNumber_add_eq_zero`).

* If `f(X)` is a point, take `ξ` the generic point of `X`: so `A = 0`, and `L = N D` is
  principal over a neighbourhood of `f(X)`, hence relatively free.
* Otherwise the Stein factorization `X ⟶ C ⟶ Z` has `C` a normal projective curve, smooth over
  the perfect field `k`, with `p_* 𝒪_X = 𝒪_C`, and `C ⟶ Z` finite. A horizontal component of `A`
  would meet a fibre `p⁻¹(c)` over a closed point `c` carrying no component of `A`; taking `ξ`
  the generic point of a component of that fibre shows that `A` is vertical. As `-A ≡ D` over
  `C`, `A = p^*P` for an effective `P`
  (`MMP.Fourfold.exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg`). With `d` clearing
  the denominators of `R = dN P`, `dN D = d L - p^*R` is relatively free over `Z`
  (`MMP.Fourfold.isRelativelyFreeDivisor_add_neg_pullback`): at a closed point `x` over
  `z ∈ Z` and `c ∈ C`, a rational function `t` on `C` with `v_c(t) = R(c)` and `v_s(t) ≥ R(s)`
  at the other points `s` of the finite fibre over `z` gives a section of `𝒪_X(dN D)` over a
  neighbourhood of the fibre of `z`, not vanishing at `x`.

## Main results

* `MMP.Fourfold.exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent`: the
  statement above.
* `MMP.Fourfold.exists_isRelativelyFreeDivisor_of_add_qLinearlyEquivalent`: the same for an
  `f`-nef `ℚ`-divisor `D` on a `ℚ`-factorial projective variety of any dimension, over a separated
  base of finite type.
* `MMP.Fourfold.isRelativelyFreeDivisor_add_neg_pullback`: a divisor locally principal over the
  base, minus the pull-back of a divisor on a curve finite over the base, is relatively free.
* `MMP.Fourfold.exists_isLocalEquation_preimage_of_iso_pullback`: a divisor `L` with
  `𝒪_X(L) ≅ f^* M`, `M` invertible, is principal over a neighbourhood of every point of the base.
* `MMP.Fourfold.exists_unit_ord_eq_and_le`: rational functions on a normal curve with prescribed
  orders at finitely many closed points of an affine open.
* `MMP.Fourfold.topologicalKrullDim_le_of_isFinite`: a finite morphism does not raise dimension.

## Implementation notes

* "`D + A ∼_ℚ f^*H` for a rational Cartier divisor `H` on `Z`" is stated as `D + A ∼_ℚ G`
  (`MMP.Mori.QDivisor.QLinearlyEquivalent`) for a `ℚ`-divisor `G` on `X` with
  `𝒪_X(mG) ≅ f^* M` for some `m > 0` and an invertible `𝒪_Z`-module `M` (`M = 𝒪_Z(mH)`, `mH`
  Cartier). The morphism `f` is not dominant, so the pull-back of a Cartier divisor on `Z` is
  that of its invertible sheaf, as in `MMP.Mori.degreeOn_pullback_divisorialSheaf_eq_zero`;
  `M` is allowed to be any invertible sheaf, and `Z` need not be normal.
* "`D` is `f`-semiample" is: some positive multiple `mD` is a Cartier divisor `L` whose sheaf is
  relatively generated, `f^* f_* 𝒪_X(L) → 𝒪_X(L)` surjective
  (`MMP.Fourfold.IsRelativelyFreeDivisor`), as in
  `MMP.Fourfold.exists_isRelativelyFreeDivisor_of_pullback`.
* "The image has dimension at most one" is `topologicalKrullDim (Set.range f) ≤ 1`.
* The source works over `ℂ`; the proof uses only that `k` is perfect (so that the normal curve
  `C` is smooth). The dlt condition, the dimension three and the effectivity of `B` are not used:
  `K_X + B` enters only through its `f`-nefness.
* The vanishing of `A` over a point and the verticality of `A` over a curve are proved with
  curves through closed points of `Supp A` (`MMP.Fourfold.exists_isProperCurve_of_specializes`),
  instead of intersecting with the square of an ample divisor or restricting to a general fibre
  surface; no intersection theory beyond intersection numbers with curves is needed. The
  Stein factorization of `f` itself is used, its base being already normal, so the normalization
  of the image is not needed.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Notation 0.4
* [Stacks Project, Tag 03H0](https://stacks.math.columbia.edu/tag/03H0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori MMP.Threefold.Mori.CanonUniq
open Stacks.AlgebraicGeometry.AmpleDimensionOne (isClosed_singleton_of_ne_genericPoint)

section LocalEquation

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X]

/-- If an isomorphism `𝒪_X(D)|_U ≅ 𝒪_X(D')|_U` acts on sections as multiplication by a unit `ψ`
of `K(X)`, then `D(Γ) - D'(Γ) ≤ v_Γ(ψ)` for every prime divisor `Γ` with generic point in `U`:
the local form of `MMP.Threefold.Mori.CanonUniq.ord_ge_of_phi`. -/
theorem ord_ge_of_phi_of_mem {U : X.Opens} {D D' : Divisor X}
    (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι)
    (ψ : (RationalFunctions X)ˣ)
    (hL1 : ∀ (V : U.toScheme.Opens) (s : D.divisorialSubmodule (U.ι ''ᵁ V))
      (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}),
      (phi e V s).1 Z = (ψ : RationalFunctions X) Z.1 * s.1 Z)
    (Γ : MMP.Mori.PrimeDivisor X) (hΓ : Γ.genericPoint ∈ U) :
    D.coeff Γ - D'.coeff Γ ≤ Γ.ord ψ := by
  classical
  obtain ⟨g, hg⟩ := exists_unit_ord Γ (-D.coeff Γ)
  let T : Set (MMP.Mori.PrimeDivisor X) := {E | E ≠ Γ ∧ (E.ord g ≠ 0 ∨ D.coeff E ≠ 0)}
  have hTfin : T.Finite := by
    refine ((finite_ord_ne_zero g).union D.support.finite_toSet).subset ?_
    rintro E ⟨-, h | h⟩
    · exact Or.inl h
    · exact Or.inr (by simpa [DivisorWithCoeffs.coeff_apply] using h)
  let C : Set X := ⋃ E ∈ T, (E.support : Set X)
  have hC : IsClosed C := hTfin.isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed
  let O : X.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  let VΓ : U.toScheme.Opens := U.ι ⁻¹ᵁ O
  have hγO : Γ.genericPoint ∈ O := by
    intro hmem
    obtain ⟨E, hET, hE⟩ := Set.mem_iUnion₂.mp hmem
    exact genericPoint_notMem_support_of_ne (Ne.symm hET.1) hE
  have hγW : Γ.genericPoint ∈ U.ι ''ᵁ VΓ := ⟨⟨Γ.genericPoint, hΓ⟩, hγO, rfl⟩
  have hmem : ∀ E : MMP.Mori.PrimeDivisor X,
      (E.support ∩ ((U.ι ''ᵁ VΓ : X.Opens) : Set X)).Nonempty →
      E ≠ Γ → E.ord g = 0 ∧ D.coeff E = 0 := by
    intro E ⟨x, hxE, hxW⟩ hEΓ
    obtain ⟨v, hv, rfl⟩ := hxW
    by_contra hcon
    have hET : E ∈ T := ⟨hEΓ, by
      by_cases h : E.ord g = 0
      · exact Or.inr fun h' => hcon ⟨h, h'⟩
      · exact Or.inl h⟩
    exact hv (Set.mem_biUnion hET hxE)
  let sec : D.divisorialSubmodule (U.ι ''ᵁ VΓ) :=
    ⟨fun Z => (g : RationalFunctions X) Z.1, fun E h => Or.inr <| by
      change WithZero.exp _ ≤ E.valuation ((g : RationalFunctions X) E.component)
      by_cases hEΓ : E = Γ
      · subst hEΓ
        rw [E.valuation_component, hg]
      · obtain ⟨h1, h2⟩ := hmem E h hEΓ
        rw [E.valuation_component, h1, h2]
        simp⟩
  have hγE : Γ.genericPoint ∈ Γ.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have ht := (phi e VΓ sec).2 Γ ⟨Γ.genericPoint, hγE, hγW⟩
  have hL := hL1 VΓ sec ⟨Γ.component, Γ.componentGenericPoint_mem_of_nonempty
    ⟨Γ.genericPoint, hγE, hγW⟩⟩
  rcases ht with h0 | hle
  · exfalso
    change (phi e VΓ sec).1 ⟨Γ.component, _⟩ = 0 at h0
    rw [hL] at h0
    have hu' := (ψ * g).isUnit.map (RationalFunctions.component X Γ.component)
    change IsUnit ((ψ : RationalFunctions X) Γ.component * (g : RationalFunctions X) Γ.component)
      at hu'
    exact hu'.ne_zero h0
  · change WithZero.exp _ ≤ Γ.valuation ((phi e VΓ sec).1 ⟨Γ.component, _⟩) at hle
    rw [hL] at hle
    change WithZero.exp _ ≤ Γ.valuation
      (((ψ * g : (RationalFunctions X)ˣ) : RationalFunctions X) Γ.component) at hle
    rw [Γ.valuation_component, WithZero.exp_le_exp, PrimeDivisor.ord_mul, hg] at hle
    omega

/-- **A trivialization of `𝒪_X(D)` on an open set is a local equation.** If `𝒪_X(D)|_W ≅ 𝒪_W`,
then `D|_W = div(ψ)|_W` for a unit `ψ` of `K(X)`. -/
theorem exists_isLocalEquation_of_restrict_iso_unit {D : Divisor X} {W : X.Opens}
    (e : D.divisorialSheaf.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    ∃ ψ : (RationalFunctions X)ˣ, D.IsLocalEquation W ψ := by
  let D' : Divisor X := 0
  let e' : D.divisorialSheaf.restrict W.ι ≅ D'.divisorialSheaf.restrict W.ι :=
    e ≪≫ ((Scheme.Modules.restrictFunctor W.ι).mapIso Divisor.divisorialSheafZeroIso ≪≫
      Scheme.Modules.restrictUnitIso W.ι).symm
  by_cases hWe : (W : Set X).Nonempty
  swap
  · exact ⟨1, fun E ⟨x, _, hx⟩ => absurd ⟨x, hx⟩ hWe⟩
  obtain ⟨u, hu⟩ := hWe
  have hηU : genericPoint X ∈ W := by
    obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) := ⟨⟨Set.univ, by
      rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
    rw [← componentGenericPoint_eq Z]
    exact componentGenericPoint_mem ⟨u, hu⟩ Z
  let O₀ : X.Opens := ⟨((D.supp ⊔ D'.supp : TopologicalSpace.Closeds X) : Set X)ᶜ,
    (D.supp ⊔ D'.supp).isClosed.isOpen_compl⟩
  let V₀ : W.toScheme.Opens := W.ι ⁻¹ᵁ O₀
  have hηO : genericPoint X ∉ ((D.supp ⊔ D'.supp : TopologicalSpace.Closeds X) : Set X) := by
    intro h
    have h' : genericPoint X ∈ (D.supp : Set X) ∪ (D'.supp : Set X) := by simpa using h
    rcases h' with h | h <;>
    · obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
      exact genericPoint_notMem_support E hE
  have hV₀ : (V₀ : Set W).Nonempty := ⟨⟨genericPoint X, hηU⟩, hηO⟩
  have hDD : ∀ (F : Divisor X), F.supp ≤ D.supp ⊔ D'.supp →
      ∀ Γ : MMP.Mori.PrimeDivisor X,
        (Γ.support ∩ ((W.ι ''ᵁ V₀ : X.Opens) : Set X)).Nonempty → F.coeff Γ = 0 := by
    intro F hF Γ ⟨x, hxΓ, v, hv, hvx⟩
    by_contra hne
    have hvx' : W.ι v = x := hvx
    exact hv (hvx' ▸ hF (DivisorWithCoeffs.support_subset_supp hne hxΓ))
  have hD := hDD D le_sup_left
  have hD' := hDD D' le_sup_right
  let ψU : (RationalFunctions X)ˣ :=
    ⟨psi e' V₀ hV₀ hD, psi e'.symm V₀ hV₀ hD', funext fun Z => by
      rw [Pi.mul_apply, mul_comm]; exact psi_mul e' V₀ hV₀ hD hD' Z,
      funext fun Z => psi_mul e' V₀ hV₀ hD hD' Z⟩
  have hL1 := phi_apply_eq e' V₀ hV₀ hD
  have hL1' := phi_apply_eq e'.symm V₀ hV₀ hD'
  refine ⟨ψU, fun Γ hΓ => ?_⟩
  have hΓW : Γ.genericPoint ∈ W := (Γ.genericPoint_mem_iff W).mpr hΓ
  have a1 := ord_ge_of_phi_of_mem e' ψU hL1 Γ hΓW
  have a2 := ord_ge_of_phi_of_mem e'.symm ψU⁻¹ hL1' Γ hΓW
  rw [PrimeDivisor.ord_inv] at a2
  have : D'.coeff Γ = 0 := DivisorWithCoeffs.coeff_zero Γ
  omega

/-- **A divisor whose sheaf is a pull-back is locally principal over the base.** Let `f : X ⟶ Z`
and let `M` be an invertible `𝒪_Z`-module with `𝒪_X(L) ≅ f^* M`. Every `z ∈ Z` has an open
neighbourhood `U` such that `L` has a local equation on `f⁻¹(U)`: trivializing `M` on `U`
trivializes `𝒪_X(L)` on `f⁻¹(U)`. -/
theorem exists_isLocalEquation_preimage_of_iso_pullback {Z : Scheme.{u}} (f : X ⟶ Z)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M] {L : Divisor X}
    (e : L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M) (z : Z) :
    ∃ U : Z.Opens, z ∈ U ∧ ∃ ψ : (RationalFunctions X)ˣ, L.IsLocalEquation (f ⁻¹ᵁ U) ψ := by
  obtain ⟨U, hzU, ⟨eU⟩⟩ :=
    (AlgebraicGeometry.isInvertible_iff_exists_restrict_iso_unit Z M).mp inferInstance z
  refine ⟨U, hzU, ?_⟩
  let W : X.Opens := f ⁻¹ᵁ U
  let g : W.toScheme ⟶ U.toScheme := f ∣_ U
  let : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  let eunit : (Scheme.Modules.pullback g).obj (SheafOfModules.unit U.toScheme.ringCatSheaf) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    @asIso _ _ _ _ _
      (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{u} g.toRingCatSheafHom)
  let eW : L.divisorialSheaf.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctor W.ι).mapIso e ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
      (Scheme.Modules.pullbackComp W.ι f).app M ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
      ((Scheme.Modules.pullbackComp g U.ι).app M).symm ≪≫
      (Scheme.Modules.pullback g).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
      (Scheme.Modules.pullback g).mapIso eU ≪≫ eunit
  exact exists_isLocalEquation_of_restrict_iso_unit eW

end LocalEquation

/-! ### Intersection numbers with curves contracted over the base -/

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]

/-- **A divisor with a local equation near a curve is numerically trivial on it.** If `L` has a
local equation on an open `W` containing the proper curve `γ`, on a `ℚ`-factorial `X`, then
`(L · γ) = 0`: `L - div ψ` is disjoint from `γ`. -/
theorem intersectionNumber_eq_zero_of_isLocalEquation (hX : IsQFactorial sX) {L : Divisor X}
    {W : X.Opens} {ψ : (RationalFunctions X)ˣ} (hL : L.IsLocalEquation W ψ)
    (hLq : (Divisor.toQDivisor L).IsQCartier) (γ : ProperCurve sX)
    (hγ : ∀ x : X, γ.point ⤳ x → x ∈ W) :
    (Divisor.toQDivisor L).intersectionNumber k sX γ.ι γ.dim_le hLq = 0 := by
  set G : Divisor X := L - principalDivisor ψ
  have hGdisj : ∀ x : X, γ.point ⤳ x → x ∉ (Divisor.toQDivisor G).supp := by
    intro x hx hmem
    rw [Divisor.supp_toQDivisor] at hmem
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    refine hE ?_
    rw [DivisorWithCoeffs.coeff_sub, hL E ⟨x, hxE, hγ x hx⟩, coeff_principalDivisor, sub_self]
  have hdc := Divisor.isCartier_principalDivisor ψ
  have hdq := QDivisor.isQCartier_toQDivisor hdc
  have hGq := isQCartier_of_isQFactorial sX hX (Divisor.toQDivisor G)
  have hsum : Divisor.toQDivisor L =
      Divisor.toQDivisor G + Divisor.toQDivisor (principalDivisor ψ) := by
    rw [← map_add, sub_add_cancel]
  rw [intersectionNumber_congr sX γ.ι γ.dim_le hLq (hGq.add hdq) hsum,
    QDivisor.intersectionNumber_add' k sX γ.ι γ.dim_le _ _ hGq hdq,
    intersectionNumber_eq_zero_of_disjoint sX hX _ hGq γ hGdisj, zero_add,
    QDivisor.intersectionNumber_toQDivisor k sX γ.ι γ.dim_le _ hdc hdq]
  have hiso := (Divisor.linearlyEquivalent_principalDivisor_zero ψ).divisorialSheafIso
  have h0 : (0 : Divisor X).degreeOn k sX γ.ι γ.dim_le Divisor.isCartier_zero = 0 :=
    Divisor.degreeOn_zero' k sX γ.ι γ.dim_le
  have := hdc.isInvertibleModule_divisorialSheaf
  have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
  have h1 : (principalDivisor ψ).degreeOn k sX γ.ι γ.dim_le hdc =
      (0 : Divisor X).degreeOn k sX γ.ι γ.dim_le Divisor.isCartier_zero :=
    degreeOn_eq_of_iso k sX γ.ι γ.dim_le hiso
  rw [h1, h0, Int.cast_zero]

omit [CompactSpace X] in
/-- Relative nefness from intersection numbers: a `ℚ`-Cartier `ℚ`-divisor with `(D · C) ≥ 0`
for every proper curve `C` contracted by `f` is `f`-nef. -/
theorem QDivisor.isRelativelyNef_of_intersectionNumber_nonneg {Y : Scheme.{u}} {f : X ⟶ Y}
    {D : QDivisor X} (hD : D.IsQCartier)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ D.intersectionNumber k sX C.ι C.dim_le hD) :
    D.IsRelativelyNef sX f := by
  refine ⟨hD, fun C hC => ?_⟩
  have key := h C hC
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp)]
  rw [QDivisor.intersectionNumber] at key
  have hm : (0 : ℚ) < D.cartierIndex hD := by exact_mod_cast QDivisor.cartierIndex_pos hD
  have h1 : (0 : ℚ) ≤ ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX C.ι C.dim_le
      (D.cartierIndexSMul hD).2 : ℚ) := by
    have := mul_nonneg key hm.le
    rw [div_mul_cancel₀ _ hm.ne'] at this
    exact_mod_cast this
  simp only [smul_eq_mul, mul_one]
  have h2 : (0 : ℝ) ≤ ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX C.ι C.dim_le
      (D.cartierIndexSMul hD).2 : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ (((1 / (D.cartierIndex hD : ℚ)) : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ 1 / (D.cartierIndex hD : ℚ) := by positivity
    exact_mod_cast this
  exact mul_nonneg h3 h2

omit [CompactSpace X] in
/-- **A curve through a component of an effective divisor in a contracted locus.** Let `D` be
`f`-nef and `A ≥ 0` with `((D + A) · γ) = 0` for every proper curve `γ` contracted by `f`. Then
no closed point `x ∈ Supp A` has a generization `ξ ∉ Supp A` whose closure is contracted by `f`:
a proper curve through `x` inside `{ξ}⁻`, not contained in `Supp A`, would have `(A · γ) > 0` and
`(D · γ) ≥ 0`. -/
theorem false_of_forall_intersectionNumber_add_eq_zero [IsProper sX] {Y : Scheme.{u}}
    (f : X ⟶ Y) {D A : QDivisor X} (hDq : D.IsQCartier) (hAq : A.IsQCartier)
    (hDAq : (D + A).IsQCartier) (hnef : D.IsRelativelyNef sX f) (hA : 0 ≤ A)
    (h0 : ∀ γ : ProperCurve sX, γ.IsContractedBy f →
      (D + A).intersectionNumber k sX γ.ι γ.dim_le hDAq = 0)
    {ξ x : X} (hξx : ξ ⤳ x) (hx : IsClosed ({x} : Set X)) (hxA : x ∈ A.supp)
    (hξA : ξ ∉ A.supp) (hξ : ∀ y : X, ξ ⤳ y → f y = f ξ) : False := by
  obtain ⟨y, hξy, hyx, hyA, hy⟩ :=
    exists_isProperCurve_of_specializes sX hξx hx A.supp.isClosed hxA hξA
  let γ : ProperCurve sX := ⟨y, hy⟩
  have hγ : γ.IsContractedBy f := fun w hw => by
    have hyw : y ⤳ w := specializes_iff_mem_closure.mpr hw
    rw [hξ w (hξy.trans hyw), hξ y hξy]
  obtain ⟨hnn, hiff⟩ := intersectionNumber_nonneg_and_eq_zero_iff sX A hAq hA γ hyA
  have hApos : 0 < A.intersectionNumber k sX γ.ι γ.dim_le hAq :=
    hnn.lt_of_ne fun h => hiff.mp h.symm x hyx hxA
  have hDnn := QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef hDq γ hγ
  have := h0 γ hγ
  rw [QDivisor.intersectionNumber_add' k sX γ.ι γ.dim_le D A hDq hAq] at this
  linarith

end Intersection

/-! ### Finite morphisms and curves -/

section Curve

/-- Two points of a fibre of a finite morphism, one specializing to the other, are equal. -/
theorem eq_of_specializes_of_isFinite {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [IsFinite g]
    {a b : Y'} (hab : a ⤳ b) (hg : g a = g b) : a = b := by
  have hd := g.isDiscrete_preimage_singleton (g b)
  have : DiscreteTopology (g ⁻¹' {g b}) := hd.to_subtype
  have hs : (⟨a, hg⟩ : g ⁻¹' {g b}) ⤳ ⟨b, rfl⟩ :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp hab
  have := hs.mem_open (isOpen_discrete {⟨b, rfl⟩}) rfl
  exact congrArg Subtype.val this

/-- **A finite morphism does not raise dimension.** If `g : Y' ⟶ Y` is finite with image in
`T ⊆ Y`, then `dim Y' ≤ dim T`: a strict chain of irreducible closed subsets of `Y'` has a strict
chain of images, since a finite morphism identifies no two distinct points one of which
specializes to the other. -/
theorem topologicalKrullDim_le_of_isFinite {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [IsFinite g]
    {T : Set Y} (hT : ∀ y, g y ∈ T) : topologicalKrullDim Y' ≤ topologicalKrullDim T := by
  let φ : Y' → T := fun y => ⟨g y, hT y⟩
  have hφ : Continuous φ := g.continuous.subtype_mk hT
  refine Order.krullDim_le_of_strictMono (TopologicalSpace.IrreducibleCloseds.map φ hφ)
    fun A B hAB => ?_
  refine lt_of_le_of_ne (TopologicalSpace.IrreducibleCloseds.map_mono hφ hAB.le) fun heq => ?_
  obtain ⟨a, ha⟩ := QuasiSober.sober A.isIrreducible A.isClosed
  obtain ⟨b, hb⟩ := QuasiSober.sober B.isIrreducible B.isClosed
  have hfa := ha.image hφ
  have hfb := hb.image hφ
  have hcl : closure (φ '' (A : Set Y')) = closure (φ '' (B : Set Y')) :=
    congrArg (fun Z : TopologicalSpace.IrreducibleCloseds T => (Z : Set T)) heq
  rw [hcl] at hfa
  have h1 : φ a = φ b := hfa.eq hfb
  have hba : b ⤳ a := hb.specializes (hAB.le ha.mem)
  have hab : b = a := eq_of_specializes_of_isFinite g hba (congrArg Subtype.val h1).symm
  refine hAB.ne (SetLike.coe_injective ?_)
  rw [← ha.def, ← hb.def, hab]

variable {C : Scheme.{u}} [IsIntegral C]

/-- **A curve has a closed point outside every finite set.** A curve locally of finite type over
a field is a Jacobson space, so its closed points are dense; if they all lay in a finite set,
the generic point would be closed. -/
theorem exists_isClosed_singleton_notMem {k : Type u} [Field k] (sC : C ⟶ Spec (.of k))
    [LocallyOfFiniteType sC] (hC : topologicalKrullDim C = 1) {F : Set C} (hF : F.Finite) :
    ∃ c : C, IsClosed ({c} : Set C) ∧ c ∉ F := by
  by_contra! h
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace sC
  have hsub : closedPoints C ⊆ F ∩ closedPoints C := fun c hc => ⟨h c hc, hc⟩
  have hcl : IsClosed (F ∩ closedPoints C) := by
    rw [← Set.biUnion_of_singleton (F ∩ closedPoints C)]
    exact (hF.subset Set.inter_subset_left).isClosed_biUnion fun c hc => hc.2
  have hη : genericPoint C ∈ F ∩ closedPoints C := by
    have := closure_minimal hsub hcl
    rw [closure_closedPoints] at this
    exact this trivial
  have hsing : ∀ y : C, y = genericPoint C := fun y => by
    have : y ∈ closure ({genericPoint C} : Set C) := by
      rw [(genericPoint_spec C).def]; trivial
    rwa [(hη.2 : IsClosed ({genericPoint C} : Set C)).closure_eq] at this
  have : Subsingleton C := ⟨fun a b => (hsing a).trans (hsing b).symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C
  rw [hC] at h0
  exact absurd h0 (by decide)

end Curve

/-! ### Rational functions with prescribed orders at finitely many points -/

section Approximation

variable {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]

/-- **A regular function as a rational function.** A section `a ∈ Γ(W, 𝒪_C)` with nonempty
non-vanishing locus is a unit `φ` of `K(C)` with `v_E(φ) ≥ 0` along every prime divisor `E`
meeting `W`, with `v_E(φ) = 0` when `a` does not vanish at `η_E` and `v_E(φ) ≥ 1` when it does. -/
theorem exists_unit_of_section {W : C.Opens} (a : Γ(C, W)) (ha : (C.basicOpen a : Set C).Nonempty) :
    ∃ φ : (RationalFunctions C)ˣ, ∀ E : Mori.PrimeDivisor C, E.genericPoint ∈ W →
      0 ≤ E.ord φ ∧ (E.genericPoint ∈ C.basicOpen a → E.ord φ = 0) ∧
        (E.genericPoint ∉ C.basicOpen a → 1 ≤ E.ord φ) := by
  have hη : genericPoint C ∈ C.basicOpen a :=
    ((genericPoint_spec C).mem_open_set_iff (C.basicOpen a).isOpen).mpr (by simpa using ha)
  have hηW : genericPoint C ∈ W := C.basicOpen_le a hη
  have hcomp : ∀ Z : irreducibleComponents C, componentGenericPoint C Z = genericPoint C :=
    componentGenericPoint_eq
  have hmemW : ∀ Z : irreducibleComponents C, componentGenericPoint C Z ∈ W := fun Z => by
    rw [hcomp Z]; exact hηW
  have hunit : ∀ Z : irreducibleComponents C,
      IsUnit (C.presheaf.germ W (componentGenericPoint C Z) (hmemW Z) a) := fun Z =>
    (C.mem_basicOpen a _ (hmemW Z)).mp (by rw [hcomp Z]; exact hη)
  let φ : (RationalFunctions C)ˣ :=
    (RationalFunctions.unitsEquiv C).symm fun Z => (hunit Z).unit
  have hφ : ∀ Z : irreducibleComponents C, (φ : RationalFunctions C) Z =
      C.presheaf.germ W (componentGenericPoint C Z) (hmemW Z) a := fun Z => rfl
  refine ⟨φ, fun E hE => ?_⟩
  set b : E.localRing := C.presheaf.germ W E.genericPoint hE a
  have hb : E.toComponent.hom b = (φ : RationalFunctions C) E.component := by
    rw [hφ]
    change (C.presheaf.germ W E.genericPoint hE ≫ C.presheaf.stalkSpecializes _).hom a = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
  have hb0 : b ≠ 0 := fun h =>
    (hunit E.component).ne_zero (by rw [← hφ, ← hb, h, map_zero])
  have hval := E.valuation_component φ
  refine ⟨?_, fun hEb => ?_, fun hEb => ?_⟩
  · have h1 := E.one_le_valuation_toComponent hb0
    rwa [hb, hval, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  · exact E.ord_eq_zero_of_isUnit ((C.mem_basicOpen a _ hE).mp hEb) hb
  · have hmax : b ∈ IsLocalRing.maximalIdeal E.localRing :=
      (IsLocalRing.mem_maximalIdeal b).mpr fun hu => hEb ((C.mem_basicOpen a _ hE).mpr hu)
    rcases E.ordGE_one_toComponent hmax with h0 | h1
    · exact absurd (by rwa [← hφ, ← hb]) (hunit E.component).ne_zero
    · rwa [hb, hval, WithZero.exp_le_exp] at h1

omit [IsIntegral C] in
/-- The order of vanishing of a finite product is the sum of the orders. -/
theorem PrimeDivisor.ord_prod (P : Mori.PrimeDivisor C) {ι : Type*} (S : Finset ι)
    (φ : ι → (RationalFunctions C)ˣ) : P.ord (∏ i ∈ S, φ i) = ∑ i ∈ S, P.ord (φ i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, PrimeDivisor.ord_mul, ih]

/-- **Weak approximation at finitely many closed points.** Let `S` be a finite set of prime
divisors of `C` whose generic points are closed and lie in an affine open `W`, and let
`P₀ ∈ S`. For all integers `n_P` there is a unit `t` of `K(C)` with `v_{P₀}(t) = n_{P₀}` and
`v_P(t) ≥ n_P` for every `P ∈ S`.

For `P ≠ P₀` in `S` choose `a_P ∈ Γ(W, 𝒪_C)` vanishing at `η_P` but not at `η_{P₀}` (the basic
opens of `W` form a basis), and let `π` be a uniformizer at `P₀`; then
`t = π^{n_{P₀}} ∏ a_P^N` works for `N` large. -/
theorem exists_unit_ord_eq_and_le {W : C.Opens} (hW : IsAffineOpen W)
    (S : Finset (Mori.PrimeDivisor C)) (hSW : ∀ P ∈ S, P.genericPoint ∈ W)
    (hScl : ∀ P ∈ S, IsClosed ({P.genericPoint} : Set C)) {P₀ : Mori.PrimeDivisor C}
    (hP₀ : P₀ ∈ S) (n : Mori.PrimeDivisor C → ℤ) :
    ∃ t : (RationalFunctions C)ˣ, P₀.ord t = n P₀ ∧ ∀ P ∈ S, n P ≤ P.ord t := by
  classical
  have hφ : ∀ P : Mori.PrimeDivisor C, ∃ φ : (RationalFunctions C)ˣ,
      (∀ Q ∈ S, 0 ≤ Q.ord φ) ∧ P₀.ord φ = 0 ∧ (P ∈ S → P ≠ P₀ → 1 ≤ P.ord φ) := by
    intro P
    by_cases hP : P ∈ S ∧ P ≠ P₀
    · obtain ⟨hPS, hPP₀⟩ := hP
      let V : C.Opens := W ⊓ ⟨({P.genericPoint} : Set C)ᶜ, (hScl P hPS).isOpen_compl⟩
      have hne : P₀.genericPoint ≠ P.genericPoint := fun h =>
        hPP₀ (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h).symm
      obtain ⟨a, haV, ha⟩ := hW.exists_basicOpen_le (V := V) ⟨P₀.genericPoint,
        hSW P₀ hP₀, hne⟩ (hSW P₀ hP₀)
      obtain ⟨φ, hφ⟩ := exists_unit_of_section a ⟨_, ha⟩
      refine ⟨φ, fun Q hQ => (hφ Q (hSW Q hQ)).1, (hφ P₀ (hSW P₀ hP₀)).2.1 ha,
        fun _ _ => (hφ P (hSW P hPS)).2.2 fun h => (haV h).2 rfl⟩
    · refine ⟨1, fun Q _ => by simp, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hP⟩
  choose φ hφS hφ₀ hφP using hφ
  obtain ⟨π, hπ⟩ := exists_unit_ord P₀ 1
  let N : ℕ := ∑ P ∈ S, (n P - n P₀ * P.ord π).toNat
  let t : (RationalFunctions C)ˣ := π ^ n P₀ * ∏ Q ∈ S, φ Q ^ N
  have hord : ∀ P : Mori.PrimeDivisor C,
      P.ord t = n P₀ * P.ord π + ∑ Q ∈ S, (N : ℤ) * P.ord (φ Q) := by
    intro P
    rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow, PrimeDivisor.ord_prod, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [PrimeDivisor.ord_pow, nsmul_eq_mul]
  refine ⟨t, ?_, fun P hP => ?_⟩
  · rw [hord, hπ, mul_one, Finset.sum_eq_zero fun Q _ => by rw [hφ₀, mul_zero], add_zero]
  · by_cases hPP₀ : P = P₀
    · subst hPP₀
      rw [hord, hπ, mul_one, Finset.sum_eq_zero fun Q _ => by rw [hφ₀, mul_zero], add_zero]
    have hsum : (N : ℤ) * P.ord (φ P) ≤ ∑ Q ∈ S, (N : ℤ) * P.ord (φ Q) :=
      Finset.single_le_sum (f := fun Q => (N : ℤ) * P.ord (φ Q))
        (fun Q _ => mul_nonneg (Int.natCast_nonneg N) (hφS Q P hP)) hP
    have h1 : 1 ≤ P.ord (φ P) := hφP P hP hPP₀
    have hN : n P - n P₀ * P.ord π ≤ (N : ℤ) := by
      have h2 : (n P - n P₀ * P.ord π).toNat ≤ N :=
        Finset.single_le_sum (f := fun P => (n P - n P₀ * P.ord π).toNat)
          (fun _ _ => Nat.zero_le _) hP
      have h3 := Int.self_le_toNat (n P - n P₀ * P.ord π)
      omega
    have h4 : (N : ℤ) ≤ (N : ℤ) * P.ord (φ P) := by
      have := mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg N)
      simpa using this
    rw [hord]
    linarith

end Approximation

/-! ### Pull-backs of divisors from a curve -/

section PullbackCurve

variable {X C : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]
  (hC : topologicalKrullDim C = 1) (p : X ⟶ C)
  (hη : ∀ (D : Divisor C) (Z : irreducibleComponents X), p (componentGenericPoint X Z) ∉ D.supp)
  (hcart : ∀ D : Divisor C, D.IsCartier)

include hC hcart in
/-- **Coefficients of a pull-back from a curve.** The coefficient of `p^*G` along a prime divisor
`E` of `X` is `G(Q) · (p^*Q)(E)` if `p(η_E)` is the generic point of a prime divisor `Q` of the
curve `C`, and `0` otherwise; in particular its sign is that of `G(Q)`. -/
theorem coeff_isPullback_nonneg_and_eq_zero {G : Divisor C} {G' : Divisor X}
    (hG' : G.IsPullback p (hη G) G') (E : Mori.PrimeDivisor X) :
    ((∀ Q : Mori.PrimeDivisor C, p E.genericPoint = Q.genericPoint → 0 ≤ G.coeff Q) →
      0 ≤ G'.coeff E) ∧
    ((∀ Q : Mori.PrimeDivisor C, p E.genericPoint = Q.genericPoint → G.coeff Q = 0) →
      G'.coeff E = 0) := by
  classical
  set F : Mori.PrimeDivisor C → Divisor X := fun Q =>
    Divisor.pullback (f := p) (Finsupp.single Q 1 : Divisor C) (hcart _) (hη _)
  have hF : ∀ Q, Divisor.IsPullback p (Finsupp.single Q 1 : Divisor C) (hη _) (F Q) := fun Q =>
    Divisor.isPullback_pullback (hcart _) (hη _)
  have hGsum : G = ∑ Q ∈ G.support, G Q • (Finsupp.single Q 1 : Divisor C) := by
    refine Finsupp.ext fun Q => ?_
    simp only [Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h)
  have hpb := (isPullback_sum_smul_single p hη hcart F hF G.support G).of_eq hGsum.symm
    (hB₂ := hη G)
  have hG'eq : G' = ∑ Q ∈ G.support, G Q • F Q := hG'.eq (hcart G) hpb
  have hcoeff : G'.coeff E = ∑ Q ∈ G.support, G Q * (F Q).coeff E := by
    rw [hG'eq]
    simp only [DivisorWithCoeffs.coeff_apply, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  have hclosed : ∀ Q : Mori.PrimeDivisor C, IsClosed ({Q.genericPoint} : Set C) := fun Q =>
    isClosed_singleton_of_ne_genericPoint C hC fun h => by
      have h1 := Q.coheight_genericPoint
      rw [h, Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec C).specializes trivial]
        at h1
      exact zero_ne_one h1
  have hFzero : ∀ Q, p E.genericPoint ≠ Q.genericPoint → (F Q).coeff E = 0 := fun Q hQ =>
    coeff_eq_zero_of_isPullback_single p Q (hclosed Q) (hF Q) E hQ
  have hFnn : ∀ Q, 0 ≤ (F Q).coeff E := fun Q => by
    by_cases hQ : p E.genericPoint = Q.genericPoint
    · exact (coeff_pos_of_isPullback_single p Q (hF Q) E hQ).le
    · rw [hFzero Q hQ]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcoeff]
    refine Finset.sum_nonneg fun Q _ => ?_
    by_cases hQ : p E.genericPoint = Q.genericPoint
    · exact mul_nonneg (h Q hQ) (hFnn Q)
    · rw [hFzero Q hQ, mul_zero]
  · rw [hcoeff]
    refine Finset.sum_eq_zero fun Q _ => ?_
    by_cases hQ : p E.genericPoint = Q.genericPoint
    · rw [show G Q = 0 from h Q hQ, zero_mul]
    · rw [hFzero Q hQ, mul_zero]

end PullbackCurve

/-! ### Divisors `ℚ`-linearly equivalent to a pull-back from the base -/

section QLinearPullback

variable {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral X]

/-- **A `ℚ`-divisor `ℚ`-linearly equivalent to a pull-back is locally principal over the base,
after a multiple.** If `D ∼_ℚ G` and `𝒪_X(m G) ≅ f^* M` for an invertible `𝒪_Z`-module `M`, there
are `N > 0` and a divisor `L = N D` such that every `z ∈ Z` has an open neighbourhood `U` with
`L` principal on `f⁻¹(U)`. -/
theorem exists_smul_eq_and_isLocalEquation_preimage (f : X ⟶ Z) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M] {D G : QDivisor X} (hDG : D.QLinearlyEquivalent G)
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ N : ℕ, 0 < N ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (N : ℤ) • D ∧
      ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ ∃ ψ : (RationalFunctions X)ˣ,
        L.IsLocalEquation (f ⁻¹ᵁ U) ψ := by
  obtain ⟨m, hm, φ, hφ⟩ := hDG
  obtain ⟨m₀, hm₀, L₀, hL₀, ⟨e⟩⟩ := hGM
  refine ⟨m * m₀, Nat.mul_pos hm hm₀, (m : ℤ) • L₀ + (m₀ : ℤ) • principalDivisor φ, ?_,
    fun z => ?_⟩
  · rw [map_add, map_zsmul, map_zsmul, hL₀, ← hφ, smul_smul, smul_smul, smul_sub]
    push_cast
    rw [mul_comm (m₀ : ℤ) (m : ℤ)]
    abel
  · obtain ⟨U, hzU, ψ, hψ⟩ := exists_isLocalEquation_preimage_of_iso_pullback f M e z
    refine ⟨U, hzU, ψ ^ (m : ℤ) * φ ^ (m₀ : ℤ), fun E hE => ?_⟩
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul,
      hψ E hE, coeff_principalDivisor, PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow,
      PrimeDivisor.ord_zpow]

variable {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]

omit [IsIntegral X] in
/-- If a positive multiple `L = N D` is principal over a neighbourhood of every point of the
base, `D` is numerically trivial on every curve contracted by `f`. -/
theorem intersectionNumber_eq_zero_of_isLocalEquation_preimage (hX : IsQFactorial sX)
    (f : X ⟶ Z) {D : QDivisor X} (hDq : D.IsQCartier) {N : ℕ} (hN : 0 < N) {L : Divisor X}
    (hL : Divisor.toQDivisor L = (N : ℤ) • D)
    (hloc : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ ∃ ψ : (RationalFunctions X)ˣ,
        L.IsLocalEquation (f ⁻¹ᵁ U) ψ)
    (γ : ProperCurve sX) (hγ : γ.IsContractedBy f) :
    D.intersectionNumber k sX γ.ι γ.dim_le hDq = 0 := by
  obtain ⟨U, hzU, ψ, hψ⟩ := hloc (f γ.point)
  have hLq : (Divisor.toQDivisor L).IsQCartier := isQCartier_of_isQFactorial sX hX _
  have h0 := intersectionNumber_eq_zero_of_isLocalEquation sX hX hψ hLq γ fun x hx => by
    change f x ∈ U
    rw [hγ x (specializes_iff_mem_closure.mp hx)]
    exact hzU
  have hND : Divisor.toQDivisor L = (N : ℚ) • D := by rw [hL, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  rw [intersectionNumber_congr sX γ.ι γ.dim_le hLq (hND ▸ hLq) hND,
    intersectionNumber_smul sX γ.ι γ.dim_le D hDq (N : ℚ) (hND ▸ hLq)] at h0
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  exact (mul_eq_zero.mp h0).resolve_left hN'

end QLinearPullback

/-! ### Relative freeness of a divisor pulled back from a curve finite over the base -/

section RelativelyFree

variable {X C Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] [CompactSpace C]

/-- **A divisor locally principal over the base, minus a pull-back from a curve, is relatively
free.** Let `f = g ∘ p : X ⟶ C ⟶ Z` with `C` a curve all of whose divisors are Cartier, `p`
proper and `g` finite, `f` not constant. If `L` is principal over a neighbourhood of every point
of `Z` and `R' = p^*R` for a divisor `R` on `C`, then `L - R'` is relatively free over `Z`.

At a closed point `x` with `z = f(x)` and `c = p(x)`, the fibre `g⁻¹(z)` is a finite set of closed
points in an affine open of `C`; a rational function `t` with `v_c(t) = R(c)` and `v_s(t) ≥ R(s)`
along the rest of the fibre (`MMP.Fourfold.exists_unit_ord_eq_and_le`) makes `div t - R`
effective over a neighbourhood of `z`, with coefficient `0` at `c`, and `ψ^{-1} p^*t` generates
`𝒪_X(L - R')` at `x`, for `ψ` a local equation of `L` over `z`. A general point specializes to a
closed one. -/
theorem isRelativelyFreeDivisor_add_neg_pullback (hC : topologicalKrullDim C = 1) (p : X ⟶ C)
    [IsProper p] (g : C ⟶ Z) [IsFinite g] (f : X ⟶ Z) (hpg : p ≫ g = f)
    (hpt : ¬ ∃ z : Z, ∀ x : X, f x = z)
    (hη : ∀ (D : Divisor C) (Z : irreducibleComponents X), p (componentGenericPoint X Z) ∉ D.supp)
    (hcart : ∀ D : Divisor C, D.IsCartier) {L : Divisor X}
    (hloc : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧ ∃ ψ : (RationalFunctions X)ˣ,
        L.IsLocalEquation (f ⁻¹ᵁ U) ψ)
    {R : Divisor C} {R' : Divisor X} (hR' : R.IsPullback p (hη R) R') :
    IsRelativelyFreeDivisor f (L + (-1 : ℤ) • R') := by
  classical
  have hfx : ∀ y : X, g (p y) = f y := fun y => by rw [← hpg]; rfl
  have hfcl : IsClosedMap f := by
    rw [← hpg]
    exact g.isClosedMap.comp p.isClosedMap
  have hηC : ¬ IsClosed ({genericPoint C} : Set C) := not_isClosed_genericPoint hC
  have hQcl : ∀ Q : Mori.PrimeDivisor C, IsClosed ({Q.genericPoint} : Set C) := fun Q =>
    isClosed_singleton_of_ne_genericPoint C hC fun h => by
      have h1 := Q.coheight_genericPoint
      rw [h, Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec C).specializes trivial]
        at h1
      exact zero_ne_one h1
  have hvert : ∀ (P : Mori.PrimeDivisor X) (Q : Mori.PrimeDivisor C) (y : X), y ∈ P.support →
      p P.genericPoint = Q.genericPoint → p y = Q.genericPoint := by
    intro P Q y hy hPQ
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
    have h2 := (specializes_iff_mem_closure.mpr hy).map p.continuous
    rw [hPQ] at h2
    have h3 := specializes_iff_mem_closure.mp h2
    rwa [(hQcl Q).closure_eq] at h3
  have key : ∀ x : X, IsClosed ({x} : Set X) → ∃ (U : Z.Opens) (_ : f x ∈ U)
      (ψ : (RationalFunctions X)ˣ),
      (∀ P : Mori.PrimeDivisor X, (P.support ∩ f ⁻¹ᵁ U).Nonempty →
        0 ≤ (L + (-1 : ℤ) • R').coeff P + P.ord ψ) ∧
      ∀ P : Mori.PrimeDivisor X, x ∈ P.support → (L + (-1 : ℤ) • R').coeff P + P.ord ψ = 0 := by
    intro x hx
    have hzcl : IsClosed ({f x} : Set Z) := by
      have := hfcl _ hx
      rwa [Set.image_singleton] at this
    have hccl : IsClosed ({p x} : Set C) := by
      have := p.isClosedMap _ hx
      rwa [Set.image_singleton] at this
    have hgη : g (genericPoint C) ≠ f x := by
      intro h
      refine hpt ⟨f x, fun x' => ?_⟩
      have h1 : p x' ∈ closure ({genericPoint C} : Set C) := by
        rw [(genericPoint_spec C).def]; trivial
      have h3 := (specializes_iff_mem_closure.mpr h1).map g.continuous
      rw [h] at h3
      have h4 := specializes_iff_mem_closure.mp h3
      rw [hzcl.closure_eq, hfx] at h4
      exact h4
    have hSfin : (g ⁻¹' {f x}).Finite :=
      (hzcl.preimage g.continuous).isCompact.finite (g.isDiscrete_preimage_singleton (f x))
    set S : Finset (Mori.PrimeDivisor C) :=
      (hSfin.preimage AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn).toFinset
    have hmemS : ∀ Q : Mori.PrimeDivisor C, Q ∈ S ↔ g Q.genericPoint = f x := fun Q => by
      simp [S]
    have hcne : p x ≠ genericPoint C := fun h => hηC (h ▸ hccl)
    set P₀ : Mori.PrimeDivisor C := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (p x)
      (coheight_eq_one_of_ne_genericPoint hC hcne)
    have hP₀ : P₀.genericPoint = p x :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have hP₀S : P₀ ∈ S := (hmemS P₀).mpr (by rw [hP₀, hfx])
    obtain ⟨U, hzU, ψ₁, hψ₁⟩ := hloc (f x)
    obtain ⟨V, hV, hzV, hVU⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Z.isBasis_affineOpens)) hzU
    have hW : IsAffineOpen (g ⁻¹ᵁ V) := IsAffineOpen.preimage hV g
    have hSW : ∀ Q ∈ S, Q.genericPoint ∈ g ⁻¹ᵁ V := fun Q hQ => by
      change g _ ∈ V
      rw [(hmemS Q).mp hQ]
      exact hzV
    obtain ⟨t, ht₀, htS⟩ := exists_unit_ord_eq_and_le hW S hSW (fun Q _ => hQcl Q) hP₀S R.coeff
    set Neg : Set (Mori.PrimeDivisor C) := {Q | Q.ord t < R.coeff Q}
    have hNeg : Neg.Finite := by
      refine ((finite_ord_ne_zero t).union R.support.finite_toSet).subset fun Q hQ => ?_
      by_cases h : Q.ord t = 0
      · right
        have : R.coeff Q ≠ 0 := by
          have : Q.ord t < R.coeff Q := hQ
          omega
        simpa [DivisorWithCoeffs.coeff_apply] using this
      · exact Or.inl h
    set Bad : Set C := ⋃ Q ∈ Neg, (Q.support : Set C)
    have hBad : IsClosed Bad :=
      hNeg.isClosed_biUnion fun Q _ => Q.idealSheaf.support.isClosed
    have hT : IsClosed (g '' Bad) := g.isClosedMap _ hBad
    have hzT : f x ∉ g '' Bad := by
      rintro ⟨y, hy, hyz⟩
      obtain ⟨Q, hQ, hyQ⟩ := Set.mem_iUnion₂.mp hy
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, (hQcl Q).closure_eq] at hyQ
      have hQS : Q ∈ S := (hmemS Q).mpr (by rw [← hyQ]; exact hyz)
      exact absurd (htS Q hQS) (not_le.mpr hQ)
    set U' : Z.Opens := U ⊓ ⟨(g '' Bad)ᶜ, hT.isOpen_compl⟩
    have hxU' : f x ∈ U' := ⟨hzU, hzT⟩
    set t' := pullbackRationalFunction p t (hη _)
    have hGpb : (principalDivisor t + (-1 : ℤ) • R).IsPullback p (hη _)
        (principalDivisor t' + (-1 : ℤ) • R') :=
      (Divisor.isPullback_principalDivisor t (hη _)).add (hcart _) ((hcart R).zsmul _) (hη _)
        (hR'.zsmul (hcart R) (-1) (hη _))
    have hid : ∀ P : Mori.PrimeDivisor X, (P.support ∩ f ⁻¹ᵁ U).Nonempty →
        (L + (-1 : ℤ) • R').coeff P + P.ord (ψ₁⁻¹ * t') =
          (principalDivisor t' + (-1 : ℤ) • R').coeff P := by
      intro P hP
      rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hψ₁ P hP,
        PrimeDivisor.ord_mul, PrimeDivisor.ord_inv, DivisorWithCoeffs.coeff_add,
        coeff_principalDivisor, DivisorWithCoeffs.coeff_smul]
      ring
    have hGQ : ∀ Q : Mori.PrimeDivisor C,
        (principalDivisor t + (-1 : ℤ) • R).coeff Q = Q.ord t - R.coeff Q := by
      intro Q
      rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor, DivisorWithCoeffs.coeff_smul]
      ring
    refine ⟨U', hxU', ψ₁⁻¹ * t', fun P hP => ?_, fun P hxP => ?_⟩
    · have hPU : (P.support ∩ f ⁻¹ᵁ U).Nonempty :=
        hP.mono (Set.inter_subset_inter_right _ fun y hy => hy.1)
      rw [hid P hPU]
      refine (coeff_isPullback_nonneg_and_eq_zero hC p hη hcart hGpb P).1 fun Q hPQ => ?_
      rw [hGQ]
      obtain ⟨y, hyP, hyU'⟩ := hP
      have hpy := hvert P Q y hyP hPQ
      have hQ : Q ∉ Neg := by
        intro hQ
        apply hyU'.2
        refine ⟨Q.genericPoint, Set.mem_iUnion₂.mpr ⟨Q, hQ, ?_⟩, ?_⟩
        · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
        · rw [← hpy, hfx]
      have : ¬ Q.ord t < R.coeff Q := hQ
      omega
    · rw [hid P ⟨x, hxP, hzU⟩]
      refine (coeff_isPullback_nonneg_and_eq_zero hC p hη hcart hGpb P).2 fun Q hPQ => ?_
      rw [hGQ]
      have hpx := hvert P Q x hxP hPQ
      have hQP₀ : Q = P₀ :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hpx.symm.trans hP₀.symm)
      subst hQP₀
      rw [ht₀, sub_self]
  refine isRelativelyFreeDivisor_of_forall_exists f fun x => ?_
  obtain ⟨x₀, hx₀, hx₀cl⟩ :=
    (isClosed_closure : IsClosed (closure ({x} : Set X))).exists_closed_singleton
      ⟨x, subset_closure rfl⟩
  obtain ⟨U, hU, ψ, h1, h2⟩ := key x₀ hx₀cl
  have hxx₀ : x ⤳ x₀ := specializes_iff_mem_closure.mpr hx₀
  exact ⟨U, (hxx₀.map f.continuous).mem_open U.isOpen hU, ψ, h1,
    fun P hxP => h2 P (hxx₀.mem_closed P.idealSheaf.support.isClosed hxP)⟩

end RelativelyFree

/-! ### Complemented nef adjoints over a point or a curve -/

section Main

/-- **Relative semiampleness of a nef divisor complemented by a pull-back, over a base of
dimension at most one.** Let `X` be a `ℚ`-factorial projective variety over a perfect field `k`,
`f : X ⟶ Z` a `k`-morphism to a separated `k`-scheme of finite type whose image has dimension
at most one, and `D` an `f`-nef `ℚ`-divisor. Suppose `A ≥ 0` is a `ℚ`-Cartier `ℚ`-divisor and
`D + A ∼_ℚ G`, where `G` is the pull-back of a rational Cartier divisor on `Z`: `𝒪_X(mG) ≅ f^* M`
for some `m > 0` and an invertible `𝒪_Z`-module `M`. Then `D` is `f`-semiample: some positive
multiple `m' D` is a Cartier divisor `L` with `f^* f_* 𝒪_X(L) → 𝒪_X(L)` surjective.

If `f(X)` is a point, every curve is contracted, so `-A ≡ D` is nef and `A = 0`; then `ND` is
principal. Otherwise the Stein factorization `X ⟶ C ⟶ Z` has `C` a normal, hence smooth, curve;
`A` is vertical over `C`, so `A = p^*P`
(`MMP.Fourfold.exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg`), and
`N D = N(D + A) - p^*(N P)` is relatively free for `N` divisible enough
(`MMP.Fourfold.isRelativelyFreeDivisor_add_neg_pullback`). -/
theorem exists_isRelativelyFreeDivisor_of_add_qLinearlyEquivalent {k : Type u} [Field k]
    [PerfectField k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsSeparated sZ]
    [LocallyOfFiniteType sZ] (hXp : Mori.IsProjectiveVariety k sX) (hX : IsQFactorial sX)
    (f : X ⟶ Z) (hf : f ≫ sZ = sX) (himg : topologicalKrullDim (Set.range f) ≤ 1)
    {D : QDivisor X} (hnef : D.IsRelativelyNef sX f) {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) {G : QDivisor X} (hDG : (D + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • D ∧ L.IsCartier ∧
      IsRelativelyFreeDivisor f L := by
  classical
  obtain ⟨hXv, hXproj⟩ := (Mori.isProjectiveVariety_iff k sX).mp hXp
  have : IsIntegral X := hXv.toIsIntegral
  have : IsProper sX := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hXproj).2
  have : IsProper (f ≫ sZ) := hf ▸ inferInstance
  have : IsProper f := IsProper.of_comp f sZ
  obtain ⟨hDq, -⟩ := id hnef
  have hDAq : (D + A).IsQCartier := hDq.add hAq
  obtain ⟨N, hN, L₁, hL₁, hloc⟩ := exists_smul_eq_and_isLocalEquation_preimage f M hDG hGM
  have h0 : ∀ γ : ProperCurve sX, γ.IsContractedBy f →
      (D + A).intersectionNumber k sX γ.ι γ.dim_le hDAq = 0 :=
    intersectionNumber_eq_zero_of_isLocalEquation_preimage sX hX f hDAq hN hL₁ hloc
  have hL₁c : L₁.IsCartier := fun x => by
    obtain ⟨U, hU, ψ, hψ⟩ := hloc (f x)
    exact ⟨f ⁻¹ᵁ U, hU, ψ, hψ⟩
  have hgenmem : ∀ P : Mori.PrimeDivisor X, P.genericPoint ∈ P.support := fun P => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  by_cases hpt : ∃ z : Z, ∀ x : X, f x = z
  · -- the image of `f` is a point
    obtain ⟨z, hz⟩ := hpt
    have hA0 : A = 0 := by
      by_contra hne
      obtain ⟨E, hE⟩ : ∃ E, A E ≠ 0 := by
        by_contra h
        push Not at h
        exact hne (Finsupp.ext h)
      obtain ⟨x, hxE, hxcl⟩ :=
        E.idealSheaf.support.isClosed.exists_closed_singleton ⟨E.genericPoint, hgenmem E⟩
      exact false_of_forall_intersectionNumber_add_eq_zero sX f hDq hAq hDAq hnef hA h0
        ((genericPoint_spec X).specializes trivial) hxcl
        (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE, hxE⟩) (genericPoint_notMem_supp A)
        fun y _ => by rw [hz, hz]
    obtain ⟨U, hzU, ψ, hψ⟩ := hloc z
    have hall : ∀ P : Mori.PrimeDivisor X, (P.support ∩ f ⁻¹ᵁ U).Nonempty := fun P =>
      ⟨P.genericPoint, hgenmem P, show f _ ∈ U by rw [hz]; exact hzU⟩
    refine ⟨N, hN, L₁, by rw [hL₁, hA0, add_zero], hL₁c,
      isRelativelyFreeDivisor_of_forall_exists f fun x =>
        ⟨U, by rw [hz]; exact hzU, ψ⁻¹, fun P hP => ?_, fun P _ => ?_⟩⟩
    · rw [hψ P hP, PrimeDivisor.ord_inv, add_neg_cancel]
    · rw [hψ P (hall P), PrimeDivisor.ord_inv, add_neg_cancel]
  -- the image of `f` is a curve: the Stein factorization
  have : AlgebraicGeometry.IsVariety k sX := hXv
  obtain ⟨C, p, g, ⟨hSt⟩, hpP, hps, hO, -, hgfin, hCvar, -, hCnorm, -, hcontr⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX sZ f hf
  have hpg : p ≫ g = f := hSt.comp
  have hfx : ∀ y : X, g (p y) = f y := fun y => by rw [← hpg]; rfl
  have : IsIntegral C := hCvar.toIsIntegral
  have : IsNormal C := hCnorm inferInstance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sZ)
  have : CompactSpace C := ⟨by
    have := isCompact_univ.image p.continuous
    rwa [Set.image_univ, Set.range_eq_univ.mpr hps.surj] at this⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y : C, y ≠ genericPoint C := by
    obtain ⟨x₁, hx₁⟩ : ∃ x₁ : X, f x₁ ≠ f (genericPoint X) := by
      by_contra h
      push Not at h
      exact hpt ⟨_, h⟩
    by_cases h : p x₁ = genericPoint C
    · refine ⟨p (genericPoint X), fun h' => hx₁ ?_⟩
      rw [← hfx, ← hfx, h, h']
    · exact ⟨p x₁, h⟩
  have hdimC : topologicalKrullDim C = 1 := by
    refine le_antisymm ((topologicalKrullDim_le_of_isFinite g (T := Set.range f) fun y => ?_).trans
      himg) (one_le_topologicalKrullDim_of_specializes_of_ne
        ((genericPoint_spec C).specializes trivial) (Ne.symm hy₀))
    obtain ⟨x, rfl⟩ := p.surjective y
    exact ⟨x, (hfx x).symm⟩
  have hCcurve : Mori.IsCurve k (g ≫ sZ) := (Mori.isCurve_iff k _).mpr ⟨hCvar, hdimC⟩
  have hCsm : IsSmoothScheme (g ≫ sZ) := by
    have hcl : ∀ y : C, y ≠ genericPoint C → y ∈ smoothLocus (g ≫ sZ) := fun y hy => by
      set Qy : Mori.PrimeDivisor C := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y
        (coheight_eq_one_of_ne_genericPoint hdimC hy)
      have hQy : Qy.genericPoint = y :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have := MMP.Threefold.Mori.CanonUniq.genericPoint_mem_smoothLocus (f := g ≫ sZ) hCvar Qy
      rwa [hQy] at this
    refine eq_top_iff.mpr fun y _ => ?_
    by_cases hy : y = genericPoint C
    · rw [hy]
      exact ((genericPoint_spec C).specializes trivial : genericPoint C ⤳ y₀).mem_open
        (smoothLocus (g ≫ sZ)).isOpen (hcl y₀ hy₀)
    · exact hcl y hy
  have hpproj : IsProjectiveMorphism p := by
    refine IsProjectiveMorphism.of_comp p (g ≫ sZ) ?_
    rw [← Category.assoc, hpg, hf]
    exact hXproj
  have hcart : ∀ D : Divisor C, D.IsCartier := isCartier_of_isSmoothScheme hCsm
  have hgenX : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) = genericPoint C := by
    intro Z
    have hZ : Z.1 = Set.univ := by
      have h : Z.1 ∈ ({Set.univ} : Set (Set X)) :=
        (irreducibleComponents_eq_singleton (X := X)) ▸ Z.2
      exact h
    have hgp := isGenericPoint_componentGenericPoint X Z
    rw [hZ] at hgp
    refine IsGenericPoint.eq ?_ (genericPoint_spec C)
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨x, rfl⟩ := p.surjective y
    have hx : x ∈ closure {componentGenericPoint X Z} := by rw [hgp.def]; trivial
    have := image_closure_subset_closure_image p.continuous ⟨x, hx, rfl⟩
    rwa [Set.image_singleton] at this
  have hη : ∀ (D : Divisor C) (Z : irreducibleComponents X),
      p (componentGenericPoint X Z) ∉ D.supp := fun D Z => by
    rw [hgenX]; exact genericPoint_notMem_supp D
  -- `A` is vertical over `C`
  have hAv : QDivisor.IsVertical p A := by
    intro E hE x₂ hx₂
    by_contra hne
    have hηE : p E.genericPoint = genericPoint C := by
      by_contra h
      apply hne
      have hcl := isClosed_singleton_of_ne_genericPoint C hdimC h
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx₂
      have h2 := specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hx₂).map p.continuous)
      rwa [hcl.closure_eq] at h2
    obtain ⟨c, hccl, hcF⟩ := exists_isClosed_singleton_notMem (g ≫ sZ) hdimC
      (F := (fun E' : Mori.PrimeDivisor X => p E'.genericPoint) '' (A.support : Set _))
      (A.support.finite_toSet.image _)
    have hsurjE : ∃ x' ∈ E.support, p x' = c := by
      have hclimg : IsClosed (p '' E.support) := p.isClosedMap _ E.idealSheaf.support.isClosed
      have h1 : closure ({genericPoint C} : Set C) ⊆ p '' E.support :=
        closure_minimal (Set.singleton_subset_iff.mpr ⟨E.genericPoint, hgenmem E, hηE⟩) hclimg
      rw [(genericPoint_spec C).def] at h1
      exact h1 trivial
    obtain ⟨x', hx'E, hx'c⟩ := hsurjE
    obtain ⟨x, ⟨hxE, hxc⟩, hxcl⟩ :=
      (E.idealSheaf.support.isClosed.inter (hccl.preimage p.continuous)).exists_closed_singleton
        ⟨x', hx'E, hx'c⟩
    have hcne : c ≠ genericPoint C := fun h => not_isClosed_genericPoint hdimC (h ▸ hccl)
    set Q : Mori.PrimeDivisor C := AlgebraicGeometry.PrimeDivisor.ofCoheightOne c
      (coheight_eq_one_of_ne_genericPoint hdimC hcne)
    have hQ : Q.genericPoint = c := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have hFpb := Divisor.isPullback_pullback (f := p) (hcart (Finsupp.single Q 1)) (hη _)
    have hxF := mem_supp_of_isPullback_single p Q hFpb (x := x) (by rw [hQ]; exact hxc)
    obtain ⟨E', hE'F, hxE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxF
    have hE'c : p E'.genericPoint = c := by
      by_contra h
      exact hE'F (coeff_eq_zero_of_isPullback_single p Q (hQ ▸ hccl) hFpb E' (by rw [hQ]; exact h))
    have hAE' : A E' = 0 := by
      by_contra h
      exact hcF ⟨E', Finsupp.mem_support_iff.mpr h, hE'c⟩
    refine false_of_forall_intersectionNumber_add_eq_zero sX f hDq hAq hDAq hnef hA h0
      (ξ := E'.genericPoint) (x := x) ?_ hxcl (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE, hxE⟩)
      ?_ ?_
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE'
      exact specializes_iff_mem_closure.mpr hxE'
    · intro h
      obtain ⟨E'', hE'', hE''m⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
      have := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E'' E' hE''m
      subst this
      exact hE'' hAE'
    · intro y hy
      have hpy : p y = c := by
        have h1 := hy.map p.continuous
        rw [hE'c] at h1
        have h2 := specializes_iff_mem_closure.mp h1
        rwa [hccl.closure_eq] at h2
      rw [← hfx, ← hfx, hpy, hE'c]
  -- `-A` is nef over `C`
  have hnAq : (-A).IsQCartier := isQCartier_of_isQFactorial sX hX _
  have hnef' : (-A).IsRelativelyNef sX p :=
    QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hnAq fun γ hγ => by
      have hγf : γ.IsContractedBy f := (hcontr γ).mpr hγ
      have h1 := h0 γ hγf
      rw [QDivisor.intersectionNumber_add' k sX γ.ι γ.dim_le D A hDq hAq] at h1
      have h2 := QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef hDq γ hγf
      have h3 : (-A).intersectionNumber k sX γ.ι γ.dim_le hnAq =
          -A.intersectionNumber k sX γ.ι γ.dim_le hAq := by
        have hm : ((-1 : ℚ) • A).IsQCartier := by rw [neg_one_smul]; exact hnAq
        rw [intersectionNumber_congr sX γ.ι γ.dim_le hnAq hm (neg_one_smul ℚ A).symm,
          intersectionNumber_smul sX γ.ι γ.dim_le A hAq (-1) hm]
        ring
      linarith
  obtain ⟨P, hPq, hPB, -, hAP⟩ := exists_eq_pullback_of_isVertical_of_isRelativelyNef_neg sX
    (g ≫ sZ) hX hXp hCcurve hCsm p hpproj hO A hA hAv hnef'
  -- an integral multiple of `P` and its pull-back
  obtain ⟨d, hd, R, hR⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor ((N : ℤ) • P)
  obtain ⟨R', hR'eq, hR'pb⟩ := QDivisor.isPullback_pullback hPq hPB (d * N) (Nat.mul_pos hd hN)
    R (by rw [hR, smul_smul]; push_cast; rfl) (hcart R)
  rw [← hAP] at hR'eq
  refine ⟨d * N, Nat.mul_pos hd hN, (d : ℤ) • L₁ + (-1 : ℤ) • R', ?_, ?_, ?_⟩
  · rw [map_add, map_zsmul, map_zsmul, hL₁, hR'eq, smul_smul, smul_smul, smul_add]
    module
  · exact (hL₁c.zsmul _).add ((isCartier_of_isPullback p (hcart R) hR'pb).zsmul _)
  · refine isRelativelyFreeDivisor_add_neg_pullback hdimC p g f hpg hpt hη hcart
      (fun z => ?_) hR'pb
    obtain ⟨U, hU, ψ, hψ⟩ := hloc z
    exact ⟨U, hU, ψ ^ (d : ℤ), hψ.zsmul _⟩

/-- **Complemented nef threefold adjoints over a point or a curve are relatively semiample.** Let
`(X, B)` be an effective rational `ℚ`-factorial projective dlt threefold pair over a perfect field
`k` (for instance `ℂ`), with canonical divisor `K`, let `f : X ⟶ Z` be a morphism to a projective
variety whose image has dimension at most one, and let `D = K + B` be `f`-nef. Suppose `A ≥ 0` is
a rational Cartier divisor and `D + A ∼_ℚ f^*H` for a rational Cartier divisor `H` on `Z`, that is
`D + A ∼_ℚ G` with `𝒪_X(mG) ≅ f^* M` for some `m > 0` and the invertible sheaf `M = 𝒪_Z(mH)`.
Then `D` is `f`-semiample: some positive multiple `m' D` is a Cartier divisor `L` which is
relatively free over `Z`, `f^* f_* 𝒪_X(L) → 𝒪_X(L)` being surjective. -/
@[mmp "lem_fourfold_complemented_lc_threefold_small_base_good"]
theorem exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent {k : Type u}
    [Field k] [PerfectField k] {X Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [QuasiCompact sX] (hXp : Mori.IsProjectiveVariety k sX) (hX : IsQFactorial sX)
    (_hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (_hB : 0 ≤ B)
    (_hKB : IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety k sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) (himg : topologicalKrullDim (Set.range f) ≤ 1)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) {G : QDivisor X}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor f L := by
  have : AlgebraicGeometry.IsVariety k sZ := ((Mori.isProjectiveVariety_iff k sZ).mp hZ).1
  exact exists_isRelativelyFreeDivisor_of_add_qLinearlyEquivalent sX sZ hXp hX f hf himg hnef hA
    hAq hDG M hGM

end Main

end MMP.Fourfold
