module

public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierWeilDivisor

/-!
# Sections of `𝒪_X(G)` by orders, and push-forwards of exceptional divisors (Lazarsfeld §9.2)

Let `X` be a normal integral locally Noetherian scheme.

* A rational function `φ ≠ 0`, seen as a section of `𝓜_X` over a non-empty open `V`, is a section
  of `𝒪_X(G)` for a Cartier divisor `G` with Weil divisor `[G]` if and only if
  `ord_P(φ) + ord_P(G) ≥ 0` for every prime divisor `P` meeting `V`.
* For a proper birational morphism `μ : X' ⟶ X` of normal varieties and an effective divisor `G` on
  `X'` every prime component of which lies in `Exc(μ)`, `μ_*𝒪_{X'}(G) = 𝒪_X` inside `K(X)`.

## Main results

* `MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add`
* `MMP.Intersection.multiplierIdealSections_eq_range_of_exceptional`

## Implementation notes

* A rational function `φ ∈ K(X)` is identified with a section `σ ∈ Γ(V, 𝓜_X)` through the germs:
  `σ` restricts to `φ` in `𝓜_{X,x} → K(X)` at every `x ∈ V`
  (`AlgebraicGeometry.totalQuotientStalkToFunctionField`).
* Lazarsfeld's hypothesis that the varieties are non-singular is used only through normality.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry Order

namespace MMP.Intersection

open MMP.Mori (Divisor)

variable {X : Scheme.{u}}

/-! ### The stalks of `𝓜_X` and the function field -/

/-- On a locally Noetherian integral scheme, the stalk `𝓜_{X,x}` is identified with `K(X)`. -/
theorem totalQuotientStalkToFunctionField_bijective [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) : Function.Bijective (totalQuotientStalkToFunctionField x) := by
  have : IsIso (totalQuotientStalkToFunctionField x) := by
    unfold totalQuotientStalkToFunctionField
    refine IsIso.comp_isIso' (Iso.isIso_inv _) ?_
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (RingEquiv.bijective _)
  exact ConcreteCategory.bijective_of_isIso _

/-- The identification `𝓜_{X,x} ≅ K(X)` restricts to the inclusion `𝒪_{X,x} ⊆ K(X)`. -/
theorem totalQuotientStalkToFunctionField_stalkToTotalQuotient [IsIntegral X]
    [IsLocallyNoetherian X] (x : X) (a : X.presheaf.stalk x) :
    totalQuotientStalkToFunctionField x (stalkToTotalQuotient x a) =
      algebraMap (X.presheaf.stalk x) X.functionField a :=
  ConcreteCategory.congr_hom (totalQuotientStalkToFunctionField_comp x) a

/-- The identifications `𝓜_{X,x} ≅ K(X)` are compatible with specialization. -/
theorem totalQuotientStalkToFunctionField_stalkSpecializes [IsIntegral X]
    [IsLocallyNoetherian X] {x y : X} (h : y ⤳ x) (m : X.totalQuotientSheaf.presheaf.stalk x) :
    totalQuotientStalkToFunctionField y (X.totalQuotientSheaf.presheaf.stalkSpecializes h m) =
      totalQuotientStalkToFunctionField x m := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x)
    (totalQuotientStalkToFunctionField x m)
  have hb0 : algebraMap (X.presheaf.stalk x) X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hm : m * stalkToTotalQuotient x b = stalkToTotalQuotient x a := by
    apply (totalQuotientStalkToFunctionField_bijective x).1
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient, ← hab, div_mul_cancel₀ _ hb0]
  have hspec : ∀ c : X.presheaf.stalk x,
      totalQuotientStalkToFunctionField y (X.totalQuotientSheaf.presheaf.stalkSpecializes h
        (stalkToTotalQuotient x c)) = algebraMap (X.presheaf.stalk x) X.functionField c := by
    intro c
    have h1 := ConcreteCategory.congr_hom
      (TopCat.Presheaf.stalkSpecializes_stalkFunctor_map X.toTotalQuotientSheaf.hom h) c
    change stalkToTotalQuotient y (X.presheaf.stalkSpecializes h c) =
      X.totalQuotientSheaf.presheaf.stalkSpecializes h (stalkToTotalQuotient x c) at h1
    rw [← h1, totalQuotientStalkToFunctionField_stalkToTotalQuotient]
    change (X.presheaf.stalkSpecializes _) (X.presheaf.stalkSpecializes h c) =
      (X.presheaf.stalkSpecializes _) c
    rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  have h2 := congrArg (fun t => totalQuotientStalkToFunctionField y
    (X.totalQuotientSheaf.presheaf.stalkSpecializes h t)) hm
  simp only [map_mul, hspec] at h2
  rw [← hab, eq_div_iff hb0, h2]

/-- A local equation of a Cartier divisor is a unit of `K(X)`. -/
theorem totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt [IsIntegral X]
    [IsLocallyNoetherian X] {D : X.CartierDivisor} {x : X}
    {f : X.totalQuotientSheaf.presheaf.stalk x} (hf : IsLocalEquationAt D x f) :
    totalQuotientStalkToFunctionField x f ≠ 0 := by
  obtain ⟨U, hx, g, -, rfl⟩ := hf
  exact ((g.isUnit.map (X.totalQuotientSheaf.presheaf.germ U x hx).hom).map
    (totalQuotientStalkToFunctionField x).hom).ne_zero

/-- The order at `x` of a local equation of `D` at `x` is the multiplicity of `D` at `x`. -/
theorem cartierMultiplicity_eq_ord_of_isLocalEquationAt [IsIntegral X] [IsLocallyNoetherian X]
    {D : X.CartierDivisor} {x : X} {f : X.totalQuotientSheaf.presheaf.stalk x}
    (hf : IsLocalEquationAt D x f) :
    cartierMultiplicity D x = X.ord (totalQuotientStalkToFunctionField x f) x := by
  obtain ⟨U, hx, g, hg, rfl⟩ := hf
  refine cartierMultiplicity_local D x U hx (Additive.ofMul g) ?_
  rw [rawUnitGroupQuotientMap_eq]
  exact hg.symm

/-- The generic point of the subvariety underlying a prime divisor is its generic point. -/
theorem primeDivisorSubvariety_genericPoint (P : MMP.Mori.PrimeDivisor X) :
    (primeDivisorSubvariety P).genericPoint = MMP.Mori.PrimeDivisor.genericPoint P :=
  rfl

/-- The identifications `𝓜_{X,x} ≅ K(X)` agree on the germs of a section at `x` and at a
generization `y` of `x`. -/
theorem totalQuotientStalkToFunctionField_germ_of_specializes [IsIntegral X]
    [IsLocallyNoetherian X] {U : X.Opens} {x y : X} (hyx : y ⤳ x) (hxU : x ∈ U) (hyU : y ∈ U)
    (s : X.totalQuotientSheaf.obj.obj (op U)) :
    totalQuotientStalkToFunctionField y (X.totalQuotientSheaf.presheaf.germ U y hyU s) =
      totalQuotientStalkToFunctionField x (X.totalQuotientSheaf.presheaf.germ U x hxU s) := by
  rw [← totalQuotientStalkToFunctionField_stalkSpecializes hyx]
  congr 1
  exact (ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes _ hxU hyx) _).symm

/-- If `w = [G]`, the order along a prime divisor `P` of a local equation of `G` at the generic
point of `P` is the coefficient `w_P`. -/
theorem ord_eq_coeff_of_isLocalEquationAt [IsIntegral X] [IsLocallyNoetherian X]
    {G : X.CartierDivisor} {wG : Divisor X} (hG : IsWeilDivisorOfCartier G wG)
    (P : MMP.Mori.PrimeDivisor X) {y : X} (hy : MMP.Mori.PrimeDivisor.genericPoint P = y)
    {f : X.totalQuotientSheaf.presheaf.stalk y} (hf : IsLocalEquationAt G y f) :
    X.ord (totalQuotientStalkToFunctionField y f) y = wG.coeff P := by
  subst hy
  rw [← cartierMultiplicity_eq_ord_of_isLocalEquationAt hf]
  have hGP := hG P
  unfold IsOrderAlong at hGP
  dsimp only [primeDivisorSubvariety_genericPoint] at hGP
  obtain ⟨a, b, ha, hb, ⟨g, hg, hgab⟩, la, lb, hla, hlb, hN⟩ := hGP
  rw [cartierMultiplicity_eq_ord_of_isLocalEquationAt hg, hN]
  have hcoh : coheight (MMP.Mori.PrimeDivisor.genericPoint P) = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  have hbK : algebraMap (X.presheaf.stalk _) X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : totalQuotientStalkToFunctionField _ g *
      algebraMap (X.presheaf.stalk _) X.functionField b =
      algebraMap (X.presheaf.stalk _) X.functionField a := by
    have := congrArg (totalQuotientStalkToFunctionField _) hgab.2
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient] at this
    rwa [mul_comm]
  have hTg := totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg
  have hord := X.ord_mul (x := MMP.Mori.PrimeDivisor.genericPoint P) hTg hbK
  rw [key, ord_algebraMap_stalk _ hcoh a (nonZeroDivisors.ne_zero ha),
    ord_algebraMap_stalk _ hcoh b (nonZeroDivisors.ne_zero hb)] at hord
  erw [hla, hlb, ENat.toNat_coe, ENat.toNat_coe] at hord
  omega

/-- **Lazarsfeld §9.2, sections of `𝒪_X(G)` by orders.** Let `X` be a normal integral locally
Noetherian scheme, `G` a Cartier divisor on `X` with Weil divisor `[G]`, `V ⊆ X` a non-empty open
subset and `φ ∈ K(X)^*`, seen as the section `σ ∈ Γ(V, 𝓜_X)`. Then `φ ∈ 𝒪_X(G)(V)` if and only if
`ord_P(φ) + ord_P(G) ≥ 0` for every prime divisor `P` with `P ∩ V ≠ ∅`. -/
@[mmp "lem_p09a_line_bundle_of_divisor_valuative"]
theorem mem_lineBundleSections_iff_forall_zero_le_ord_add [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {G : X.CartierDivisor} {wG : Divisor X} (hG : IsWeilDivisorOfCartier G wG)
    (V : X.Opens) [Nonempty V] {φ : X.functionField} (hφ : φ ≠ 0)
    (σ : X.totalQuotientSheaf.obj.obj (op V))
    (hσ : ∀ (x : X) (hx : x ∈ V), AlgebraicGeometry.totalQuotientStalkToFunctionField x
      (X.totalQuotientSheaf.presheaf.germ V x hx σ) = φ) :
    σ ∈ lineBundleSections G V ↔
      ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ V).Nonempty →
        0 ≤ Scheme.ord φ P.genericPoint + wG.coeff P := by
  constructor
  · intro hσ' P hP
    have hη := genericPoint_mem_of_support_inter_nonempty P hP
    have hGP := hG P
    unfold IsOrderAlong at hGP
    dsimp only [primeDivisorSubvariety_genericPoint] at hGP
    obtain ⟨a, b, -, -, ⟨g, hg, -⟩, -⟩ := hGP
    obtain ⟨c, hc⟩ := hσ' _ hη g hg
    have h1 := congrArg (totalQuotientStalkToFunctionField _) hc
    rw [totalQuotientStalkToFunctionField_stalkToTotalQuotient, map_mul, hσ _ hη] at h1
    have hTg := totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hg
    have hmem := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P) (mul_ne_zero hφ hTg)).mp ⟨c, h1⟩
    rwa [X.ord_mul hφ hTg, ord_eq_coeff_of_isLocalEquationAt hG P rfl hg] at hmem
  · intro h x hx f hf
    have hTf := totalQuotientStalkToFunctionField_ne_zero_of_isLocalEquationAt hf
    have hmem : φ * totalQuotientStalkToFunctionField x f ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range := by
      refine Scheme.mem_range_algebraMap_stalk_of_forall_zero_le_ord x (mul_ne_zero hφ hTf)
        fun y hy hyx => ?_
      obtain ⟨U, hxU, g, hg, rfl⟩ := hf
      have hyU : y ∈ U := hyx.mem_open U.isOpen hxU
      let P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy
      have hPη : MMP.Mori.PrimeDivisor.genericPoint P = y :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy
      rw [X.ord_mul hφ hTf, ← totalQuotientStalkToFunctionField_germ_of_specializes hyx hxU hyU,
        ord_eq_coeff_of_isLocalEquationAt hG P hPη ⟨U, hyU, g, hg, rfl⟩]
      have := h P (support_inter_nonempty_of_genericPoint_mem P (hPη ▸ hyx.mem_open V.isOpen hx))
      rwa [hPη] at this
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, (totalQuotientStalkToFunctionField_bijective x).1 ?_⟩
    rw [totalQuotientStalkToFunctionField_stalkToTotalQuotient, hc, map_mul, hσ x hx]

variable {k : Type u} [Field k] {X' : Scheme.{u}}
variable [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]

/-- **Lazarsfeld §9.2, push-forward of an effective exceptional divisor.** Let `μ : X' ⟶ X` be a
proper birational morphism of normal varieties over `k` and `G` an effective divisor on `X'` every
prime component of which is contained in `Exc(μ)`. Then `μ_*𝒪_{X'}(G) = 𝒪_X` as
`𝒪_X`-submodules of `K(X)`: over every non-empty open `U ⊆ X`, the sections of `μ_*𝒪_{X'}(G)` are
the regular functions on `U`. -/
@[mmp "lem_p09a_pushforward_effective_exceptional"]
theorem multiplierIdealSections_eq_range_of_exceptional
    [MMP.Mori.IsVariety k (X ↘ Spec (.of k))] [MMP.Mori.IsVariety k (X' ↘ Spec (.of k))]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {μ : X' ⟶ X} [μ.IsOver (Spec (.of k))] [IsProper μ] (hμ : MMP.Mori.IsBirationalMorphism μ)
    [IsDominant μ] {G : Divisor X'} (hG : 0 ≤ G)
    (hGexc : ∀ P : MMP.Mori.PrimeDivisor X', G.coeff P ≠ 0 → P.support ⊆ exceptionalLocus μ)
    (U : X.Opens) [Nonempty U] :
    multiplierIdealSections μ G U = Set.range (X.germToFunctionField U) := by
  have hbij := hμ.functionFieldMap_bijective
  have hne : μ ⁻¹ᵁ U ≠ ⊥ := by
    intro h
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    obtain ⟨_, hx', ⟨x', rfl⟩⟩ := μ.denseRange.inter_open_nonempty U U.isOpen ⟨u.1, u.2⟩
    have hmem : x' ∈ μ ⁻¹ᵁ U := hx'
    simp [h] at hmem
  ext g
  constructor
  · rintro ⟨-, hg⟩
    rcases eq_or_ne g 0 with rfl | hg0
    · exact ⟨0, map_zero _⟩
    refine (exists_germToFunctionField_eq_iff_forall_zero_le_ord U hg0).mpr fun Q hQ => ?_
    have hη := genericPoint_mem_of_support_inter_nonempty Q hQ
    rw [← Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q) hg0]
    obtain ⟨x', hx', hco, hexc, hpull⟩ := exists_preimage_of_coheight_eq_one μ hbij
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)
    refine hpull g ?_
    let P' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hco
    have hP' : MMP.Mori.PrimeDivisor.genericPoint P' = x' :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hco
    have hP'U : (P'.support ∩ μ ⁻¹ᵁ U).Nonempty :=
      support_inter_nonempty_of_genericPoint_mem P' (by
        rw [hP']; change μ x' ∈ U; rw [hx']; exact hη)
    have hcoeff : G.coeff P' = 0 := by
      by_contra hc
      apply hexc
      rw [← hP']
      apply hGexc P' hc
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have := hg P' hP'U
    rw [hcoeff, WithZero.exp_zero, MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff] at this
    rwa [← hP']
  · rintro ⟨r, rfl⟩
    refine ⟨fun h => absurd h hne, fun P hP => ?_⟩
    have hη := genericPoint_mem_of_support_inter_nonempty P hP
    have hle : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (G.coeff P) := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      exact hG P
    refine le_trans ?_ hle
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
      ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (show μ P.genericPoint ∈ U from hη),
      MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact ⟨_, rfl⟩

end MMP.Intersection
