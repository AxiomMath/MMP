module

public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Divisors over a variety, small contractions and a tree lemma

Foundational lemmas on multiplicities and discrepancies along divisors over a normal variety,
on `ℚ`-Cartier divisors, on small and birational contractions, on the models of a procedure
datum for a flip, and a combinatorial lemma on trees.

* The multiplicity `mult_F(G)` of an `ℝ`-Cartier divisor `G` along a divisor `F` over `X` does
  not depend on the presentation `G = ∑ r_j L_j` nor on the model realizing `F`; for a Cartier
  divisor with local equation `φ` it is the order of `φ` along `F`. Consequently the discrepancy
  is affine in the boundary: `a(F, D') = a(F, D) - mult_F(D' - D)`.
* A `ℚ`-divisor on a normal scheme is a `ℚ`-combination of Cartier divisors if and only if some
  nonzero multiple of it is Cartier.
* In a finite tree with at least three vertices of degree `≥ 3`, one of them separates two
  others.
* An irreducible closed curve in the exceptional set of a small contraction of a threefold is a
  flipping curve.
* A proper birational morphism `g : Y ⟶ X` onto a normal variety satisfies `g_* 𝒪_Y = 𝒪_X` and
  is an isomorphism over an open set whose complement has codimension `≥ 2`; if moreover `Y` is
  normal and `g` contracts no prime divisor, `g` is small.
* For a procedure datum `(π, (F_j), H')` and a proper birational `h' : Y' ⟶ Z` from a normal
  variety, an isomorphism over `Z ∖ Supp H'`, the exceptional divisors of `h'` and `h'⁻¹(T)` lie
  in `Supp h'^*H'`, and `h'^*H' = h'⁻¹_*H' + ∑ α_k E_k` with `α_k ≥ 0`.

## Main results

* `MMP.Flips.IsMultiplicityAlong.eq_and_eq_neg_log`
* `MMP.Flips.IsDiscrepancy.sub_of_isMultiplicityAlong`
* `MMP.Mori.QDivisor.isCartierCombination_iff_isQCartier`
* `MMP.Foundations.exists_branch_vertex_separating_branch_vertices_of_isTree`
* `MMP.Flips.isFlippingCurve_of_subset_exceptionalSet`
* `MMP.Flips.isIso_app_and_exists_isBiregular_of_isBirationalMorphism`
* `MMP.Flips.isSmall_of_forall_primeDivisor_image`
* `MMP.Flips.ProcedureDatum.exceptional_subset_supp_pullback`

## Implementation notes

The discrepancy `MMP.Flips.IsDiscrepancy` and the multiplicity `MMP.Flips.IsMultiplicityAlong`
are relations between the data and a real number; `F` is a valuation `k(X) → ℤᵐ⁰` in Mathlib's
multiplicative convention, so the additive order of `φ` along `F` is `-log F(φ)`.

The source deduces `g_* 𝒪_Y = 𝒪_X` from integrality of `g_* 𝒪_Y` over the normal `𝒪_X`. Here
it is deduced from the isomorphism over the domain `V` of `g⁻¹` and algebraic Hartogs across the
codimension-two complement of `V`, which avoids coherence of direct images.

The base `Z` of a procedure datum is only assumed locally Noetherian and normal; that it is
integral and separated follows from the existence of `h'`, since a universally closed surjective
morphism from a separated scheme has a separated target.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (1.1), 2.3,
  2.5.3, 2.17, Remark 4.14, Chapter 6, 18.12.2
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

/-! ### The multiplicity along a divisor over `X` is well defined -/

section Multiplicity

open MMP.Mori

namespace MMP.Flips

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- On an integral scheme, the identification `K(X) ≃ k(X)` is evaluation at the generic point
along the (unique) component. -/
private theorem rationalFunctionsEquivFunctionField_eq_evalFF {X : Scheme.{u}} [IsIntegral X]
    (Z : irreducibleComponents X) (φ : RationalFunctions X) :
    rationalFunctionsEquivFunctionField X φ = MMP.Threefold.Mori.Helpers.evalFF Z φ := by
  unfold rationalFunctionsEquivFunctionField Stacks.Chow.rationalFunctionsEquivFunctionField
  simp only [RingEquiv.trans_apply]
  erw [RingEquiv.apply_symm_apply]
  change ((X.presheaf.stalkCongr _).hom (φ _)) = _
  rw [TopCat.Presheaf.stalkCongr_hom]
  unfold MMP.Threefold.Mori.Helpers.evalFF
  simp only [RingHom.comp_apply, RationalFunctions.component, Pi.evalRingHom_apply]
  have hs : (irreducibleComponents X).Subsingleton := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.subsingleton_singleton
  have hsub : ∀ W W' : irreducibleComponents X, W = W' := fun W W' => Subtype.ext (hs W.2 W'.2)
  have key : ∀ (W W' : irreducibleComponents X) (_ : W = W')
      (p : genericPoint X ⤳ componentGenericPoint X W)
      (p' : genericPoint X ⤳ componentGenericPoint X W'),
      (X.presheaf.stalkSpecializes p).hom (φ W) = (X.presheaf.stalkSpecializes p').hom (φ W') := by
    rintro W _ rfl p p'
    rfl
  exact key _ _ (hsub _ _) _ _

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- **The multiplicity through a relation at the center.** If `μ` is a multiplicity of `G` along
`F` computed on `(Y, f, E)`, and nonzero rational functions `g_j` with real weights `w_j` satisfy
`∑ w_j v_Γ(g_j) = coeff_Γ(G)` for every prime divisor `Γ` through `f(η_E)`, then
`μ = ∑ w_j (-log F(g_j))`. -/
private theorem eq_sum_of_forall_coeff {G : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} {F : Valuation X.functionField ℤᵐ⁰} {E : ProperDivisorOver k sX}
    {μ : ℝ} (h : IsMultiplicityAlong sX G r L F E μ) {p : Type*} [Fintype p]
    (g : p → X.functionField) (hg : ∀ j, g j ≠ 0) (w : p → ℝ)
    (hw : ∀ Γ : MMP.Mori.PrimeDivisor X, E.f E.E.genericPoint ∈ Γ.support →
      ∑ j, (X.ord (g j) Γ.genericPoint : ℝ) * w j = G.coeff Γ) :
    μ = ∑ j, (-(WithZero.log (F (g j)) : ℤ) : ℝ) * w j := by
  classical
  obtain ⟨-, -, hEF, hLc, rfl, L', hpb, rfl⟩ := h
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  set x := E.f E.E.genericPoint
  choose V hV φ hφ using fun i => hLc i x
  let Z0 := MMP.Mori.pointComponent x
  let g' : Fin m → X.functionField := fun i =>
    MMP.Threefold.Mori.Helpers.evalFF Z0 ((φ i : MMP.Mori.RationalFunctions X))
  have hg' : ∀ i, g' i ≠ 0 := fun i => ((φ i).isUnit.map _).ne_zero
  have hZ : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.component = Z0 := fun Γ => Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  have hF : ∀ t : X.functionField, t ≠ 0 →
      (-(WithZero.log (F t) : ℤ) : ℝ) = E.Y.ord (functionFieldMap E.f t) E.E.genericPoint := by
    intro t ht
    rw [← hEF]
    change (-(WithZero.log (E.E.valuationOver E.f t) : ℤ) : ℝ) = _
    rw [PrimeDivisor.valuationOver_apply,
      E.E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr ht), WithZero.log_exp]
    push_cast
    ring
  let Gs : Fin m ⊕ p → X.functionField := Sum.elim g' g
  let ws : Fin m ⊕ p → ℝ := Sum.elim r fun j => -w j
  have hGs : ∀ j, Gs j ≠ 0 := by
    rintro (i | j)
    exacts [hg' i, hg j]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := E.f) E.E Gs hGs ws
    fun Γ hΓ => by
      simp only [Fintype.sum_sum_type, Gs, ws, Sum.elim_inl, Sum.elim_inr]
      have e1 := hw Γ hΓ
      rw [coeff_sum_smul_toRDivisor] at e1
      have e2 : ∀ i, (X.ord (g' i) Γ.genericPoint : ℝ) = (L i).coeff Γ := fun i => by
        rw [hφ i Γ ⟨x, hΓ, hV i⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
      simp_rw [e2, mul_neg, Finset.sum_neg_distrib, e1, mul_comm (L _ |>.coeff Γ : ℝ)]
      ring
  have hcoeff : ∀ i, ((L' i).coeff E.E : ℝ) =
      E.Y.ord (functionFieldMap E.f (g' i)) E.E.genericPoint :=
    fun i => mod_cast
      MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hpb i).2 (hφ i) E.E (hV i) Z0
  simp only [Fintype.sum_sum_type, Gs, ws, Sum.elim_inl, Sum.elim_inr] at key
  simp_rw [hcoeff]
  simp_rw [mul_neg, Finset.sum_neg_distrib, mul_comm _ (r _),
    fun j => (hF (g j) (hg j)).symm] at key
  linear_combination key

/-- **The multiplicity along a divisor over `X` is well defined.** If `μ` and `μ'` are
multiplicities of `G` along `F` computed from presentations `G = ∑ r_j L_j = ∑ r'_j L'_j` and
realizations `E`, `E'` of `F`, then `μ = μ'`. If `L` is a Cartier divisor with local equation `φ`
on an open set `U` meeting `Center_X(F)`, then any multiplicity `μ` of `L` along `F` is the
order of `φ` along `F`, `μ = -log F(φ)`. -/
@[mmp "lem_fa2_multiplicity_along_divisor_well_defined"]
public theorem IsMultiplicityAlong.eq_and_eq_neg_log {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (F : Valuation X.functionField ℤᵐ⁰) :
    (∀ (G : RDivisor X) {m m' : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
        (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X) (E E' : ProperDivisorOver k sX)
        (μ μ' : ℝ),
        IsMultiplicityAlong sX G r L F E μ → IsMultiplicityAlong sX G r' L' F E' μ' →
          μ = μ') ∧
    (∀ (L : Divisor X) {m : ℕ} (r : Fin m → ℝ) (M : Fin m → Divisor X)
        (E : ProperDivisorOver k sX) (μ : ℝ) (U : X.Opens) (φ : (RationalFunctions X)ˣ),
        L.IsLocalEquation U φ → ((E.center : Set X) ∩ U).Nonempty →
        IsMultiplicityAlong sX (Divisor.toRDivisor L) r M F E μ →
          μ = -((WithZero.log (F (rationalFunctionsEquivFunctionField X (φ : RationalFunctions X)))
            : ℤ) : ℝ)) := by
  have hZ : ∀ (Γ : MMP.Mori.PrimeDivisor X) (Z : irreducibleComponents X), Γ.component = Z :=
    fun Γ Z => Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  refine ⟨fun G m m' r L r' L' E E' μ μ' h h' => ?_, fun L m r M E μ U φ hφ hU h => ?_⟩
  · have hcen : E.f E.E.genericPoint = E'.f E'.E.genericPoint :=
      MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq h.1
        (h.2.2.1.trans h'.2.2.1.symm)
    set x := E.f E.E.genericPoint
    choose V hV φ hφ using fun i => h.2.2.2.1 i x
    let g : Fin m → X.functionField := fun i =>
      MMP.Threefold.Mori.Helpers.evalFF (pointComponent x) ((φ i : MMP.Mori.RationalFunctions X))
    have hg : ∀ i, g i ≠ 0 := fun i => ((φ i).isUnit.map _).ne_zero
    have hw : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support →
        ∑ i, (X.ord (g i) Γ.genericPoint : ℝ) * r i = G.coeff Γ := by
      intro Γ hΓ
      rw [h.2.2.2.2.1, coeff_sum_smul_toRDivisor]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hφ i Γ ⟨x, hΓ, hV i⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ Γ, mul_comm]
    rw [eq_sum_of_forall_coeff h g hg r hw, eq_sum_of_forall_coeff h' g hg r (hcen ▸ hw)]
  · set x := E.f E.E.genericPoint
    have hxU : x ∈ U := by
      obtain ⟨z, ⟨y, hy, rfl⟩, hzU⟩ := hU
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
      exact ((specializes_iff_mem_closure.mpr hy).map E.f.continuous).mem_open U.isOpen hzU
    have hne : rationalFunctionsEquivFunctionField X (φ : RationalFunctions X) ≠ 0 :=
      (φ.isUnit.map (rationalFunctionsEquivFunctionField X)).ne_zero
    have hw : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support →
        ∑ _ : Unit, (X.ord (rationalFunctionsEquivFunctionField X (φ : RationalFunctions X))
          Γ.genericPoint : ℝ) * 1 = (Divisor.toRDivisor L).coeff Γ := by
      intro Γ hΓ
      rw [Fintype.sum_unique, mul_one, Divisor.coeff_toRDivisor, hφ Γ ⟨x, hΓ, hxU⟩,
        MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
        rationalFunctionsEquivFunctionField_eq_evalFF Γ.component]
    rw [eq_sum_of_forall_coeff h (fun _ : Unit => _) (fun _ => hne) (fun _ => 1) hw,
      Fintype.sum_unique, mul_one]

end MMP.Flips

end Multiplicity

/-! ### The discrepancy is affine in the boundary -/

section Discrepancy

open MMP.Mori

namespace MMP.Flips

/-- A multiplicity `μ = mult_F(G)` computed on one realization of `F` can be computed on any
other realization `E₁` of `F`, with the same presentation of `G`: the Cartier divisors `L_j`
pull back to `E₁.Y`, and the multiplicity is well defined. -/
private lemma IsMultiplicityAlong.exists_isPullback {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {G : RDivisor X}
    {F : Valuation X.functionField ℤᵐ⁰} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {μ : ℝ} (hμ : IsMultiplicityAlong sX G r L F E μ)
    (E₁ : ProperDivisorOver k sX) (hE₁ : E₁.valuation = F) :
    haveI := E₁.isLocallyNoetherian
    haveI := E₁.isNormal
    ∃ M : Fin m → Divisor E₁.Y,
      (∀ j, ∃ hB : ∀ Z : irreducibleComponents E₁.Y,
          E₁.f (componentGenericPoint E₁.Y Z) ∉ (L j).supp,
        (L j).IsPullback E₁.f hB (M j)) ∧
      μ = ∑ j, r j * (M j).coeff E₁.E := by
  obtain ⟨hX, hF, -, hLc, hsum, -⟩ := id hμ
  have := E₁.isIntegral
  have := E₁.isLocallyNoetherian
  have := E₁.isNormal
  have := E₁.isDominant
  have : IsProper E₁.f := E₁.isProper
  have : CompactSpace E₁.Y := QuasiCompact.compactSpace_of_compactSpace E₁.f
  choose M hM using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E₁.f (hLc j)
  have hM' : ∀ j, ∃ hB : ∀ Z : irreducibleComponents E₁.Y,
      E₁.f (componentGenericPoint E₁.Y Z) ∉ (L j).supp, (L j).IsPullback E₁.f hB (M j) :=
    fun j => ⟨_, hM j⟩
  exact ⟨M, hM', (IsMultiplicityAlong.eq_and_eq_neg_log sX F).1 _ r L r L _ E₁ μ _ hμ
    ⟨hX, hF, hE₁, hLc, hsum, M, hM', rfl⟩⟩

/-- **The discrepancy is affine in the boundary.** Let `X` be a normal variety of dimension `n`,
`K_X` a canonical divisor and `D`, `D'` `ℝ`-divisors on `X`. If `a = a(F, D)` is the discrepancy
of a divisor `F` of `k(X)` (so `K_X + D` is `ℝ`-Cartier and `F` has nonempty center on `X`) and
`μ = mult_F(D' - D)` is the multiplicity along `F` of `D' - D`, computed from a presentation
`D' - D = ∑ r_j L_j` by Cartier divisors and a divisor `E` over `X` realizing `F`, then
`a - μ = a(F, D')`. -/
@[mmp "lem_fa2_discrepancy_affine_in_boundary"]
public theorem IsDiscrepancy.sub_of_isMultiplicityAlong {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {D D' : RDivisor X}
    {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ} (h : IsDiscrepancy sX n K D F a)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {E : ProperDivisorOver k sX} {μ : ℝ}
    (hμ : IsMultiplicityAlong sX (D' - D) r L F E μ) :
    IsDiscrepancy sX n K D' F (a - μ) := by
  obtain ⟨hK, -, hF, E₁, ω, m₁, r₁, L₁, hE₁, hω, hX, hn, hω0, hL₁c, hsum₁, L₁', hpb₁, rfl⟩ := h
  obtain ⟨M, hM, rfl⟩ := IsMultiplicityAlong.exists_isPullback hμ E₁ hE₁
  have hc : ∀ j, (Fin.append L₁ L j).IsCartier :=
    Fin.addCases (fun j => by simpa using hL₁c j) (fun j => by simpa using hμ.2.2.2.1 j)
  have hsum : Divisor.toRDivisor (divisorOfForm ω) + D' =
      ∑ j, Fin.append r₁ r j • Divisor.toRDivisor (Fin.append L₁ L j) := by
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, ← hsum₁, ← hμ.2.2.2.2.1]
    abel
  refine ⟨hK, ⟨_, _, _, hc, hω ▸ hsum⟩, hF, E₁, ω, _, _, _, hE₁, hω, hX, hn, hω0, hc, hsum,
    Fin.append L₁' M,
    Fin.addCases (fun j => by simpa using hpb₁ j) (fun j => by simpa using hM j), ?_⟩
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  ring

end MMP.Flips

end Discrepancy

/-! ### `ℚ`-Cartier as a combination of Cartier divisors versus a Cartier multiple -/

section QCartier

open MMP.Mori

namespace MMP.Mori.QDivisor

/-- Finitely many rationals have a common denominator: some `m > 0` makes every `m * r j` an
integer. -/
private lemma exists_pos_nat_mul_eq_intCast {ι : Type*} [Fintype ι] (r : ι → ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∀ j, ∃ n : ℤ, (m : ℚ) * r j = n := by
  refine ⟨∏ j, (r j).den, Finset.prod_pos fun j _ => (r j).den_pos, fun j => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j => (r j).den) (Finset.mem_univ j)
  refine ⟨c * (r j).num, ?_⟩
  rw [hc]
  push_cast
  rw [← Rat.mul_den_eq_num (r j)]
  ring

/-- A `ℚ`-divisor on a normal scheme is a `ℚ`-linear combination of Cartier divisors if and only
if it is `ℚ`-Cartier, i.e. some nonzero integral multiple of it is an integral Cartier divisor. -/
@[mmp "lem_fa2_q_cartier_iff_multiple_cartier"]
public theorem isCartierCombination_iff_isQCartier {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (D : QDivisor X) :
    MMP.Flips.IsCartierCombination D ↔ D.IsQCartier := by
  constructor
  · rintro ⟨k, r, L, hL, rfl⟩
    obtain ⟨m, hm, hint⟩ := exists_pos_nat_mul_eq_intCast r
    choose n hn using hint
    refine QDivisor.isQCartier_iff_exists_pos.mpr ⟨m, hm, ∑ j, n j • L j, ?_,
      Divisor.cartierSubgroup.sum_mem fun j _ => (hL j).zsmul (n j)⟩
    simp only [map_sum, map_zsmul, Finset.smul_sum, ← Int.cast_smul_eq_zsmul ℚ, ← hn, mul_smul,
      Int.cast_natCast]
    rfl
  · intro h
    obtain ⟨m, hm, D', hD', hc⟩ := QDivisor.isQCartier_iff_exists_pos.mp h
    refine ⟨1, fun _ => (m : ℚ)⁻¹, fun _ => D', fun _ => hc, ?_⟩
    change D = ∑ _ : Fin 1, (m : ℚ)⁻¹ • Divisor.toQDivisor D'
    rw [Fin.sum_univ_one, hD', ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
      inv_mul_cancel₀ (by positivity), one_smul]

end MMP.Mori.QDivisor

end QCartier

/-! ### A branch vertex separating two other branch vertices of a tree -/

section TreeFork

open SimpleGraph

namespace MMP.Foundations

variable {V : Type*} {G : SimpleGraph V}

/-- A walk from `w ≠ m` to `m` yields a neighbour `n` of `m` and a walk from `w` to `n`
avoiding `m`. -/
private lemma exists_adj_walk_notMem {w m : V} (p : G.Walk w m) (hw : w ≠ m) :
    ∃ n, G.Adj m n ∧ ∃ q : G.Walk w n, m ∉ q.support := by
  induction p with
  | nil => exact absurd rfl hw
  | @cons u v x h p ih =>
    by_cases hv : v = x
    · subst hv
      exact ⟨u, h.symm, Walk.nil, by simpa using Ne.symm hw⟩
    · obtain ⟨n, hn, q, hq⟩ := ih hv
      exact ⟨n, hn, Walk.cons h q, by simp [Ne.symm hw, hq]⟩

/-- In a tree, if `n` is a neighbour of `m` and `w` reaches `n` avoiding `m`, then `n` is one
step closer to `w` than `m` is. -/
private lemma dist_eq_dist_add_one_of_walk_notMem (hG : G.IsTree) {w m n : V}
    (hadj : G.Adj m n) (p : G.Walk w n) (hp : m ∉ p.support) :
    G.dist w m = G.dist w n + 1 := by
  classical
  rcases hG.dist_eq_dist_add_one_of_adj w hadj with h | h
  · exact h
  · exfalso
    obtain ⟨q, -, hql⟩ := (hG.connected w m).exists_path_of_dist
    have hr : (q.concat hadj).IsPath :=
      (q.concat hadj).isPath_of_length_eq_dist (by simp [Walk.length_concat, hql, h])
    have := hG.isAcyclic.path_unique ⟨_, hr⟩ ⟨_, p.bypass_isPath⟩
    have hm : m ∈ (q.concat hadj).support := by simp [Walk.support_concat]
    rw [show q.concat hadj = p.bypass from congrArg Subtype.val this] at hm
    exact hp (p.support_bypass_subset_support hm)

/-- At a minimiser `m` of the distance sum to `a b c`, no walk from `a ≠ m` to `b`
avoids `m`. -/
private lemma no_walk_notMem_of_min (hG : G.IsTree) {a b c m : V} (ha : a ≠ m)
    (hmin : ∀ u, G.dist m a + G.dist m b + G.dist m c ≤ G.dist u a + G.dist u b + G.dist u c)
    (p : G.Walk a b) (hp : m ∉ p.support) : False := by
  obtain ⟨n, hn, q, hq⟩ := exists_adj_walk_notMem (hG.connected a m).some ha
  have h1 := dist_eq_dist_add_one_of_walk_notMem hG hn q hq
  have h2 := dist_eq_dist_add_one_of_walk_notMem hG hn (p.reverse.append q)
    (by simp [Walk.mem_support_append_iff, hp, hq])
  have h3 : G.dist n c ≤ G.dist n m + G.dist m c := hG.connected.dist_triangle
  have h4 : G.dist n m = 1 := dist_eq_one_iff_adj.mpr hn.symm
  have := hmin n
  rw [SimpleGraph.dist_comm (u := m) (v := a), SimpleGraph.dist_comm (u := m) (v := b),
    SimpleGraph.dist_comm (u := n) (v := a), SimpleGraph.dist_comm (u := n) (v := b)] at this
  omega

/-- If no walk from `a` to `b` avoids `m`, then the endpoints of walks from `a` and from `b`
avoiding `m` are distinct. -/
private lemma ne_of_no_walk_notMem {a b m na nb : V}
    (h : ∀ p : G.Walk a b, m ∉ p.support → False) (qa : G.Walk a na) (hqa : m ∉ qa.support)
    (qb : G.Walk b nb) (hqb : m ∉ qb.support) : na ≠ nb := by
  rintro rfl
  exact h (qa.append qb.reverse) (by simp [Walk.mem_support_append_iff, hqa, hqb])

/-- If no walk between `a` and `b` avoids `m`, they are not reachable in `G - m`. -/
private lemma not_reachable_of_no_walk {m : V} {a b : ({m}ᶜ : Set V)}
    (h : ∀ p : G.Walk a.1 b.1, m ∉ p.support → False) :
    ¬ (G.induce {m}ᶜ).Reachable a b := by
  rintro ⟨p⟩
  suffices ∀ {c d : ({m}ᶜ : Set V)} (p : (G.induce {m}ᶜ).Walk c d),
      ∃ q : G.Walk c.1 d.1, m ∉ q.support by
    obtain ⟨q, hq⟩ := this p
    exact h q hq
  intro c d p
  induction p with
  | @nil c => exact ⟨Walk.nil, by simpa using fun h => c.2 (Set.mem_singleton_iff.mpr h.symm)⟩
  | @cons c e d hce p ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨Walk.cons (by simpa using hce) q,
      by simpa [hq] using fun h => c.2 (Set.mem_singleton_iff.mpr h.symm)⟩

variable [Fintype V] [DecidableRel G.Adj]

/-- In a finite tree with at least three vertices of degree `≥ 3`, some vertex `v` of degree
`≥ 3` has two vertices `a`, `b` of degree `≥ 3` in different connected components of the
graph obtained by deleting `v`. -/
@[mmp "lem_fa3_tree_fork_combinatorics"]
public theorem exists_branch_vertex_separating_branch_vertices_of_isTree (hG : G.IsTree)
    (h3 : 3 ≤ (Finset.univ.filter fun v => 3 ≤ G.degree v).card) :
    ∃ v, 3 ≤ G.degree v ∧ ∃ (a b : V) (ha : a ≠ v) (hb : b ≠ v),
      3 ≤ G.degree a ∧ 3 ≤ G.degree b ∧
        ¬ (G.induce {v}ᶜ).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp h3
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ
    (fun u => G.dist u x + G.dist u y + G.dist u z) ⟨x, Finset.mem_univ _⟩
  have hmin : ∀ u, G.dist m x + G.dist m y + G.dist m z ≤
      G.dist u x + G.dist u y + G.dist u z := fun u => hm u (Finset.mem_univ _)
  have sxy : x ≠ m → ∀ p : G.Walk x y, m ∉ p.support → False :=
    fun h => no_walk_notMem_of_min hG h hmin
  have sxz : x ≠ m → ∀ p : G.Walk x z, m ∉ p.support → False :=
    fun h => no_walk_notMem_of_min hG h (c := y) (fun u => by have := hmin u; omega)
  have syz : y ≠ m → ∀ p : G.Walk y z, m ∉ p.support → False :=
    fun h => no_walk_notMem_of_min hG h (c := x) (fun u => by have := hmin u; omega)
  by_cases hmx : m = x
  · subst hmx
    exact ⟨m, hx, y, z, hxy.symm, hxz.symm, hy, hz, not_reachable_of_no_walk (syz hxy.symm)⟩
  by_cases hmy : m = y
  · subst hmy
    exact ⟨m, hy, x, z, hxy, hyz.symm, hx, hz, not_reachable_of_no_walk (sxz hxy)⟩
  by_cases hmz : m = z
  · subst hmz
    exact ⟨m, hz, x, y, hxz, hyz, hx, hy, not_reachable_of_no_walk (sxy hxz)⟩
  refine ⟨m, ?_, x, y, Ne.symm hmx, Ne.symm hmy, hx, hy,
    not_reachable_of_no_walk (sxy (Ne.symm hmx))⟩
  obtain ⟨nx, hnx, qx, hqx⟩ := exists_adj_walk_notMem (hG.connected x m).some (Ne.symm hmx)
  obtain ⟨ny, hny, qy, hqy⟩ := exists_adj_walk_notMem (hG.connected y m).some (Ne.symm hmy)
  obtain ⟨nz, hnz, qz, hqz⟩ := exists_adj_walk_notMem (hG.connected z m).some (Ne.symm hmz)
  have h12 := ne_of_no_walk_notMem (sxy (Ne.symm hmx)) qx hqx qy hqy
  have h13 := ne_of_no_walk_notMem (sxz (Ne.symm hmx)) qx hqx qz hqz
  have h23 := ne_of_no_walk_notMem (syz (Ne.symm hmy)) qy hqy qz hqz
  rw [← card_neighborFinset_eq_degree]
  calc 3 = ({nx, ny, nz} : Finset V).card :=
        (Finset.card_eq_three.mpr ⟨nx, ny, nz, h12, h13, h23, rfl⟩).symm
    _ ≤ _ := Finset.card_le_card (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> simpa)

end MMP.Foundations

end TreeFork

/-! ### Curves in the exceptional set of a small contraction are flipping curves -/

section FlippingCurve

namespace MMP.Flips

/-- On a variety of dimension `3`, there is no chain `a ⤳ b ⤳ c` of distinct points with
`coheight a ≥ 2`. -/
private theorem false_of_two_le_coheight_of_specializes {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsVariety k sX) (hdim : topologicalKrullDim X = 3)
    {a b c : X} (ha : 2 ≤ Order.coheight a) (hab : a ⤳ b) (hbc : b ⤳ c) (hab' : a ≠ b)
    (hbc' : b ≠ c) : False := by
  have := hX.toIsIntegral
  have := hX.toLocallyOfFiniteType
  have h := topologicalKrullDim_closure_singleton_add_coheight sX a
  have h2 := two_le_topologicalKrullDim_of_specializes (S := closure {a}) (subset_closure rfl)
    hab.mem_closure (hab.trans hbc).mem_closure hab hbc hab' hbc'
  rw [hdim] at h
  have h4 : (2 : WithBot ℕ∞) + 2 ≤ 3 := h ▸ add_le_add h2 (WithBot.coe_le_coe.mpr ha)
  exact absurd h4 (by decide)

/-- A morphism which is an open immersion on an open `O` is injective on `O`. -/
private theorem eq_of_isOpenImmersion {X Z : Scheme.{u}} {φ : X ⟶ Z} {O : X.Opens}
    (hO : IsOpenImmersion (O.ι ≫ φ)) {a b : X} (ha : a ∈ O) (hb : b ∈ O) (h : φ a = φ b) :
    a = b :=
  congrArg Subtype.val ((O.ι ≫ φ).isOpenEmbedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h)

/-- A small contraction of a threefold is an open immersion off a closed set `V ⊇ Ex(φ)` from
which no chain `a ⤳ b ⤳ c` of distinct points starts. -/
private theorem exists_closeds_of_isSmall {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z} (hφ : IsSmall k sZ sX φ)
    (hX : topologicalKrullDim X = 3) :
    ∃ V : Closeds X, exceptionalSet φ ⊆ V ∧
      (∀ a ∈ V, ∀ b c : X, a ⤳ b → b ⤳ c → a ≠ b → b ≠ c → False) ∧
      IsOpenImmersion ((show X.Opens from V.compl).ι ≫ φ) := by
  obtain ⟨V, W', hV, -, hle, hiso⟩ := hφ.exists_isIso
  rw [le_closedsCodimension_iff_le_coheight] at hV
  have hVc : IsOpenImmersion ((show X.Opens from V.compl).ι ≫ φ) := by
    rw [← Scheme.Hom.resLE_comp_ι φ hle]; infer_instance
  refine ⟨V, fun y hy => by_contra fun hyV => hy ⟨V.compl, hyV, hVc⟩,
    fun a ha _ _ => false_of_two_le_coheight_of_specializes sX hφ.isVariety_source hX (hV a ha),
    hVc⟩

/-- In a Noetherian space, let `V` be a closed set from which no chain `a ⤳ b ⤳ c` of distinct
points starts. Then only finitely many non-closed points lie in `V`: each is the generic point of
an irreducible component of `V`. -/
private theorem finite_inter_of_forall_exists_specializes {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] [T0Space X] {V F : Set X} (hV : IsClosed V)
    (hchain : ∀ a ∈ V, ∀ b c : X, a ⤳ b → b ⤳ c → a ≠ b → b ≠ c → False)
    (hF : ∀ y ∈ F, ∃ y', y ⤳ y' ∧ y ≠ y') : (F ∩ V).Finite := by
  obtain ⟨S, hSfin, hScl, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hV
  refine (hSfin.biUnion fun t _ => Set.Subsingleton.finite
    (s := {y | IsGenericPoint y t}) fun a ha b hb => ha.eq hb).subset ?_
  rintro y ⟨hyF, t, htS, hyt⟩
  have hg := (hSirr t htS).isGenericPoint_genericPoint_closure
  rw [(hScl t htS).closure_eq] at hg
  obtain ⟨y', hyy', hne⟩ := hF y hyF
  refine Set.mem_biUnion htS (by_contra fun hgy => ?_)
  exact hchain _ ⟨t, htS, hg.mem⟩ y y' (hg.specializes hyt) hyy' (fun h => hgy (h ▸ hg)) hne

/-- A contraction is a local isomorphism at every point whose fibre is finite. -/
private theorem notMem_exceptionalSet_of_finite_preimage {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z}
    (hφ : IsContraction k sZ sX φ) {x : X} (hfin : (φ ⁻¹' {φ x}).Finite) :
    x ∉ exceptionalSet φ := by
  have : IsProper φ := hφ.isProper
  obtain ⟨U, hzU, hfinU⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton φ (φ x) hfin
  obtain ⟨Va, hVa, hzVa, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := U.toScheme) (x := ⟨φ x, hzU⟩) (U := ⊤) trivial
  have hiso : IsIso ((φ ∣_ U).app Va) := by
    rw [morphismRestrict_app]
    exact IsIso.comp_isIso' (hφ.isIso_app _) (by
      rw [eqToHom_op, eqToHom_map]; exact CategoryTheory.instIsIsoEqToHom _)
  have : IsIso (φ ∣_ (U.ι ''ᵁ Va)) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict φ U Va)).mp ((isIso_morphismRestrict_iff_isIso_app _ hVa).mpr hiso)
  refine fun hx => hx ⟨φ ⁻¹ᵁ (U.ι ''ᵁ Va), ⟨⟨φ x, hzU⟩, hzVa, rfl⟩, ?_⟩
  rw [← morphismRestrict_ι]; infer_instance

/-- A small contraction of a threefold maps every point of its exceptional set to a closed
point. -/
private theorem isClosed_singleton_map_of_mem_exceptionalSet {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z}
    (hφ : IsSmall k sZ sX φ) (hX : topologicalKrullDim X = 3) {x : X}
    (hx : x ∈ exceptionalSet φ) : IsClosed ({φ x} : Set Z) := by
  have := hφ.isVariety_source.toLocallyOfFiniteType
  have := hφ.isVariety_source.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := ⟨⟩
  have : IsProper φ := hφ.isProper
  obtain ⟨V, -, hchain, hVc⟩ := exists_closeds_of_isSmall hφ hX
  by_contra hzc
  refine notMem_exceptionalSet_of_finite_preimage hφ.toIsContraction ?_ hx
  have hnc : ∀ y ∈ φ ⁻¹' {φ x}, ∃ y', y ⤳ y' ∧ y ≠ y' := by
    intro y (hy : φ y = φ x)
    by_contra! h
    have hy' : IsClosed ({y} : Set X) := closure_subset_iff_isClosed.mp fun t ht =>
      (h t (specializes_iff_mem_closure.mpr ht)).symm
    have := φ.isClosedMap _ hy'
    rw [Set.image_singleton, hy] at this
    exact hzc this
  rw [← Set.inter_union_diff (φ ⁻¹' {φ x}) V]
  exact (finite_inter_of_forall_exists_specializes V.isClosed hchain hnc).union
    (Set.Subsingleton.finite fun a ha b hb =>
      eq_of_isOpenImmersion hVc ha.2 hb.2 (ha.1.trans hb.1.symm))

/-- On a Jacobson scheme, a point `s` off the exceptional set of `φ` whose specializations all
lie in its fibre is closed: `φ` is injective near `s`, so `{s}` is locally closed. -/
private theorem isClosed_singleton_of_notMem_exceptionalSet {X Z : Scheme.{u}} [JacobsonSpace X]
    {φ : X ⟶ Z} {s : X} (hs : s ∉ exceptionalSet φ) (hfib : ∀ t, s ⤳ t → φ t = φ s) :
    IsClosed ({s} : Set X) := by
  obtain ⟨O, hsO, hO⟩ := exists_isOpenImmersion_of_notMem_exceptionalSet hs
  refine isClosed_singleton_of_isLocallyClosed_singleton
    ⟨O, closure {s}, O.isOpen, isClosed_closure, Set.ext fun t => ⟨?_, ?_⟩⟩
  · rintro rfl
    exact ⟨hsO, subset_closure rfl⟩
  · rintro ⟨htO, ht⟩
    exact eq_of_isOpenImmersion hO htO hsO (hfib t (specializes_iff_mem_closure.mpr ht))

/-- A set of dimension one has a point other than any given one. -/
private theorem exists_mem_ne_of_topologicalKrullDim_eq_one {X : Type*} [TopologicalSpace X]
    {W : Set X} (hW : topologicalKrullDim W = 1) (x : X) : ∃ c ∈ W, c ≠ x := by
  by_contra! h
  have : Subsingleton W := ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology W
  rw [hW] at h0
  exact absurd h0 (by decide)

/-- Let `φ : X ⟶ Z` be a small contraction (`MMP.Flips.IsSmall`) of a threefold `X`, and `W ⊆ X`
an irreducible closed subset of dimension one contained in the exceptional set
`MMP.Flips.exceptionalSet φ`. Then `W` is a flipping curve of `φ`
(`MMP.Flips.IsFlippingCurve`). -/
@[mmp "lem_fa4_curve_in_exceptional_set_is_flipping"]
public theorem isFlippingCurve_of_subset_exceptionalSet {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z}
    (hφ : IsSmall k sZ sX φ) (hX : topologicalKrullDim X = 3) {W : Set X}
    (hWirr : IsIrreducible W) (hWcl : IsClosed W) (hWdim : topologicalKrullDim W = 1)
    (hWex : W ⊆ exceptionalSet φ) :
    IsFlippingCurve k sX sZ φ W := by
  have := hφ.isVariety_source.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  set η := hWirr.genericPoint
  have hη : IsGenericPoint η W := hWcl.closure_eq ▸ hWirr.isGenericPoint_genericPoint_closure
  have hz := isClosed_singleton_map_of_mem_exceptionalSet hφ hX (hWex hη.mem)
  -- every specialization of `η` lies in the fibre of the closed point `φ η`
  have hfib : ∀ t, η ⤳ t → φ t = φ η := fun t ht => by
    have := (ht.map φ.continuous).mem_closure
    rwa [hz.closure_eq] at this
  refine ⟨hφ.isVariety_source, hφ.isVariety_target, hφ.comp_eq, hφ.isProper, φ η, hz,
    ⟨⟨hWirr, fun x hx => hfib x (hη.specializes hx)⟩, ?_⟩, by rw [hWdim]; exact zero_lt_one⟩
  rintro S ⟨hSirr, hSfib⟩ hWS
  have hs := hSirr.isGenericPoint_genericPoint_closure
  have hsη : hSirr.genericPoint ⤳ η := hs.specializes (subset_closure (hWS hη.mem))
  suffices hsη' : hSirr.genericPoint = η by
    rw [← hη.def, ← hsη', hs.def]
    exact subset_closure
  by_contra hne
  obtain ⟨V, hExV, hchain, -⟩ := exists_closeds_of_isSmall hφ hX
  by_cases hsEx : hSirr.genericPoint ∈ exceptionalSet φ
  · obtain ⟨c, hcW, hcη⟩ := exists_mem_ne_of_topologicalKrullDim_eq_one hWdim η
    exact hchain _ (hExV hsEx) η c hsη (hη.specializes hcW) hne hcη.symm
  · have hcl := isClosed_singleton_of_notMem_exceptionalSet hsEx fun t ht =>
      (closure_minimal hSfib (hz.preimage φ.continuous) (hs.specializes_iff_mem.mp ht)).trans
        (closure_minimal hSfib (hz.preimage φ.continuous) hs.mem).symm
    exact hne (hcl.closure_eq ▸ hsη.mem_closure : η ∈ ({_} : Set X)).symm

end MMP.Flips

end FlippingCurve

/-! ### Proper birational morphisms onto a normal variety -/

section BirationalIso

namespace MMP.Flips

/-- **Algebraic Hartogs.** On a normal locally Noetherian scheme, restriction of functions from
`U` to `U ∩ V` is bijective when the complement of `V` has codimension `≥ 2`. -/
private lemma bijective_map_inf_of_two_le_closedsCodimension (X : Scheme.{u})
    [IsLocallyNoetherian X] [IsNormal X] {V : X.Opens}
    (hV : 2 ≤ MMP.Mori.closedsCodimension V.compl) (U : X.Opens) :
    Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) := by
  refine MMP.Flips.bijective_presheaf_map_of_satisfiesS2
    (MMP.Flips.satisfiesS2_iff_forall_min_le_depth.mpr
      ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one X).mp inferInstance).1) _
    fun z hzU hz => ?_
  have hzV : z ∉ V := fun h => hz ⟨hzU, h⟩
  have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV z hzV
  rw [ringKrullDim_stalk_eq_coheight]
  exact WithBot.coe_le_coe.mpr h2

/-- If `g` restricts to an isomorphism over `W`, then `𝒪_X(W) ⟶ 𝒪_Y(g⁻¹ W)` is an
isomorphism. -/
private lemma isIso_app_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : Y ⟶ X) {W : X.Opens}
    (hW : IsIso (g ∣_ W)) : IsIso (g.app W) := by
  have h := morphismRestrict_appTop g W
  have : IsIso (g.app (W.ι ''ᵁ ⊤) ≫
      Y.presheaf.map (eqToHom (image_morphismRestrict_preimage g W ⊤)).op) := by
    rw [← h]; exact Scheme.Hom.instIsIsoCommRingCatApp _ ⊤
  have := IsIso.of_isIso_comp_right (g.app (W.ι ''ᵁ ⊤))
    (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage g W ⊤)).op)
  rwa [Scheme.Opens.ι_image_top] at this

/-- `g_* 𝒪_Y = 𝒪_X` for a dominant morphism of integral schemes onto a normal locally
Noetherian scheme which is an isomorphism over an open with complement of codimension `≥ 2`. -/
private lemma isIso_app_of_isBiregular {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsNormal X] (g : Y ⟶ X) [IsDominant g] {V : X.Opens}
    (hV : 2 ≤ MMP.Mori.closedsCodimension V.compl) (hg : MMP.Mori.IsBiregular g V)
    (U : X.Opens) : IsIso (g.app U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  obtain hU | hU := (U : Set X).eq_empty_or_nonempty
  · obtain rfl : U = ⊥ := Opens.coe_eq_empty.mp hU
    have : Subsingleton Γ(Y, g ⁻¹ᵁ (⊥ : X.Opens)) := by
      rw [Scheme.Hom.preimage_bot]; infer_instance
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  have hVne : (V : Set X).Nonempty := by
    simpa using MMP.Flips.nonempty_compl_of_two_le_closedsCodimension V.compl hV
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen hU hVne
  have hW : MMP.Mori.IsBiregular g (U ⊓ V) :=
    MMP.Mori.isBiregular_iff_le_biregularLocus.mpr
      (inf_le_right.trans (MMP.Mori.le_biregularLocus hg))
  have hiso : IsIso (g.app (U ⊓ V)) := isIso_app_of_isIso_morphismRestrict g hW
  obtain ⟨y, hy⟩ := g.denseRange.exists_mem_open (U ⊓ V).isOpen ⟨x, hxU, hxV⟩
  have : Nonempty (g ⁻¹ᵁ (U ⊓ V)) := ⟨⟨y, hy⟩⟩
  have hle : g ⁻¹ᵁ (U ⊓ V) ≤ g ⁻¹ᵁ U := g.preimage_mono inf_le_left
  have hnat : g.app U ≫ Y.presheaf.map (homOfLE hle).op =
      X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op ≫ g.app (U ⊓ V) :=
    (g.naturality _).symm
  have hnat' (a : Γ(X, U)) : Y.presheaf.map (homOfLE hle).op (g.app U a) =
      g.app (U ⊓ V) (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a) := by
    simpa using congr($hnat a)
  have hresX := bijective_map_inf_of_two_le_closedsCodimension X hV U
  have hresY : Function.Injective (Y.presheaf.map (homOfLE hle).op) :=
    map_injective_of_isIntegral Y _
  have hgW := ConcreteCategory.bijective_of_isIso (g.app (U ⊓ V))
  refine ⟨fun a b hab => hresX.1 (hgW.1 ?_), fun t => ?_⟩
  · rw [← hnat', ← hnat', hab]
  · obtain ⟨c, hc⟩ := hgW.2 (Y.presheaf.map (homOfLE hle).op t)
    obtain ⟨a, rfl⟩ := hresX.2 c
    exact ⟨a, hresY (by rw [hnat', hc])⟩

/-- A morphism `f` whose rational map is that of a partial isomorphism `e` agrees with `e` on
`e.source`. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A morphism `g : Y ⟶ X` of reduced separated schemes which agrees with a partial isomorphism
`e` on `e.source` is an isomorphism over the domain of definition of the rational map `e⁻¹`. -/
private lemma isBiregular_domain_symm {X Y : Scheme.{u}} [IsReduced X] [IsReduced Y]
    [X.IsSeparated] [Y.IsSeparated] (g : Y ⟶ X) (e : Y.PartialIso X)
    (key : e.iso.hom ≫ e.target.ι = e.source.ι ≫ g) :
    MMP.Mori.IsBiregular g e.symm.toRationalMap.domain := by
  set V := e.symm.toRationalMap.domain
  let s : V.toScheme ⟶ Y := e.symm.toRationalMap.toPartialMap.hom
  have hTV : e.target ≤ V := e.symm.toPartialMap.le_domain_toRationalMap
  have hs : X.homOfLE hTV ≫ s = e.iso.inv ≫ e.source.ι :=
    e.symm.toPartialMap.toPartialMap_toRationalMap_restrict
  have hsg : s ≫ g = V.ι := by
    have : IsDominant (X.homOfLE hTV) :=
      AlgebraicGeometry.Opens.isDominant_homOfLE e.dense_target _
    refine ext_of_isDominant (X.homOfLE hTV) ?_
    rw [reassoc_of% hs, ← key, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι]
  have hrange : Set.range s ⊆ Set.range (g ⁻¹ᵁ V).ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    change g (s v) ∈ V
    rw [← Scheme.Hom.comp_apply, hsg]
    exact v.2
  let s' : V.toScheme ⟶ (g ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift (g ⁻¹ᵁ V).ι s hrange
  have hs' : s' ≫ (g ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ _
  have hSV : e.source ≤ g ⁻¹ᵁ V := by
    intro y hy
    obtain ⟨y', rfl⟩ : y ∈ Set.range e.source.ι := by rwa [Scheme.Opens.range_ι]
    change g (e.source.ι y') ∈ V
    rw [← Scheme.Hom.comp_apply, ← key, Scheme.Hom.comp_apply]
    exact hTV (e.iso.hom y').2
  refine ⟨⟨s', ?_, ?_⟩⟩
  · rw [← cancel_mono (g ⁻¹ᵁ V).ι, Category.assoc, hs', Category.id_comp]
    have : IsDominant (Y.homOfLE hSV) :=
      AlgebraicGeometry.Opens.isDominant_homOfLE e.dense_source _
    refine ext_of_isDominant (Y.homOfLE hSV) ?_
    have hj : Y.homOfLE hSV ≫ (g ∣_ V) = e.iso.hom ≫ X.homOfLE hTV := by
      rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
        Category.assoc, Scheme.homOfLE_ι, key]
    rw [reassoc_of% hj, hs, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hs', hsg,
      Category.id_comp]

/-- Let `g : Y ⟶ X` be a proper birational morphism of `k`-varieties with `X` normal. Then
`g_* 𝒪_Y = 𝒪_X` (each `𝒪_X(U) ⟶ 𝒪_Y(g⁻¹ U)` is an isomorphism), and there is an open `V ⊆ X`
with `codim_X (X ∖ V) ≥ 2` over which `g` is an isomorphism `g⁻¹(V) ⟶ V`. -/
@[mmp "lem_fa6_birational_iso_over_codim_two"]
public theorem isIso_app_and_exists_isBiregular_of_isBirationalMorphism {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : Mori.IsNormalVariety k sX) (g : Y ⟶ X)
    (hY : Mori.IsVariety k (g ≫ sX)) [IsProper g] (hg : Mori.IsBirationalMorphism g) :
    (∀ U : X.Opens, IsIso (g.app U)) ∧
      ∃ V : X.Opens, 2 ≤ Mori.closedsCodimension V.compl ∧ Mori.IsBiregular g V := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsSeparated sX := hX.1.toIsSeparated
  have : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sX]; infer_instance⟩
  have : IsSeparated (g ≫ sX) := hY.toIsSeparated
  have : Y.IsSeparated := ⟨by rw [← Limits.terminal.comp_from (g ≫ sX)]; infer_instance⟩
  have : IsDominant g := hg.isDominant
  have hcodim := MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hX g hY hg
  obtain ⟨e, he, hinv⟩ := hg.isInverse_inverse
  rw [← hinv] at hcodim
  have hbir := isBiregular_domain_symm g e (source_ι_comp_eq_of_toRationalMap_eq g e he).symm
  exact ⟨isIso_app_of_isBiregular g hcodim hbir, _, hcodim, hbir⟩

end MMP.Flips

end BirationalIso

/-! ### A criterion for smallness -/

section Small

namespace MMP.Flips

/-- In an irreducible scheme, a point of coheight zero lies in every nonempty open subset. -/
private lemma mem_of_coheight_eq_zero {Y : Scheme.{u}} [IrreducibleSpace Y] {U : Y.Opens}
    (hU : (U : Set Y).Nonempty) {y : Y} (hy : Order.coheight y = 0) : y ∈ U := by
  have hη := genericPoint_spec Y
  have h : y ⤳ genericPoint Y := Scheme.le_iff_specializes.mp <| Order.coheight_eq_zero.mp hy <|
    Scheme.le_iff_specializes.mpr (hη.specializes (Set.mem_univ _))
  exact h.mem_open U.isOpen ((hη.mem_open_set_iff U.isOpen).mpr (by simpa using hU))

/-- The heart of the argument: if `g` maps every prime divisor of `Y` onto a prime divisor of `X`,
`codim (X ∖ V) ≥ 2` and `g⁻¹(V)` is nonempty, then every point of `Y ∖ g⁻¹(V)` has coheight
`≥ 2`. A point of coheight one is the generic point of a prime divisor `D`, and the generic point
of the prime divisor `g(D)` would then be a point of `X ∖ V` of coheight one. -/
private lemma two_le_coheight_of_notMem_preimage {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (g : Y ⟶ X) {V : X.Opens} (hV : 2 ≤ MMP.Mori.closedsCodimension V.compl)
    (hne : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty)
    (hD : ∀ D : MMP.Mori.PrimeDivisor Y, ∃ Q : MMP.Mori.PrimeDivisor X, g '' D.support = Q.support)
    {y : Y} (hy : y ∉ g ⁻¹ᵁ V) : 2 ≤ Order.coheight y := by
  by_contra hlt
  rcases ENat.le_one_iff_eq_zero_or_eq_one.mp (ENat.lt_two_iff.mp (not_le.mp hlt)) with h0 | h1
  · exact hy (mem_of_coheight_eq_zero hne h0)
  obtain ⟨Q, hQ⟩ := hD (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1)
  have hQmem : Q.genericPoint ∈ Q.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  rw [← hQ, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] at hQmem
  obtain ⟨z, hz, hzQ⟩ := hQmem
  have hzV : z ∉ g ⁻¹ᵁ V :=
    closure_minimal (Set.singleton_subset_iff.mpr hy) (g ⁻¹ᵁ V).compl.isClosed hz
  have hQV : Q.genericPoint ∈ (V.compl : Set X) := by rw [← hzQ]; exact hzV
  have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV _ hQV
  simp [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this

/-- **Criterion for smallness.** Let `g : Y ⟶ X` be a proper birational morphism of normal
`k`-varieties, such that the image of every prime divisor of `Y` is a prime divisor of `X`.
Then `g` is small. -/
@[mmp "lem_fa6_no_exceptional_divisor_small"]
public theorem isSmall_of_forall_primeDivisor_image {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : Mori.IsNormalVariety k sX) (g : Y ⟶ X)
    (hY : Mori.IsNormalVariety k (g ≫ sX)) [IsProper g] (hg : Mori.IsBirationalMorphism g)
    (hD : ∀ D : Mori.PrimeDivisor Y, ∃ Q : Mori.PrimeDivisor X, g '' D.support = Q.support) :
    IsSmall k sX (g ≫ sX) g := by
  obtain ⟨hiso_app, V, hV, hiso⟩ :=
    MMP.Flips.isIso_app_and_exists_isBiregular_of_isBirationalMorphism hX g hY.1 hg
  have := hX.1
  have := hY.1
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsIso (g ∣_ V) := hiso
  obtain ⟨x, hx⟩ : (V : Set X).Nonempty := by
    simpa using MMP.Flips.nonempty_compl_of_two_le_closedsCodimension V.compl hV
  have hcodim : 2 ≤ MMP.Mori.closedsCodimension (g ⁻¹ᵁ V).compl :=
    MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun _ hy =>
      two_le_coheight_of_notMem_preimage g hV ⟨_, ((inv (g ∣_ V)) ⟨x, hx⟩).2⟩ hD hy
  have hcc : (g ⁻¹ᵁ V).compl.compl = g ⁻¹ᵁ V := Opens.ext (by simp)
  have hcc' : V.compl.compl = V := Opens.ext (by simp)
  refine ⟨⟨⟨hX.1, hY.1, rfl, inferInstance, hiso_app⟩,
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg).symm⟩,
    (g ⁻¹ᵁ V).compl, V.compl, hcodim, hV, by rw [hcc, hcc'], ?_⟩
  refine (Scheme.Hom.resLE_congr g le_rfl hcc'.symm hcc.symm
    (MorphismProperty.isomorphisms Scheme)).mp ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact this

end MMP.Flips

end Small

/-! ### Exceptional divisors of a model over a procedure datum lie in `Supp h'^*H'` -/

section ProcedureDatum

open Limits MMP.Mori

namespace MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Chains of irreducible closed subsets lift along a closed continuous surjection. -/
private theorem exists_ltSeries_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober Y] {f : X → Y} (hc : Continuous f) (hcl : IsClosedMap f)
    (hs : Function.Surjective f) :
    ∀ (n : ℕ) (p : LTSeries (IrreducibleCloseds Y)), p.length = n →
      ∃ q : LTSeries (IrreducibleCloseds X), q.length = n ∧
        f '' (q.head : Set X) = (p.head : Set Y) := by
  -- an irreducible closed subset contained in `f(S)` is the image of one contained in `S`
  have key : ∀ (T : IrreducibleCloseds Y) (S : Set X), IsClosed S → (T : Set Y) ⊆ f '' S →
      ∃ S' : IrreducibleCloseds X, (S' : Set X) ⊆ S ∧ f '' (S' : Set X) = T := by
    intro T S hS hT
    have hgen := T.isIrreducible.isGenericPoint_genericPoint T.isClosed
    obtain ⟨y, hyS, hy⟩ := hT hgen.mem
    refine ⟨⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩,
      closure_minimal (Set.singleton_subset_iff.mpr hyS) hS, ?_⟩
    change f '' closure {y} = T
    rw [← hcl.closure_image_eq_of_continuous hc, Set.image_singleton, hy, hgen.def]
  intro n
  induction n with
  | zero =>
    intro p _
    obtain ⟨S', -, hS'⟩ := key p.head Set.univ isClosed_univ
      (by rw [Set.image_univ, hs.range_eq]; exact Set.subset_univ _)
    exact ⟨RelSeries.singleton _ S', rfl, hS'⟩
  | succ n ih =>
    intro p hp
    have hp0 : p.length ≠ 0 := by omega
    obtain ⟨q, hq, hqh⟩ := ih (p.tail hp0) (by rw [RelSeries.tail_length]; omega)
    have hlt : p.head < (p.tail hp0).head := by
      rw [RelSeries.head_tail]
      apply p.strictMono
      simp only [Fin.lt_def, Fin.val_zero, Fin.val_one']
      rw [hp, Nat.one_mod_eq_one.mpr (by omega)]
      omega
    obtain ⟨S', hS'q, hS'⟩ := key p.head q.head q.head.isClosed (by
      rw [hqh]; exact hlt.le)
    have hS'lt : S' < q.head := by
      refine lt_of_le_of_ne hS'q fun heq => hlt.ne ?_
      apply SetLike.coe_injective
      rw [← hS', ← hqh, heq]
    exact ⟨q.cons S' hS'lt, by rw [RelSeries.cons_length, hq], by
      rw [RelSeries.head_cons, hS']⟩

/-- **Dimension does not drop along a closed continuous surjection.** -/
private theorem topologicalKrullDim_le_of_isClosedMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober Y] {f : X → Y} (hc : Continuous f) (hcl : IsClosedMap f)
    (hs : Function.Surjective f) : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  refine iSup_le fun p => ?_
  obtain ⟨q, hq, -⟩ := exists_ltSeries_lift hc hcl hs p.length p rfl
  rw [← hq]
  exact Order.LTSeries.length_le_krullDim q

/-- `dim {z}⁻ + codim z ≤ dim Z` for a point `z` of a scheme. -/
private theorem topologicalKrullDim_closure_add_coheight_le {Z : Scheme.{u}} (z : Z) :
    topologicalKrullDim (closure {z} : Set Z) + Order.coheight z ≤ topologicalKrullDim Z := by
  let T : IrreducibleCloseds Z := IrreducibleCloseds.closureSingleton z
  have hT : IsClosed (closure {z} : Set Z) := isClosed_closure
  let φ : IrreducibleCloseds (closure {z} : Set Z) → Set.Iic T := fun W =>
    ⟨⟨Subtype.val '' (W : Set (closure {z} : Set Z)),
      W.isIrreducible.image _ continuous_subtype_val.continuousOn,
      hT.isClosedEmbedding_subtypeVal.isClosedMap _ W.isClosed⟩,
      Subtype.coe_image_subset _ _⟩
  have hφ : StrictMono φ := by
    intro W₁ W₂ hlt
    have hlt' : (W₁ : Set (closure {z} : Set Z)) < W₂ := hlt
    exact Subtype.val_injective.image_strictMono hlt'
  have h1 : topologicalKrullDim (closure {z} : Set Z) ≤ Order.height T := by
    rw [Order.height_eq_krullDim_Iic]
    exact Order.krullDim_le_of_strictMono φ hφ
  have h2 : Order.coheight z = Order.coheight T := by
    rw [show T = (irreducibleSetEquivPoints (α := Z)).symm z from rfl, Order.coheight_orderIso]
  rw [h2]
  calc topologicalKrullDim (closure {z} : Set Z) + (Order.coheight T : WithBot ℕ∞)
      ≤ Order.height T + Order.coheight T := by gcongr
    _ ≤ topologicalKrullDim Z := Order.height_add_coheight_le_krullDim T

private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- If `h ∣_ U` is an isomorphism, `h` is injective on `h⁻¹(U)`. -/
private theorem injOn_preimage_of_isIso_morphismRestrict {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    (U : Z.Opens) [IsIso (h ∣_ U)] : Set.InjOn h (h ⁻¹ᵁ U) := by
  intro a ha b hb hab
  rw [← morphismRestrict_base_coe h U ⟨a, ha⟩, ← morphismRestrict_base_coe h U ⟨b, hb⟩] at hab
  exact congrArg Subtype.val
    ((h ∣_ U).isOpenEmbedding.injective (U.ι.isOpenEmbedding.injective hab))

/-- If `h ∣_ U` is an isomorphism, `h` preserves the codimension of points of `h⁻¹(U)`. -/
private theorem coheight_apply_of_isIso_morphismRestrict {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    (U : Z.Opens) [IsIso (h ∣_ U)] {y : Y} (hy : y ∈ h ⁻¹ᵁ U) :
    Order.coheight (h y) = Order.coheight y := by
  let v : (h ⁻¹ᵁ U).toScheme := ⟨y, hy⟩
  rw [show h y = U.ι ((h ∣_ U) v) from (morphismRestrict_base_coe h U v).symm,
    coheight_eq_of_isOpenImmersion U.ι, coheight_eq_of_isOpenImmersion (h ∣_ U)]
  exact (coheight_eq_of_isOpenImmersion (h ⁻¹ᵁ U).ι).symm

private theorem not_add_two_le_add_one {a : WithBot ℕ∞} (ha : a + 1 ≠ ⊤) (h0 : 0 ≤ a + 1) :
    ¬ a + 2 ≤ a + 1 := by
  intro h
  induction a using WithBot.recBotCoe with
  | bot => simp at h0
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact ha rfl
    | coe n =>
      rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl,
        show (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_add,
        ← WithBot.coe_add, WithBot.coe_le_coe] at h
      have : n + 2 ≤ n + 1 := by exact_mod_cast h
      omega

/-- **A prime divisor over the isomorphism locus is not contracted.** Let `h : Y ⟶ Z` be a
universally closed surjection from an integral scheme of finite type over `k`, which is an
isomorphism over `U`. A prime divisor `E` of `Y` whose generic point lies over `U` satisfies
`dim Z < dim h(E) + 2`. -/
private theorem not_add_two_le_of_genericPoint_mem {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} (h : Y ⟶ Z) [IsIntegral Y] [LocallyOfFiniteType (h ≫ sZ)]
    [UniversallyClosed h] [Surjective h] (U : Z.Opens) [IsIso (h ∣_ U)]
    (E : MMP.Mori.PrimeDivisor Y) (hE : E.genericPoint ∈ h ⁻¹ᵁ U) :
    ¬ topologicalKrullDim (h.base '' (E.support : Set Y)) + 2 ≤ topologicalKrullDim Z := by
  intro hle
  set V := h ⁻¹ᵁ U
  let v : V.toScheme := ⟨E.genericPoint, hE⟩
  letI : Y.Over (Spec (.of k)) := ⟨h ≫ sZ⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType (h ≫ sZ))
  have : Nonempty V.toScheme := ⟨v⟩
  have : QuasiSober (closure {v} : Set V.toScheme) :=
    isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  have : Nonempty (IrreducibleCloseds Y) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
  have hcoV : Order.coheight v = 1 := by
    rw [← coheight_eq_of_isOpenImmersion V.ι]; exact E.coheight_genericPoint
  have hYa : topologicalKrullDim (closure {v} : Set V.toScheme) + 1 = topologicalKrullDim Y := by
    have hVY : topologicalKrullDim V = topologicalKrullDim Y :=
      (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen k _ (_ ↘ Spec (.of k)) _
          (TopologicalSpace.Opens.isOpen V) ⟨_, hE⟩).symm
    rw [← hVY, ← MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (V.ι ≫ h ≫ sZ) v,
      hcoV]
    rfl
  have hmem : ∀ x : (closure {v} : Set V.toScheme),
      h (V.ι x.1) ∈ h.base '' (E.support : Set Y) := fun x => by
    refine ⟨V.ι x.1, ?_, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact map_mem_closure V.ι.base.hom.continuous x.2 (t := {E.genericPoint})
      (by rintro _ rfl; rfl)
  have hdim : topologicalKrullDim (closure {v} : Set V.toScheme) ≤
      topologicalKrullDim (h.base '' (E.support : Set Y)) :=
    topologicalKrullDim_le_of_specializes_imp_eq
      (f := fun x => (⟨h (V.ι x.1), hmem x⟩ : h.base '' (E.support : Set Y)))
      (by fun_prop) fun a b _ hab => Subtype.ext (V.ι.isOpenEmbedding.injective
        (injOn_preimage_of_isIso_morphismRestrict h U a.1.2 b.1.2 (congrArg Subtype.val hab)))
  refine not_add_two_le_add_one
    (by
      rw [hYa]
      exact (Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints).trans_ne
        (MMP.krullDim_lt_top_of_isIntegral k Y).ne)
    (by rw [hYa]; exact Order.krullDim_nonneg) ?_
  calc _ ≤ topologicalKrullDim (h.base '' (E.support : Set Y)) + 2 := by gcongr
    _ ≤ topologicalKrullDim Z := hle
    _ ≤ topologicalKrullDim Y :=
      topologicalKrullDim_le_of_isClosedMap h.base.hom.continuous h.isClosedMap h.surjective
    _ = _ := hYa.symm

variable {k : Type u} [Field k] {X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
  [IsLocallyNoetherian Z] [IsNormal Z]

/-- If the strict transform of `P'` under the inverse of the birational morphism `h` is `E`, then
`h` maps the generic point of `E` to that of `P'`. -/
private theorem apply_genericPoint_eq_of_transformPrimeDivisor_inverse {Y : Scheme.{u}}
    [IsIntegral Y] [IsIntegral Z] [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {h : Y ⟶ Z} (hbir : IsBirationalMorphism h) {P' : Mori.PrimeDivisor Z} {E : Mori.PrimeDivisor Y}
    (hPE : Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hbir) P' =
      some E) :
    h E.genericPoint = P'.genericPoint := by
  obtain ⟨e, he, he'⟩ := hbir.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hPE).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some hPE g' hg' hP]
  exact apply_hom_eq_of_isInverse h e he g' (hg'.trans he'.symm) hP

/-- If the proper birational morphism `h` maps the generic point of `E` to that of `P'`, then
the strict transform of `P'` under the inverse of `h` is `E`. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_apply_genericPoint_eq {Y : Scheme.{u}}
    [IsIntegral Y] [IsIntegral Z] [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {h : Y ⟶ Z} [IsProper h] [IsDominant h] (hbir : IsBirationalMorphism h)
    {P' : Mori.PrimeDivisor Z} {E : Mori.PrimeDivisor Y}
    (hPE : h E.genericPoint = P'.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hbir) P' =
      some E := by
  have hbij := hbir.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hbir.isInverse_inverse
  have hover : (Mori.RationalMap.IsBirational.inverse hbir).compHom h =
      Scheme.Hom.toRationalMap (𝟙 Z) := by
    rw [← he']
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ⟨e.target, e.dense_target, le_rfl, le_top, ?_⟩
    change Z.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ h =
      Z.homOfLE _ ≫ Z.topIso.hom ≫ 𝟙 Z
    rw [Category.assoc, source_ι_comp_eq_of_toRationalMap_eq h e he, Iso.inv_hom_id_assoc]
    simp
  obtain ⟨g', hP, hg'⟩ := Scheme.RationalMap.mem_domain.mp <|
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 Z) h _ hover
      (by rw [P'.coheight_genericPoint])
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse h e he g' (hg'.trans he'.symm) hP
  have := P'.isDiscreteValuationRing_localRing
  have : ValuationRing (Z.presheaf.stalk (h E.genericPoint)) := by
    rw [hPE]
    infer_instance
  have : ValuationRing (Z.presheaf.stalk (h (g'.hom ⟨P'.genericPoint, hP⟩))) := by
    rw [hy]
    infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing h hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing h hbij (g'.hom ⟨P'.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap h hbij (hy.trans hPE.symm)

/-- Over a proper birational morphism `h` which is an isomorphism over `Z ∖ Supp H'`, a prime
divisor `E` of `Y` either maps to a point of codimension at least two, where the strict transform
of `H'` vanishes, or the pullback of `H'` and its strict transform agree along `E`. -/
private theorem coheight_two_le_or_coeff_eq_of_isPullback {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y] [IsIntegral Z]
    [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {h : Y ⟶ Z} [IsProper h]
    [IsDominant h] (hbir : IsBirationalMorphism h) {H' : Divisor Z} (hC : H'.IsCartier)
    [IsIso (h ∣_ H'.supp.compl)]
    {hB : ∀ W : irreducibleComponents Y, h (componentGenericPoint Y W) ∉ H'.supp}
    {H : Divisor Y} (hH : H'.IsPullback h hB H) (E : Mori.PrimeDivisor Y) :
    (2 ≤ Order.coheight (h E.genericPoint) ∧ birationalInverseTransform h hbir H' E = 0) ∨
      H.coeff E = (birationalInverseTransform h hbir H').coeff E := by
  have hbij := hbir.functionFieldMap_bijective
  by_cases h2 : 2 ≤ Order.coheight (h E.genericPoint)
  · refine Or.inl ⟨h2, mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P' hP' => ?_) H'⟩
    rw [apply_genericPoint_eq_of_transformPrimeDivisor_inverse hbir hP',
      P'.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  right
  rcases ENat.le_one_iff_eq_zero_or_eq_one.mp (ENat.lt_two_iff.mp (not_le.mp h2)) with h0 | h1
  · exfalso
    have hsp : genericPoint Z ⤳ h E.genericPoint := (genericPoint_spec Z).specializes trivial
    have hx : h E.genericPoint = genericPoint Z :=
      (show h E.genericPoint ⤳ genericPoint Z from
        (Order.coheight_eq_zero.1 h0) hsp).antisymm hsp |>.eq
    have hmem : E.genericPoint ∈ h ⁻¹ᵁ H'.supp.compl := by
      change h E.genericPoint ∈ H'.supp.compl
      rw [hx]
      let W : irreducibleComponents Y :=
        ⟨irreducibleComponent (genericPoint Y), irreducibleComponent_mem_irreducibleComponents _⟩
      exact ((genericPoint_spec Z).mem_open_set_iff H'.supp.compl.isOpen).mpr ⟨_, trivial, hB W⟩
    rw [coheight_apply_of_isIso_morphismRestrict h _ hmem, E.coheight_genericPoint] at h0
    exact absurd h0 (by decide)
  · let P' : Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
    have heq : h E.genericPoint = P'.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm
    have hTE : birationalInverseTransform h hbir H' E = H' P' :=
      MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
        (transformPrimeDivisor_inverse_eq_some_of_apply_genericPoint_eq hbir heq)
        (fun P'' hP'' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          ((apply_genericPoint_eq_of_transformPrimeDivisor_inverse hbir hP'').symm.trans heq))
        H'
    have := P'.isDiscreteValuationRing_localRing
    have : ValuationRing (Z.presheaf.stalk (h E.genericPoint)) := by
      rw [heq]
      infer_instance
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing h hbij E.genericPoint
    rw [MMP.Positivity.coeff_eq_of_isPullback E P' heq hC hH]
    exact hTE.symm

/-- Let `P` be a procedure datum for `(X, D, f)` with divisor `H'` and `h' : Y' ⟶ Z` a proper
birational morphism from a normal variety which is an isomorphism over `Z ∖ Supp H'`, and let
`H = h'^*H'`. Then every `h'`-exceptional prime divisor of `Y'` and `h'⁻¹(f(Ex(f)))` lie in
`Supp H`, and `H = h'⁻¹_*H' + A` for an effective divisor `A` whose components are
`h'`-exceptional. -/
@[mmp "lem_fa18_procedure_log_resolution_exceptional_in_support"]
public theorem ProcedureDatum.exceptional_subset_supp_pullback {D : RDivisor X} {f : X ⟶ Z}
    (P : ProcedureDatum k sZ D f) {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    {h : Y ⟶ Z} (hY : Mori.IsNormalVariety k (h ≫ sZ)) (hbir : IsBirationalMorphism h)
    [IsProper h] [IsIso (h ∣_ P.H'.supp.compl)]
    {hB : ∀ W : irreducibleComponents Y, h (componentGenericPoint Y W) ∉ P.H'.supp}
    {H : Divisor Y} (hH : P.H'.IsPullback h hB H) :
    (∀ E : Mori.PrimeDivisor Y, IsExceptionalPrimeDivisor sZ h E →
        (E.support : Set Y) ⊆ (H.supp : Set Y)) ∧
      h.base ⁻¹' (f.base '' exceptionalSet f) ⊆ (H.supp : Set Y) ∧
      ∃ A : Divisor Y, A.IsEffective ∧
        (∀ E : Mori.PrimeDivisor Y, A.coeff E ≠ 0 → IsExceptionalPrimeDivisor sZ h E) ∧
        H = birationalInverseTransform h hbir P.H' + A := by
  classical
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsSeparated (h ≫ sZ) := hY.1.toIsSeparated
  have : LocallyOfFiniteType (h ≫ sZ) := hY.1.toLocallyOfFiniteType
  have : IsDominant h := hbir.isDominant
  have : IsSeparated sZ := by
    let f : Over.mk (h ≫ sZ) ⟶ Over.mk sZ := Over.homMk h rfl
    have : Surjective f.left := inferInstanceAs (Surjective h)
    have : UniversallyClosed f.left := inferInstanceAs (UniversallyClosed h)
    have : IsSeparated (Over.mk (h ≫ sZ)).hom := ‹IsSeparated (h ≫ sZ)›
    exact isSeparated_of_surjective_universallyClosed f
  have : IrreducibleSpace Z := h.surjective.irreducibleSpace h.continuous
  have : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  have : IsSeparated (Z ↘ ⊤_ Scheme) := by
    rw [show (Z ↘ ⊤_ Scheme) = sZ ≫ (Spec (.of k) ↘ ⊤_ Scheme) from terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = (h ≫ sZ) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      terminal.hom_ext _ _]
    infer_instance
  have hHe : DivisorWithCoeffs.IsEffective P.H' := fun E => by
    rcases P.isReduced_H' E with h' | h' <;> simp [h']
  have hsupp := supp_eq_preimage_supp_of_isPullback P.isCartier_H' hHe hH
  set U : Z.Opens := P.H'.supp.compl
  have himage : ∀ E : MMP.Mori.PrimeDivisor Y,
      h.base '' (E.support : Set Y) = closure {h E.genericPoint} := fun E => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← h.isClosedMap.closure_image_eq_of_continuous h.base.hom.continuous, Set.image_singleton]
  refine ⟨fun E hE => ?_, ?_, ?_⟩
  · obtain ⟨_, _, _, hE⟩ := hE
    rw [hsupp]
    by_contra hsub
    obtain ⟨y, hyE, hyU⟩ := Set.not_subset.mp hsub
    exact not_add_two_le_of_genericPoint_mem (sZ := sZ) h U E
      ((E.genericPoint_mem_iff (h ⁻¹ᵁ U)).mpr ⟨y, hyE, hyU⟩) hE
  · rw [hsupp]
    exact Set.preimage_mono P.image_exceptionalSet_subset
  · set T := birationalInverseTransform h hbir P.H'
    have key := coheight_two_le_or_coeff_eq_of_isPullback hbir P.isCartier_H' hH
    refine ⟨H - T, fun E => ?_, fun E hE => ?_, (add_sub_cancel _ _).symm⟩
    · rcases key E with ⟨-, h0⟩ | h0
      · change 0 ≤ H E - T E
        rw [h0, sub_zero]
        exact MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) P.isCartier_H'
          (fun P' _ => hHe P') hH E ((E.genericPoint_mem_iff (h ⁻¹ᵁ ⊤)).mp trivial)
      · exact (sub_eq_zero.mpr h0).ge
    · rcases key E with ⟨h2, -⟩ | h0
      · refine ⟨hY, hbir, inferInstance, ?_⟩
        change topologicalKrullDim (h.base '' (E.support : Set Y)) + 2 ≤ topologicalKrullDim Z
        rw [himage]
        calc topologicalKrullDim (closure {h E.genericPoint} : Set Z) + 2
            ≤ topologicalKrullDim (closure {h E.genericPoint} : Set Z) +
                Order.coheight (h E.genericPoint) := by
              gcongr
              exact WithBot.coe_le_coe.mpr h2
          _ ≤ topologicalKrullDim Z := topologicalKrullDim_closure_add_coheight_le _
      · exact absurd (sub_eq_zero.mpr h0) hE

end MMP.Flips

end ProcedureDatum
