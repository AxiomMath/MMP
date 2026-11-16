module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.Singularities.LogResolution.FloorPushforward
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Threefold.MoriFibration.TwoFloorResidues
import MMP.AlgebraicGeometry.MMP.Fourfold.TwoFloorFibrationResidue
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Admissible floor sections descend through a two-floor Mori curve fibration

Let `r : Y ⟶ V` be a Mori fibre space from a `ℚ`-factorial projective threefold onto a normal
projective surface, with `-(K_Y + Γ)` `r`-ample for an effective klt boundary `Γ`. Let `B` be an
effective lc boundary with `D = K_Y + B` numerically trivial over `V`, such that
`(Y, B - ε⌊B⌋)` is klt for some `ε > 0`, and such that the horizontal part of the reduced floor
`⌊B⌋` has degree two over `V`. For a sufficiently divisible even `m`, `mD = r^*M` for an
invertible sheaf `M` on `V`. A section `s` of `mD` on the reduced floor `⌊B⌋`, whose pull-back to
a crepant dlt model `(Y', B')` of `(Y, B)` has admissible residue restrictions on the normal
floor components of `B'`, is the restriction of a unique global section of `mD`, that is, of the
pull-back `r^*t` of a section `t` of `M`. If such floor sections generate `mD|_{⌊B⌋}` at every
point of the floor, their extensions generate `mD` on `r⁻¹(U)` for a neighbourhood `U` of every
point of `V`; so the descended sections generate `M` on `V`, and their pull-backs generate `mD`
on `Y`.

On a pair of horizontal floor branches of degree one over `V`, admissibility together with the
crepant residue identification of the two branches gives one rational section over `k(V)`; on a
single branch of degree two it gives a section invariant under the crepant deck involution. The
section is regular on the normal surface `V` by Hartogs, and agreement on the vertical floor
components follows from the detection of pulled-back sections on a dominating horizontal curve.

## Main results

* `MMP.Fourfold.IsMoriFibreSpace.existsUnique_isPoincareResidue_of_mem_admissibleSections`.

## Implementation notes

* The floor components are indexed by the prime divisors `P` of `Y` with `coeff_P B = 1`, each
  given as an integral closed subscheme `j P : F P ⟶ Y`; `F P` need not be normal. A section of
  `mD` on the reduced floor is recorded by its family of restrictions `s P`, a rational
  `m`-canonical form of degree two on each `F P`, which near every point of the floor is the
  Poincaré residue (`MMP.Fourfold.IsPoincareResidue`) of a local section `τ` of
  `𝒪_Y(mK_Y + ⌊mB⌋)` (`MMP.Mori.pluricanonicalSections`) on all components meeting the open set.
  Since `mD` is Cartier and the floor is reduced, a section of `𝒪_{⌊B⌋}(mD)` is exactly such a
  locally liftable family: two local lifts agree modulo the ideal of the floor if and only if their
  residues agree at the generic points of the floor components. Restriction of a global section
  to the floor is the family of its residues.
* The pull-back of a floor section to a floor component `S` of the crepant dlt model `p : Y' ⟶ Y`
  is the residue along `S` of `p^*τ` for a local lift `τ` around `p(η_S)`; these pull-backs are
  required to form an admissible section system (`MMP.Fourfold.admissibleSections`) for a
  residue-restriction system `R` on the pairs `(S, B_S)` obtained by adjunction.
* Since `r_* 𝒪_Y = 𝒪_V` and `mD = r^*M`, pull-back `r^*` is an isomorphism
  `H⁰(V, M) ≅ H⁰(Y, mD)`; "the floor restriction of `r^*t` for a section `t` of `M`" is
  therefore stated as the floor restriction of a global section of `mD`
  (`MMP.Fourfold.logPluricanonicalSections`), and `t` generates `M` on an open `U ⊆ V` exactly
  when `r^*t` generates `mD` on `r⁻¹(U)` (`MMP.Mori.Scheme.GeneratesOn`).
* The degree of the horizontal floor on the generic fibre is `∑ [k(P) : k(V)]` over the floor
  components `P` dominating `V`.
* The base is a field `k`; `MMP.Fourfold.IsKltPair` forces it to be algebraically closed of
  characteristic zero. The source works over `ℂ`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

universe v

section

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold MMP.Mori

namespace Proof_lem_fourfold_mori_threefold_two_floor_section_descent

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The value of `D · C` for the one-term presentation `D = (1/N) L` of a `ℚ`-Cartier divisor with
Cartier multiple `L = N D`, computed on any normalization of `C`. -/
private theorem isRIntersectionNumber_cartierIndex {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) (c : ℝ) (hc : c = (D.cartierIndex hD : ℝ))
    (C : ProperCurve sX) {C' : Scheme.{0}} (ν : C' ⟶ C.scheme)
    (hν : MMP.Flips.IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    MMP.Flips.IsRIntersectionNumber k sX (QDivisor.toRDivisor D) (fun _ : Fin 1 => 1 / c)
      (fun _ => (D.cartierIndexSMul hD : Divisor X)) C
      (1 / c * ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX C.ι C.dim_le
        (D.cartierIndexSMul hD).2 : ℝ)) := by
  have hNpos : (0 : ℚ) < D.cartierIndex hD := by exact_mod_cast QDivisor.cartierIndex_pos hD
  have hLD : ∀ P, (((D.cartierIndexSMul hD : Divisor X).coeff P : ℤ) : ℚ) =
      (D.cartierIndex hD : ℚ) * D.coeff P := fun P => by
    have := congrArg (fun G : QDivisor X => G.coeff P) (QDivisor.toQDivisor_cartierIndexSMul D hD)
    simpa [zsmul_eq_mul] using this
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have h1 : MMP.Flips.IsCartierIntersectionNumber k sX C (D.cartierIndexSMul hD : Divisor X)
      (D.cartierIndexSMul hD).2
      ((D.cartierIndexSMul hD : Divisor X).degreeOn k sX (ν ≫ C.ι) hdim
        (D.cartierIndexSMul hD).2) := by
    have := hν.isFinite
    haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    exact ⟨C', ν, hν, hdim, rfl⟩
  refine ⟨fun _ => (D.cartierIndexSMul hD).2, fun _ => _, ?_, fun _ => h1, ?_⟩
  · ext P
    rw [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      QDivisor.coeff_toRDivisor, smul_eq_mul, ← Rat.cast_intCast, hLD P, hc]
    push_cast
    field_simp [show ((D.cartierIndex hD : ℚ) : ℝ) ≠ 0 by exact_mod_cast hNpos.ne']
    exact (mul_div_cancel_right₀ _ (by exact_mod_cast hNpos.ne')).symm
  · rw [Fin.sum_univ_one,
      ← MMP.Fourfold.Oai4C1.Negativity.eq_degreeOn_of_isCartierIntersectionNumber h1]

/-- **Nef on both signs is numerically trivial.** A `ℚ`-divisor `D` with `D` and `-D` both
relatively nef over `f` is, as an `ℝ`-divisor, numerically trivial over `f`. -/
private theorem isNumericallyTrivialOver_of_isRelativelyNef {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] {f : X ⟶ Y} {D : QDivisor X} (h₁ : QDivisor.IsRelativelyNef sX f D)
    (h₂ : QDivisor.IsRelativelyNef sX f (-D)) :
    MMP.Flips.IsNumericallyTrivialOver k sX f (QDivisor.toRDivisor D) := by
  obtain ⟨hD, hn⟩ := h₁
  obtain ⟨hD', hn'⟩ := h₂
  have hNpos : (0 : ℝ) < ((D.cartierIndex hD : ℚ) : ℝ) := by
    exact_mod_cast QDivisor.cartierIndex_pos hD
  have hNpos' : (0 : ℝ) < (((-D).cartierIndex hD' : ℚ) : ℝ) := by
    exact_mod_cast QDivisor.cartierIndex_pos hD'
  -- nefness, as an inequality on the degree of the Cartier multiple
  have hdeg : ∀ (E : QDivisor X) (hE : E.IsQCartier) (C : ProperCurve sX),
      (0 : ℝ) ≤ ((E.associatedCartier hE).sum fun G c =>
        (c : ℝ) * ((G : Divisor X).degreeOn k sX C.ι C.dim_le G.2 : ℝ)) →
      0 ≤ ((E.cartierIndexSMul hE : Divisor X).degreeOn k sX C.ι C.dim_le
        (E.cartierIndexSMul hE).2 : ℝ) := by
    intro E hE C key
    rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
      Finsupp.sum_single_index (by simp)] at key
    simp only [smul_eq_mul, mul_one] at key
    have hE0 : (0 : ℝ) < ((E.cartierIndex hE : ℚ) : ℝ) := by
      exact_mod_cast QDivisor.cartierIndex_pos hE
    push_cast at key
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg (show (0 : ℝ) < 1 / (E.cartierIndex hE : ℝ) from
      one_div_pos.mpr (by exact_mod_cast QDivisor.cartierIndex_pos hE)) hneg
    linarith
  have hval : ∀ (C : ProperCurve sX), C.IsContractedBy f → ∀ (m₁ : ℕ) (r₁ : Fin m₁ → ℝ)
      (L₁ : Fin m₁ → Divisor X) (x₁ : ℝ),
      MMP.Flips.IsRIntersectionNumber k sX (QDivisor.toRDivisor D) r₁ L₁ C x₁ → x₁ = 0 := by
    intro C hC m₁ r₁ L₁ x₁ hx
    rcases Nat.eq_zero_or_pos m₁ with rfl | hm
    · obtain ⟨-, -, -, -, rfl⟩ := hx
      simp
    obtain ⟨hL₁, d₁, -, hd₁, -⟩ := id hx
    obtain ⟨C', ν, hν, hdim, -⟩ := hd₁ ⟨0, hm⟩
    have hy := isRIntersectionNumber_cartierIndex hD _ rfl C ν hν hdim
    have hy' := isRIntersectionNumber_cartierIndex hD' _ rfl C ν hν hdim
    have e₁ := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hy
    -- the presentation of `-D`, negated, is a presentation of `D`
    have hy'' := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ (-1) 0
      hy' hy'
    rw [map_neg, neg_smul, one_smul, zero_smul, add_zero, neg_neg] at hy''
    have e₂ := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hy''
    have p₁ := hdeg D hD C (by exact_mod_cast hn C hC)
    have p₂ := hdeg (-D) hD' C (by exact_mod_cast hn' C hC)
    have q₁ : 0 ≤ x₁ := e₁ ▸ mul_nonneg (by positivity) p₁
    have q₂ : x₁ ≤ 0 := by
      rw [e₂]
      have := mul_nonneg (show (0 : ℝ) ≤ 1 / ((-D).cartierIndex hD' : ℝ) by positivity) p₂
      linarith
    linarith
  refine ⟨?_, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂
    x₂ hx₁ hx₂ => ?_⟩
  · have hc : (D.cartierIndexSMul hD : Divisor X).IsCartier := (D.cartierIndexSMul hD).2
    refine ⟨1, fun _ => 1 / ((D.cartierIndex hD : ℚ) : ℝ), fun _ => _, fun _ => hc, ?_⟩
    have hLD : ∀ P, (((D.cartierIndexSMul hD : Divisor X).coeff P : ℤ) : ℚ) =
        (D.cartierIndex hD : ℚ) * D.coeff P := fun P => by
      have := congrArg (fun G : QDivisor X => G.coeff P)
        (QDivisor.toQDivisor_cartierIndexSMul D hD)
      simpa [zsmul_eq_mul] using this
    ext P
    change (QDivisor.toRDivisor D).coeff P = _
    rw [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, QDivisor.coeff_toRDivisor, smul_eq_mul]
    change _ = _ * ((((D.cartierIndexSMul hD : Divisor X).coeff P : ℤ) : ℝ))
    rw [← Rat.cast_intCast, hLD P]
    push_cast
    field_simp
    exact (mul_div_cancel_right₀ _ (by exact_mod_cast hNpos.ne')).symm
  · rw [hval C hC m₁ r₁ L₁ x₁ hx₁]
    have h0 := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ _ _ _ _ _ _ 0 0
      hx₂ hx₂
    rw [zero_smul, zero_smul, add_zero] at h0
    have := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx₂ h0
    linarith

/-- A morphism surjective on stalks has residue degree one at every point. -/
private theorem residueDegree_eq_one {X Y : Scheme.{0}} (f : X ⟶ Y) [SurjectiveOnStalks f]
    (x : X) : f.residueDegree x = 1 := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  refine (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := Y.residueField (f x))
    (E := X.residueField x)).mpr ⟨(f.residueFieldMap x).hom.injective, fun z => ?_⟩
  obtain ⟨a, rfl⟩ := X.residue_surjective x z
  obtain ⟨b, rfl⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  change (Y.residue (f x) ≫ f.residueFieldMap x) b = _
  rw [Scheme.residue_residueFieldMap]
  rfl

/-- A closed immersion of an irreducible scheme onto the support of a prime divisor sends the
generic point to the generic point of the divisor. -/
private theorem map_genericPoint_eq_of_range {X T : Scheme.{0}} (j : T ⟶ X)
    [IsClosedImmersion j] [IrreducibleSpace T] (P : Mori.PrimeDivisor X)
    (hP : Set.range j.base = (P.support : Set X)) : j (genericPoint T) = P.genericPoint := by
  have h1 : IsGenericPoint (j (genericPoint T)) (P.support : Set X) := by
    have := (genericPoint_spec T).image j.base.hom.continuous
    rwa [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq, hP] at this
  have h2 : IsGenericPoint P.genericPoint (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  exact h1.eq h2

/-- The degree of a dominant integral closed subscheme `F ⟶ Y` of a prime divisor `P` over the
base is the residue degree of `r` at the generic point of `P`. -/
private theorem finrank_functionField_eq_residueDegree {Y V F : Scheme.{0}} [IsIntegral Y]
    [IsIntegral V] [IsIntegral F] (r : Y ⟶ V) (j : F ⟶ Y) [IsClosedImmersion j]
    [IsDominant (j ≫ r)] (P : Mori.PrimeDivisor Y)
    (hP : Set.range j.base = (P.support : Set Y)) :
    (letI := functionFieldMapAlgebra (j ≫ r)
     Module.finrank V.functionField F.functionField) = r.residueDegree P.genericPoint := by
  have h1 : (letI := functionFieldMapAlgebra (j ≫ r)
      Module.finrank V.functionField F.functionField) =
        (j ≫ r).residueDegree (genericPoint F) := by
    letI := functionFieldMapAlgebra (j ≫ r)
    letI := ((j ≫ r).residueFieldMap (genericPoint F)).hom.toAlgebra
    exact Algebra.finrank_eq_of_equiv_equiv (genericResidueEquivOfDominant (j ≫ r))
      (genericResidueEquiv F) (residueFieldMap_comp_genericResidueEquivOfDominant (j ≫ r))
  rw [h1, residueDegree_comp, residueDegree_eq_one j, mul_one,
    map_genericPoint_eq_of_range j P hP]

/-- A nonzero double finite sum over a predicate has a summand at which the predicate holds. -/
private theorem exists_of_finsum_finsum_ne_zero {ι : Type*} {p : ι → Prop} {f : ∀ i, p i → ℕ}
    {n : ℕ} (h : ∑ᶠ (i) (hi : p i), f i hi = n) (hn : n ≠ 0) : ∃ i, p i := by
  by_contra hno
  push Not at hno
  exact hn (h ▸ finsum_eq_zero_of_forall_eq_zero fun i => @finsum_of_isEmpty _ _ _ ⟨hno i⟩ _)

/-- On a variety of dimension `d` over a perfect field, the rational `m`-pluriforms of top degree
form a line over the function field. -/
private theorem finrank_rationalPluriForms_eq_one_of_topologicalKrullDim {k : Type} [Field k]
    [PerfectField k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) (m : ℤ) :
    Module.finrank X.functionField (RationalPluriForms sX d m) = 1 := by
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) hd
  let bb : Module.Basis Unit X.functionField (RationalPluriForms sX d m) :=
    ZTensorPower.basis b₀ m
  rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]

/-- The degree of the horizontal floor, written over the floor components with closed immersions,
is the sum of the residue degrees of `r` at the generic points of the floor primes dominating
`V`. -/
private theorem sum_residueDegree_eq_two {k : Type} [Field k] {Y V : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral V] {r : Y ⟶ V} [IsProper r] {B : QDivisor Y}
    {F : {P : Mori.PrimeDivisor Y // B.coeff P = 1} → Scheme.{0}} [∀ P, IsIntegral (F P)]
    (j : ∀ P, F P ⟶ Y) [∀ P, IsClosedImmersion (j P)]
    (hj : ∀ P, Set.range (j P).base = (P.1.support : Set Y))
    (hdeg : ∑ᶠ (P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}) (_ : IsDominant (j P ≫ r)),
      (letI : IsDominant (j P ≫ r) := ‹_›
       letI := functionFieldMapAlgebra (j P ≫ r)
       Module.finrank V.functionField (F P).functionField) = 2) :
    (open scoped Classical in
      ∑ P ∈ B.support with B P = 1 ∧ r.base '' (P.support : Set Y) = Set.univ,
        (letI := (r.residueFieldMap P.genericPoint).hom.toAlgebra;
          Module.finrank (V.residueField (r P.genericPoint)) (Y.residueField P.genericPoint))
        = 2) := by
  classical
  let g : Mori.PrimeDivisor Y → ℕ := fun Q =>
    if r.base '' (Q.support : Set Y) = Set.univ then r.residueDegree Q.genericPoint else 0
  have hdom : ∀ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1},
      IsDominant (j P ≫ r) ↔ r.base '' (P.1.support : Set Y) = Set.univ := by
    intro P
    have hrange : Set.range (j P ≫ r).base = r.base '' (P.1.support : Set Y) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hj]
    have hcl : IsClosed (r.base '' (P.1.support : Set Y)) :=
      r.isClosedMap _ (hj P ▸ (j P).isClosedEmbedding.isClosed_range)
    constructor
    · intro h
      have := h.denseRange
      rw [DenseRange, hrange] at this
      exact hcl.closure_eq ▸ this.closure_eq
    · intro h
      exact ⟨by rw [DenseRange, hrange, h]; exact dense_univ⟩
  have key : ∀ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1},
      (∑ᶠ (_ : IsDominant (j P ≫ r)),
        (letI : IsDominant (j P ≫ r) := ‹_›
         letI := functionFieldMapAlgebra (j P ≫ r)
         Module.finrank V.functionField (F P).functionField)) = g P.1 := by
    intro P
    rw [finsum_eq_dif]
    by_cases hd : IsDominant (j P ≫ r)
    · rw [dif_pos hd]
      simp only [g, if_pos ((hdom P).mp hd)]
      exact finrank_functionField_eq_residueDegree r (j P) P.1 (hj P)
    · rw [dif_neg hd]
      simp only [g, if_neg (fun h => hd ((hdom P).mpr h))]
  rw [finsum_congr key] at hdeg
  have hset : {Q : Mori.PrimeDivisor Y | B.coeff Q = 1} =
      ((B.support.filter fun Q => B Q = 1 : Finset _) : Set (Mori.PrimeDivisor Y)) := by
    ext Q
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finsupp.mem_support_iff]
    constructor
    · intro h
      exact ⟨by change B.coeff Q ≠ 0; rw [h]; exact one_ne_zero, h⟩
    · exact fun h => h.2
  have h2 : (∑ᶠ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}, g P.1) =
      ∑ Q ∈ B.support.filter (fun Q => B Q = 1), g Q := by
    rw [← finsum_mem_coe_finset, ← hset]
    exact finsum_set_coe_eq_finsum_mem {Q : Mori.PrimeDivisor Y | B.coeff Q = 1}
  rw [h2] at hdeg
  rw [← hdeg, ← Finset.filter_filter, Finset.sum_filter]
  rfl

/-- The exterior product of a linearly independent family of vectors in a vector space is
nonzero: pairing with the exterior product of dual coordinate functionals gives `det 1 = 1`. -/
private theorem ιMulti_ne_zero_of_linearIndependent {L E : Type*} [Field L] [AddCommGroup E]
    [Module L E] {n : ℕ} {v : Fin n → E} (hv : LinearIndependent L v) :
    exteriorPower.ιMulti L n v ≠ 0 := by
  classical
  let W := Submodule.span L (Set.range v)
  let b : Module.Basis (Fin n) L W := Module.Basis.span hv
  have hf : ∀ i, ∃ g : Module.Dual L E, g.comp W.subtype = b.coord i := fun i =>
    LinearMap.exists_extend (b.coord i)
  choose f hf using hf
  have hfv : ∀ i j, f j (v i) = if i = j then 1 else 0 := by
    intro i j
    have hbi : (b i : E) = v i := by
      rw [Module.Basis.span_apply]
    rw [← hbi]
    change (f j).comp W.subtype (b i) = _
    rw [hf j, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [Finsupp.single_apply]
  intro h0
  have := exteriorPower.pairingDual_ιMulti_ιMulti (R := L) (M := E) f v
  rw [h0, map_zero] at this
  have hdet : Matrix.det (n := Fin n) (Matrix.of fun i j => f j (v i)) = 1 := by
    rw [← Matrix.det_one (n := Fin n)]
    congr 1
    ext i j
    rw [Matrix.of_apply, hfv, Matrix.one_apply]
  rw [hdet] at this
  exact zero_ne_one this

/-- **A logarithmic frame along a prime divisor.** Let `j : T ⟶ Y` be an integral closed subscheme
of a normal variety of dimension `n + 1` over a field of characteristic zero, whose generic point
is that of the prime divisor `P`. There is a rational top form `σ` with `ord_P σ = -1` and a
nonzero Poincaré residue along `T`: `σ = ϖ⁻¹ dϖ ∧ dx₁ ∧ ⋯ ∧ dx_n` (up to a positive integer), for
a uniformizer `ϖ` and lifts `xᵢ` of elements of `k(T)` with independent differentials. -/
private theorem exists_logFrame {k : Type} [Field k] [CharZero k] {Y T : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType sY] {n : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = n + 1)
    (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [LocallyOfFiniteType (j ≫ sY)]
    (P : Mori.PrimeDivisor Y) (hjT : j (genericPoint T) = P.genericPoint) :
    ∃ σ : RationalPluriForms sY (n + 1) 1, P.ordForm σ = -1 ∧
      ∃ ρ : RationalPluriForms (j ≫ sY) n 1, IsPoincareResidue sY j n 1 σ ρ ∧ ρ ≠ 0 := by
  classical
  letI := stalkAlgebra sY (j (genericPoint T))
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have hdT : (Algebra.trdeg k T.functionField).toNat = n := by
    have := trdeg_add_one_of_eq_genericPoint (sY := sY) (j := j) P hjT
    omega
  haveI := essFiniteType_functionField (sX := j ≫ sY)
  have hfr : Module.finrank T.functionField Ω[T.functionField⁄k] = n := by
    rw [finrank_kaehlerDifferential_eq_trdeg k T.functionField, hdT]
  -- `n` elements of `k(T)` with independent differentials
  obtain ⟨y, hy⟩ : ∃ y : Fin n → T.functionField,
      LinearIndependent T.functionField fun i => KaehlerDifferential.D k T.functionField (y i) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨Fin.elim0, linearIndependent_empty_type⟩
    haveI : Module.Finite T.functionField Ω[T.functionField⁄k] :=
      Module.finite_of_finrank_pos (by omega)
    obtain ⟨s, hsD, hspan, hli⟩ := exists_linearIndependent T.functionField
      (Set.range (KaehlerDifferential.D k T.functionField))
    let b := Module.Basis.mk hli (by
      rw [Subtype.range_coe, hspan, KaehlerDifferential.span_range_derivation])
    haveI : Finite s := Module.Finite.finite_basis b
    have hcard : Nat.card s = n := by rw [← Module.finrank_eq_nat_card_basis b, hfr]
    let e : Fin n ≃ s := (finCongr hcard.symm).trans (Finite.equivFin s).symm
    refine ⟨fun i => (hsD (e i).2).choose, ?_⟩
    have : (fun i => KaehlerDifferential.D k T.functionField (hsD (e i).2).choose) =
        fun i => ((e i : s) : Ω[T.functionField⁄k]) :=
      funext fun i => (hsD (e i).2).choose_spec
    rw [this]
    exact hli.comp e e.injective
  obtain ⟨-, hsurj⟩ := stalkMap_facts_of_isClosedImmersion (sY := sY) (j := j)
  choose x hx using fun i => hsurj (y i)
  obtain ⟨ϖ, -, hϖ0, -, -, hϖsq, -⟩ := exists_uniformizer_of_eq_genericPoint (sY := sY) P hjT
  let ν : MvPolynomial (Fin (n + 1)) k →ₐ[k] Y.presheaf.stalk (j (genericPoint T)) :=
    MvPolynomial.aeval (Fin.cons ϖ x)
  have hX0 : ν (MvPolynomial.X 0) = ϖ := by simp [ν]
  have hXs : ∀ i : Fin n, ν (MvPolynomial.X i.succ) = x i := by simp [ν]
  have hϖne : ϖ ≠ 0 := by
    rintro rfl
    exact hϖsq (Ideal.zero_mem _)
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (j (genericPoint T))) := by
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    have := hu.map (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField)
    rw [hϖ0] at this
    exact not_isUnit_zero this
  have hϖK : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖne
  have hli : LinearIndependent T.functionField (fun i : Fin n =>
      KaehlerDifferential.D k T.functionField
        ((j.stalkMap (genericPoint T)).hom (ν (MvPolynomial.X i.succ)))) := by
    convert hy using 2 with i
    rw [hXs]
    exact congrArg _ (hx i)
  have hF : (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ)⁻¹ *
      algebraMap _ Y.functionField (ν (MvPolynomial.X 0)) =
        algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField 1 := by
    rw [hX0, inv_mul_cancel₀ hϖK, map_one]
  obtain ⟨e, he, hres, hord⟩ := exists_isPoincareResidue_smul_tprod_ιMulti sY hd j P hjT ν
    (hX0 ▸ hϖm) (hX0 ▸ hϖne) hli hF
  refine ⟨_, hord isUnit_one, _, hres, ?_⟩
  haveI : CharZero T.functionField :=
    charZero_of_injective_algebraMap (algebraMap k T.functionField).injective
  refine smul_ne_zero ?_ fun h0 => ?_
  · rw [map_one, mul_one]
    exact Nat.cast_ne_zero.mpr he.ne'
  · refine ιMulti_ne_zero_of_linearIndependent hli
      (tprod_fin_one_injective (F := T.functionField) ?_)
    exact h0.trans (MultilinearMap.map_coord_zero _ (0 : Fin 1) rfl).symm

/-- **Comparison of two forms with the same residue.** Let `j : T ⟶ Y` be an integral closed
subscheme of a normal variety of dimension `n + 1` over a field of characteristic zero, with
generic point that of the prime divisor `P`, and `m = M + 1`. Two `m`-canonical forms with at
most a pole of order `m` along `P` and the same Poincaré residue along `T` agree to first order:
their difference is zero or has order at least `1 - m` along `P`. Both are multiples `c σ` of the
`m`-th power `σ` of a logarithmic frame, with `c` regular along `P`, and their residues are
`c̄ Res σ` with `Res σ ≠ 0`. -/
private theorem isPoincareResidue_sub {k : Type} [Field k] [CharZero k] {Y T : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType sY] {n : ℕ} (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [LocallyOfFiniteType (j ≫ sY)]
    (hT : topologicalKrullDim T = n)
    (P : Mori.PrimeDivisor Y) (hjT : j (genericPoint T) = P.genericPoint) (M : ℕ)
    {τ₁ τ₂ : RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)}
    (h₁ : τ₁ = 0 ∨ -((M + 1 : ℕ) : ℤ) ≤ P.ordForm τ₁)
    (h₂ : τ₂ = 0 ∨ -((M + 1 : ℕ) : ℤ) ≤ P.ordForm τ₂)
    {ρ : RationalPluriForms (j ≫ sY) n ((M + 1 : ℕ) : ℤ)}
    (hρ₁ : IsPoincareResidue sY j n (M + 1) τ₁ ρ) (hρ₂ : IsPoincareResidue sY j n (M + 1) τ₂ ρ) :
    τ₁ = τ₂ ∨ 1 - ((M + 1 : ℕ) : ℤ) ≤ P.ordForm (τ₁ - τ₂) := by
  classical
  letI := stalkAlgebra sY (j (genericPoint T))
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  have hd : (Algebra.trdeg k Y.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; norm_cast)
  obtain ⟨σ₁, hσ₁ord, ρ₁, hσρ₁, hρ₁0⟩ := exists_logFrame sY hd j P hjT
  have hσ₁0 : σ₁ ≠ 0 := by
    rintro rfl
    rw [PrimeDivisor.ordForm_zero] at hσ₁ord
    omega
  set σ := MMP.CyclicChartDifferent.Aux.pluriPow σ₁ M with hσdef
  have hσ0 : σ ≠ 0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero (by exact_mod_cast hY) hσ₁0 M
  have hσord : P.ordForm σ = -((M + 1 : ℕ) : ℤ) := by
    rw [hσdef, MMP.CyclicChartDifferent.Aux.ordForm_pluriPow (by exact_mod_cast hY) hσ₁0 P M,
      hσ₁ord]
    ring
  have hσρ := MMP.CyclicChartDifferent.Aux.isPoincareResidue_pluriPow P hjT
    (by exact_mod_cast hY) hσρ₁ M
  have hρσ0 : MMP.CyclicChartDifferent.Aux.pluriPow ρ₁ M ≠ 0 :=
    MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero (by exact_mod_cast hT) hρ₁0 M
  -- the line of `m`-canonical forms
  have hrank : Module.finrank Y.functionField
      (RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)) = 1 :=
    finrank_rationalPluriForms_eq_one_of_topologicalKrullDim sY (d := n + 1)
      (by exact_mod_cast hY) _
  have hspP : j (genericPoint T) ⤳ P.genericPoint := specializes_of_eq hjT
  have hspP' : P.genericPoint ⤳ j (genericPoint T) := specializes_of_eq hjT.symm
  -- every form with at most an `m`-fold pole is a regular multiple of `σ`
  have hmul : ∀ τ : RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ),
      (τ = 0 ∨ -((M + 1 : ℕ) : ℤ) ≤ P.ordForm τ) →
      ∃ c : Y.presheaf.stalk (j (genericPoint T)), τ = algebraMap _ Y.functionField c • σ := by
    intro τ hτ
    by_cases hτ0 : τ = 0
    · exact ⟨0, by rw [hτ0, map_zero, zero_smul]⟩
    have hτord := hτ.resolve_left hτ0
    obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' σ hσ0).mp hrank τ
    have hf0 : f ≠ 0 := by rintro rfl; exact hτ0 (by rw [← hf, zero_smul])
    have hford : 0 ≤ Y.ord f P.genericPoint := by
      have := P.ordForm_smul (sX := sY) hd hf0 hσ0
      rw [hf, hσord] at this
      omega
    obtain ⟨a, ha⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg P hf0 hford
    refine ⟨(Y.presheaf.stalkSpecializes hspP).hom a, ?_⟩
    rw [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' Y hspP, ha, hf]
  obtain ⟨c₁, hc₁⟩ := hmul τ₁ h₁
  obtain ⟨c₂, hc₂⟩ := hmul τ₂ h₂
  have hr₁ := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hσρ c₁
  have hr₂ := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hσρ c₂
  rw [← hc₁] at hr₁
  rw [← hc₂] at hr₂
  have e₁ := IsPoincareResidue.unique_of_isClosedImmersion P hjT hρ₁ hr₁
  have e₂ := IsPoincareResidue.unique_of_isClosedImmersion P hjT hρ₂ hr₂
  have hc : (j.stalkMap (genericPoint T)).hom (c₁ - c₂) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact smul_left_injective T.functionField hρσ0 (e₁.symm.trans e₂)
  have hδ : τ₁ - τ₂ = algebraMap _ Y.functionField (c₁ - c₂) • σ := by
    rw [hc₁, hc₂, map_sub, sub_smul]
  by_cases hg : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField (c₁ - c₂) = 0
  · left
    rw [← sub_eq_zero, hδ, hg, zero_smul]
  right
  -- `c₁ - c₂` lies in the maximal ideal, so has order at least one
  set a := (Y.presheaf.stalkSpecializes hspP').hom (c₁ - c₂) with hadef
  have haK : algebraMap _ Y.functionField a =
      algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField (c₁ - c₂) :=
    MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' Y hspP' _
  have hamax : a ∈ IsLocalRing.maximalIdeal P.localRing := by
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    have hu' := hu.map (Y.presheaf.stalkSpecializes hspP).hom
    have hback : (Y.presheaf.stalkSpecializes hspP).hom a = c₁ - c₂ := by
      rw [hadef, ← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
        TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    rw [hback] at hu'
    have := hu'.map (j.stalkMap (genericPoint T)).hom
    rw [hc] at this
    exact not_isUnit_zero this
  have hlt := (P.divisorialValuation_algebraMap_lt_one_iff a).mpr hamax
  rw [haK, P.divisorialValuation_eq_exp_neg_ord hg, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    at hlt
  rw [hδ, P.ordForm_smul (sX := sY) hd hg hσ0, hσord]
  omega

/-- **Residues of forms with at most an `m`-fold pole.** Along an integral closed subscheme
`j : T ⟶ Y` of a normal variety of dimension `n + 1` over a field of characteristic zero, with
generic point that of the prime divisor `P`, every `m`-canonical form `τ` with at most a pole of
order `m = M + 1` along `P` has a Poincaré residue, which is nonzero when the pole has order
exactly `m`: `τ = c σ` for the `m`-th power `σ` of a logarithmic frame and `c` regular along `P`,
and `Res τ = c̄ Res σ`. -/
private theorem exists_isPoincareResidue {k : Type} [Field k] [CharZero k] {Y T : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType sY] {n : ℕ} (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [LocallyOfFiniteType (j ≫ sY)]
    (hT : topologicalKrullDim T = n)
    (P : Mori.PrimeDivisor Y) (hjT : j (genericPoint T) = P.genericPoint) (M : ℕ)
    {τ : RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)}
    (hτ : τ = 0 ∨ -((M + 1 : ℕ) : ℤ) ≤ P.ordForm τ) :
    ∃ ρ : RationalPluriForms (j ≫ sY) n ((M + 1 : ℕ) : ℤ),
      IsPoincareResidue sY j n (M + 1) τ ρ ∧
        (τ ≠ 0 → P.ordForm τ = -((M + 1 : ℕ) : ℤ) → ρ ≠ 0) := by
  classical
  letI := stalkAlgebra sY (j (genericPoint T))
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  have hd : (Algebra.trdeg k Y.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; norm_cast)
  obtain ⟨σ₁, hσ₁ord, ρ₁, hσρ₁, hρ₁0⟩ := exists_logFrame sY hd j P hjT
  have hσ₁0 : σ₁ ≠ 0 := by
    rintro rfl
    rw [PrimeDivisor.ordForm_zero] at hσ₁ord
    omega
  set σ := MMP.CyclicChartDifferent.Aux.pluriPow σ₁ M with hσdef
  have hσ0 : σ ≠ 0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero (by exact_mod_cast hY) hσ₁0 M
  have hσord : P.ordForm σ = -((M + 1 : ℕ) : ℤ) := by
    rw [hσdef, MMP.CyclicChartDifferent.Aux.ordForm_pluriPow (by exact_mod_cast hY) hσ₁0 P M,
      hσ₁ord]
    ring
  have hσρ := MMP.CyclicChartDifferent.Aux.isPoincareResidue_pluriPow P hjT
    (by exact_mod_cast hY) hσρ₁ M
  have hρσ0 : MMP.CyclicChartDifferent.Aux.pluriPow ρ₁ M ≠ 0 :=
    MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero (by exact_mod_cast hT) hρ₁0 M
  -- the line of `m`-canonical forms
  have hrank : Module.finrank Y.functionField
      (RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)) = 1 :=
    finrank_rationalPluriForms_eq_one_of_topologicalKrullDim sY (d := n + 1)
      (by exact_mod_cast hY) _
  have hspP : j (genericPoint T) ⤳ P.genericPoint := specializes_of_eq hjT
  have hspP' : P.genericPoint ⤳ j (genericPoint T) := specializes_of_eq hjT.symm
  -- every form with at most an `m`-fold pole is a regular multiple of `σ`
  have hmul : ∀ τ : RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ),
      (τ = 0 ∨ -((M + 1 : ℕ) : ℤ) ≤ P.ordForm τ) →
      ∃ c : Y.presheaf.stalk (j (genericPoint T)), τ = algebraMap _ Y.functionField c • σ := by
    intro τ hτ
    by_cases hτ0 : τ = 0
    · exact ⟨0, by rw [hτ0, map_zero, zero_smul]⟩
    have hτord := hτ.resolve_left hτ0
    obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' σ hσ0).mp hrank τ
    have hf0 : f ≠ 0 := by rintro rfl; exact hτ0 (by rw [← hf, zero_smul])
    have hford : 0 ≤ Y.ord f P.genericPoint := by
      have := P.ordForm_smul (sX := sY) hd hf0 hσ0
      rw [hf, hσord] at this
      omega
    obtain ⟨a, ha⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg P hf0 hford
    refine ⟨(Y.presheaf.stalkSpecializes hspP).hom a, ?_⟩
    rw [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' Y hspP, ha, hf]
  obtain ⟨c, hc⟩ := hmul τ hτ
  have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hσρ c
  rw [← hc] at hres
  refine ⟨_, hres, fun hτ0 hτord hρ0 => ?_⟩
  -- a form with zero residue differs from `0` to first order
  have h0 : IsPoincareResidue sY j n (M + 1) (0 : RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ))
      ((j.stalkMap (genericPoint T)).hom c • MMP.CyclicChartDifferent.Aux.pluriPow ρ₁ M) := by
    rw [hρ0]
    have := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hσρ 0
    rwa [map_zero, zero_smul, map_zero, zero_smul] at this
  rcases isPoincareResidue_sub sY hY j hT P hjT M hτ (Or.inl rfl) hres h0 with h | h
  · exact hτ0 h
  · rw [sub_zero, hτord] at h
    omega

/-- The pull-back of a Cartier divisor `M` has coefficient zero along every prime divisor whose
generic point maps outside `Supp M`: `1` is a local equation of `M` off its support. -/
private theorem coeff_eq_zero_of_isPullback {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {r : Y ⟶ V} {M : Divisor V}
    {hrM : ∀ W : irreducibleComponents Y, r (componentGenericPoint Y W) ∉ M.supp}
    {rM : Divisor Y} (hrMp : M.IsPullback r hrM rM) (Γ : Mori.PrimeDivisor Y)
    (hΓ : r Γ.genericPoint ∉ M.supp) : rM.coeff Γ = 0 := by
  let U₀ : V.Opens := ⟨(M.supp : Set V)ᶜ, M.isClosed_supp.isOpen_compl⟩
  have hφ : M.IsLocalEquation U₀ 1 := by
    rintro E ⟨x, hxE, hxU⟩
    rw [PrimeDivisor.ord_one]
    by_contra hne
    exact hxU (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hxE⟩)
  have hE : (Γ.support ∩ r ⁻¹ᵁ U₀).Nonempty := (Γ.genericPoint_mem_iff (r ⁻¹ᵁ U₀)).mp hΓ
  rw [hrMp U₀ 1 hφ Γ hE, pullbackComponent_eq hrM hφ _ (mem_pointComponent _) 1 (by
    rw [Units.val_one, map_one, Units.val_one, Pi.one_apply])]
  simp

/-- **A section of `m(K_Y + B)` with a zero along a horizontal prime vanishes.** With
`div α + mB = r^*M`, `mB` integral and `r_* 𝒪_Y = 𝒪_V`, a global section `δ` of `m(K_Y + B)` is
`h α` with `div h + r^*M ≥ 0`; off `r⁻¹ Supp M` the function `h` is regular by Hartogs, hence
pulled back from `V`. If `δ` has order at least `1 - m` along a prime `P₀` dominating `V`, then
`h` vanishes along `P₀`, while a nonzero function from `k(V)` is a unit at the generic point of
`P₀`. -/
private theorem eq_zero_of_le_ordForm
    {k : Type} [Field k] [CharZero k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    {sV : V ⟶ Spec (.of k)}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sY]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {r : Y ⟶ V} (hr : IsContraction sY sV r) (hY : topologicalKrullDim Y = 3) {B : QDivisor Y}
    {m : ℕ} (α : RationalPluriForms sY 3 m) (M : Divisor V)
    (hrM : ∀ W : irreducibleComponents Y, r (componentGenericPoint Y W) ∉ M.supp)
    (rM : Divisor Y) (hrMp : M.IsPullback r hrM rM) (hα : α ≠ 0)
    (hαM : ∀ P : Mori.PrimeDivisor Y, (P.ordForm α : ℚ) + (m : ℚ) * B.coeff P = (rM.coeff P : ℚ))
    (hmB : ∀ P, ((m : ℚ) * B.coeff P).den = 1)
    {δ : RationalPluriForms sY 3 m} (hδ : δ ∈ logPluricanonicalSections sY 3 m B)
    (P₀ : Mori.PrimeDivisor Y) (hB₀ : B.coeff P₀ = 1) (hP₀ : r P₀.genericPoint = genericPoint V)
    (hord : δ = 0 ∨ 1 - (m : ℤ) ≤ P₀.ordForm δ) : δ = 0 := by
  classical
  by_contra hδ0
  have hord' := hord.resolve_left hδ0
  letI := functionFieldAlgebra sY
  have hd : (Algebra.trdeg k Y.functionField).toNat = 3 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; rfl)
  have hrank : Module.finrank Y.functionField (RationalPluriForms sY 3 m) = 1 :=
    finrank_rationalPluriForms_eq_one_of_topologicalKrullDim sY (d := 3) (by rw [hY]; rfl) _
  obtain ⟨h, hh⟩ := (finrank_eq_one_iff_of_nonzero' α hα).mp hrank δ
  have hh0 : h ≠ 0 := by rintro rfl; exact hδ0 (by rw [← hh, zero_smul])
  have hordh : ∀ Γ : Mori.PrimeDivisor Y,
      Γ.ordForm δ = Y.ord h Γ.genericPoint + Γ.ordForm α := fun Γ => by
    rw [← hh, Γ.ordForm_smul (sX := sY) hd hh0 hα]
  -- `div h + r^*M ≥ 0`
  have hpos : ∀ Γ : Mori.PrimeDivisor Y, -rM.coeff Γ ≤ Y.ord h Γ.genericPoint := by
    intro Γ
    have h1 := (mem_logPluricanonicalSections (sX := sY)).mp hδ |>.2 Γ
      ((Γ.genericPoint_mem_iff ⊤).mp trivial) hδ0
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, hordh Γ] at h1
    have h2 := hαM Γ
    have hint : ((⌊(m : ℤ) • B.coeff Γ⌋ : ℤ) : ℚ) = (m : ℚ) * B.coeff Γ := by
      rw [zsmul_eq_mul, Int.cast_natCast]
      have hq := Rat.coe_int_num_of_den_eq_one (hmB Γ)
      conv_lhs => rw [← hq]
      rw [Int.floor_intCast]
      exact hq
    have : ((Y.ord h Γ.genericPoint : ℤ) : ℚ) ≥ -(rM.coeff Γ : ℚ) := by
      have h1' : (0 : ℚ) ≤ ((Y.ord h Γ.genericPoint + Γ.ordForm α : ℤ) : ℚ) +
          ((⌊(m : ℤ) • B.coeff Γ⌋ : ℤ) : ℚ) := by exact_mod_cast h1
      push_cast at h1'
      rw [hint] at h1'
      linarith
    exact_mod_cast this
  haveI : IsDominant r := ⟨hr.surjective.denseRange⟩
  -- the generic point of `V` is off `Supp M`
  have hηV : genericPoint V ∉ M.supp := by
    obtain ⟨W⟩ : Nonempty (irreducibleComponents Y) :=
      ⟨⟨Set.univ, (irreducibleComponents_eq_singleton (X := Y)).symm ▸ rfl⟩⟩
    have := hrM W
    rwa [componentGenericPoint_eq_genericPoint,
      map_genericPoint_of_isDominant r] at this
  have hrM0 : rM.coeff P₀ = 0 := coeff_eq_zero_of_isPullback hrMp P₀ (by rw [hP₀]; exact hηV)
  have hordP₀ : 1 ≤ Y.ord h P₀.genericPoint := by
    have h1 := hαM P₀
    rw [hrM0, hB₀] at h1
    have h2 : P₀.ordForm α = -(m : ℤ) := by
      have : ((P₀.ordForm α : ℤ) : ℚ) = ((-(m : ℤ) : ℤ) : ℚ) := by
        push_cast at h1 ⊢; linarith
      exact_mod_cast this
    have := hordh P₀
    omega
  -- off `r⁻¹ Supp M`, `h` is regular, hence pulled back from `V`
  let U₀ : V.Opens := ⟨(M.supp : Set V)ᶜ, M.isClosed_supp.isOpen_compl⟩
  have hP₀U : P₀.genericPoint ∈ r ⁻¹ᵁ U₀ := by
    change r P₀.genericPoint ∉ M.supp
    rw [hP₀]; exact hηV
  haveI : Nonempty (r ⁻¹ᵁ U₀) := ⟨⟨_, hP₀U⟩⟩
  haveI : Nonempty U₀ := ⟨⟨_, hP₀U⟩⟩
  obtain ⟨t, ht⟩ := MMP.Threefold.Bridges.exists_germToFunctionField_eq_of_forall_zero_le_ord
    (r ⁻¹ᵁ U₀) h fun Γ ⟨x, hxΓ, hxU⟩ => by
      have hηΓ : Γ.genericPoint ∈ r ⁻¹ᵁ U₀ :=
        (Γ.genericPoint_mem_iff (r ⁻¹ᵁ U₀)).mpr ⟨x, hxΓ, hxU⟩
      have := hpos Γ
      rw [coeff_eq_zero_of_isPullback hrMp Γ hηΓ] at this
      omega
  haveI := hr.isIso_app U₀
  set g := inv (r.app U₀) t with hgdef
  have hgt : r.app U₀ g = t := by
    rw [hgdef, ← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  set f := V.germToFunctionField U₀ g with hfdef
  have hhf : functionFieldMap r f = h := by
    rw [hfdef, MMP.Spreading.functionFieldMap_germToFunctionField r U₀ (r ⁻¹ᵁ U₀) le_rfl g,
      Scheme.Hom.appLE_eq_app, hgt, ht]
  -- `f` is a unit at the generic point of `V`, so `h` is a unit along `P₀`
  set a := V.presheaf.germ U₀ (r P₀.genericPoint) hP₀U g with hadef
  have haf : algebraMap (V.presheaf.stalk (r P₀.genericPoint)) V.functionField a = f :=
    Scheme.algebraMap_germ_eq_germToFunctionField (X := V) hP₀U g
  have hf0 : f ≠ 0 := by
    rintro hf0
    rw [hf0, map_zero] at hhf
    exact hh0 hhf.symm
  have ha0 : a ≠ 0 := by
    rintro ha0
    rw [ha0, map_zero] at haf
    exact hf0 haf.symm
  have hfield : IsField (V.presheaf.stalk (r P₀.genericPoint)) := by
    rw [hP₀]; exact Field.toIsField V.functionField
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel ha0
  have hau : IsUnit a := IsUnit.of_mul_eq_one b hb
  have hhst : h = algebraMap (Y.presheaf.stalk P₀.genericPoint) Y.functionField
      ((r.stalkMap P₀.genericPoint).hom a) := by
    rw [← hhf, ← haf, functionFieldMap_algebraMap_stalk]
  have := P₀.ord_algebraMap_of_isUnit (hau.map (r.stalkMap P₀.genericPoint).hom)
  rw [← hhst] at this
  omega

/-- The coefficient of the pull-back of a Cartier divisor along a prime divisor `E` meeting the
preimage of an open `U` on which `φ` is a local equation is the order along `E` of the pull-back
of `φ` to the function field. -/
private theorem coeff_eq_ord_of_isPullback {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} [IsDominant f] {C : Divisor X}
    {hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp}
    {C' : Divisor Y} (hCp : C.IsPullback f hC C') {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : C.IsLocalEquation U φ) (E : Mori.PrimeDivisor Y)
    (hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty) (Z : irreducibleComponents X) :
    C'.coeff E = Y.ord (functionFieldMap f
        (MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions X))) E.genericPoint := by
  classical
  rw [hCp U φ hφ E hE]
  have hZp := E.map_componentGenericPoint_mem f hE
  have hW := mem_pointComponent (f (componentGenericPoint Y E.component))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZp (hC _) hW
  rw [pullbackComponent_eq hC hφ hZp hW a ha]
  set u := Units.map (f.stalkMap (componentGenericPoint Y E.component)).hom.toMonoidHom a
  let ψ : (RationalFunctions Y)ˣ :=
    (RationalFunctions.unitsEquiv Y).symm (Function.update 1 E.component u)
  have hψZ : (ψ : RationalFunctions Y) E.component = u := by
    simp [ψ, RationalFunctions.unitsEquiv]
  have h1 : E.ordUnit u = E.ord ψ := by
    rw [PrimeDivisor.ord_eq_ordUnit]
    congr 1
    exact (Units.ext hψZ).symm
  rw [h1, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  congr 1
  obtain rfl : Z = pointComponent (f (componentGenericPoint Y E.component)) :=
    Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
  change (Y.presheaf.stalkSpecializes _).hom ((ψ : RationalFunctions Y) E.component) =
    functionFieldMap f ((X.presheaf.stalkSpecializes _).hom
      ((φ : RationalFunctions X) _))
  rw [hψZ, ← ha]
  change _ = functionFieldMap f ((stalkToRationalFunctions X hW ≫
    X.presheaf.stalkSpecializes _).hom a)
  rw [stalkToRationalFunctions, TopCat.Presheaf.stalkSpecializes_comp]
  exact (functionFieldMap_algebraMap_stalk f (componentGenericPoint Y E.component) a.val).symm

/-- **Functions regular over an open of the base come from the base.** For a contraction
`r : Y ⟶ V` (`r_* 𝒪_Y = 𝒪_V`) of normal integral schemes and an open `W ⊆ V` with `r⁻¹ W`
nonempty, a rational function `h` on `Y` without poles along the prime divisors meeting
`r⁻¹ W` is `r^* g` for a section `g` of `𝒪_V` over `W` (algebraic Hartogs). -/
private theorem exists_app_eq_of_zero_le_ord {k : Type} [Field k] {Y V : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    {r : Y ⟶ V} (hr : IsContraction sY sV r) (W : V.Opens) [Nonempty (r ⁻¹ᵁ W)]
    (h : Y.functionField)
    (hh : ∀ Γ : Mori.PrimeDivisor Y, (Γ.support ∩ r ⁻¹ᵁ W).Nonempty →
      0 ≤ Y.ord h Γ.genericPoint) :
    ∃ g : Γ(V, W), Y.germToFunctionField (r ⁻¹ᵁ W) (r.app W g) = h := by
  obtain ⟨t, ht⟩ := MMP.Threefold.Bridges.exists_germToFunctionField_eq_of_forall_zero_le_ord
    (r ⁻¹ᵁ W) h hh
  haveI := hr.isIso_app W
  refine ⟨inv (r.app W) t, ?_⟩
  have : r.app W (inv (r.app W) t) = t := by
    rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
  rw [this, ht]

/-- A section of `m(K_Y + B)` with `mB` integral has order at least `-m b_Γ` along every prime
divisor `Γ`. -/
private theorem le_ordForm_of_mem_logPluricanonicalSections {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {B : QDivisor Y} {m : ℕ} (hmB : ∀ P, ((m : ℚ) * B.coeff P).den = 1)
    {τ : RationalPluriForms sY 3 m} (hτ : τ ∈ logPluricanonicalSections sY 3 m B) (hτ0 : τ ≠ 0)
    (Γ : Mori.PrimeDivisor Y) : -((m : ℚ) * B.coeff Γ) ≤ (Γ.ordForm τ : ℚ) := by
  have h1 := (mem_logPluricanonicalSections (sX := sY)).mp hτ |>.2 Γ
    ((Γ.genericPoint_mem_iff ⊤).mp trivial) hτ0
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at h1
  have hq := Rat.coe_int_num_of_den_eq_one (hmB Γ)
  have hfl : ((⌊(m : ℚ) * B.coeff Γ⌋ : ℤ) : ℚ) = (m : ℚ) * B.coeff Γ := by
    conv_lhs => rw [← hq]
    rw [Int.floor_intCast]
    exact hq
  have : (0 : ℚ) ≤ ((Γ.ordForm τ : ℤ) : ℚ) + ((⌊(m : ℚ) * B.coeff Γ⌋ : ℤ) : ℚ) := by
    exact_mod_cast h1
  rw [hfl] at this
  linarith

/-- **An extension generates where the local lift does.** Let `τ_U` generate `m(K_Y + B)` on an
open `U` through a point `y` of a floor prime `P₀`, and let the global section `τ` have the same
residue along `P₀`. Then `τ = q τ_U` with `q` regular at `y` (Hartogs) and `q ≡ 1` along `P₀`, so
`q` is a unit at `y`, and `τ` generates along every prime divisor through `y`. -/
private theorem ordForm_add_eq_zero_of_generatesOn {k : Type} [Field k] [CharZero k]
    {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 3) {B : QDivisor Y}
    {m : ℕ} (hm : 0 < m) (hmB : ∀ P, ((m : ℚ) * B.coeff P).den = 1)
    (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [LocallyOfFiniteType (j ≫ sY)]
    (hT : topologicalKrullDim T = 2) (P₀ : Mori.PrimeDivisor Y) (hB₀ : B.coeff P₀ = 1)
    (hjP : Set.range j.base = (P₀.support : Set Y)) {y : Y} (hy : y ∈ (P₀.support : Set Y))
    {U : Y.Opens} (hyU : y ∈ U) {τU : RationalPluriForms sY 3 m}
    (hgen : GeneratesOn B m U τU) {τ : RationalPluriForms sY 3 m}
    (hτ : τ ∈ logPluricanonicalSections sY 3 m B) {ρ : RationalPluriForms (j ≫ sY) 2 m}
    (hρ : IsPoincareResidue sY j 2 m τ ρ) (hρU : IsPoincareResidue sY j 2 m τU ρ) :
    τ ≠ 0 ∧ ∀ Γ : Mori.PrimeDivisor Y, y ∈ (Γ.support : Set Y) →
      (Γ.ordForm τ : ℚ) + (m : ℚ) * B.coeff Γ = 0 := by
  classical
  letI := functionFieldAlgebra sY
  have hd : (Algebra.trdeg k Y.functionField).toNat = 3 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; rfl)
  have hjT := map_genericPoint_eq_of_range j P₀ hjP
  have hτU0 := hgen.1
  have hUP₀ : ((P₀.support : Set Y) ∩ U).Nonempty := ⟨y, hy, hyU⟩
  have hτUord : P₀.ordForm τU = -(m : ℤ) := by
    have := hgen.2 P₀ hUP₀
    rw [hB₀, mul_one] at this
    have : ((P₀.ordForm τU : ℤ) : ℚ) = ((-(m : ℤ) : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hsp : ∀ Γ : Mori.PrimeDivisor Y, y ∈ (Γ.support : Set Y) → Γ.genericPoint ⤳ y := by
    intro Γ hΓ
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
    exact specializes_iff_mem_closure.mpr hΓ
  -- the line of `m`-canonical forms
  have hrank : Module.finrank Y.functionField (RationalPluriForms sY 3 m) = 1 :=
    finrank_rationalPluriForms_eq_one_of_topologicalKrullDim sY (d := 3) (by rw [hY]; rfl) _
  obtain ⟨q, hq⟩ := (finrank_eq_one_iff_of_nonzero' τU hτU0).mp hrank τ
  obtain ⟨M', rfl⟩ : ∃ M', m = M' + 1 := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hτpole : τ = 0 ∨ -((M' + 1 : ℕ) : ℤ) ≤ P₀.ordForm τ := by
    by_cases hτ0 : τ = 0
    · exact Or.inl hτ0
    right
    have := le_ordForm_of_mem_logPluricanonicalSections hmB hτ hτ0 P₀
    rw [hB₀, mul_one] at this
    exact_mod_cast this
  have hsub := isPoincareResidue_sub (n := 2) sY (by rw [hY]; rfl) j hT P₀ hjT M' hτpole
    (Or.inr hτUord.ge) hρ hρU
  -- generation of `τ_U` along the primes through `y`
  have hgenU : ∀ Γ : Mori.PrimeDivisor Y, y ∈ (Γ.support : Set Y) →
      (Γ.ordForm τU : ℚ) + ((M' + 1 : ℕ) : ℚ) * B.coeff Γ = 0 :=
    fun Γ hΓ => hgen.2 Γ ⟨y, hΓ, hyU⟩
  rcases hsub with heq | hsub
  · exact ⟨heq ▸ hτU0, fun Γ hΓ => heq ▸ hgenU Γ hΓ⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hq
    rw [← hq, zero_sub, PrimeDivisor.ordForm_neg, hτUord] at hsub
    omega
  have hτ0 : τ ≠ 0 := by
    rw [← hq]; exact smul_ne_zero hq0 hτU0
  refine ⟨hτ0, ?_⟩
  by_cases hq1 : q = 1
  · rw [hq1, one_smul] at hq
    exact fun Γ hΓ => hq ▸ hgenU Γ hΓ
  have hq10 : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have hordq1 : 1 ≤ Y.ord (q - 1) P₀.genericPoint := by
    have : τ - τU = (q - 1) • τU := by rw [sub_smul, one_smul, hq]
    rw [this, P₀.ordForm_smul (sX := sY) hd hq10 hτU0, hτUord] at hsub
    omega
  have hordq : ∀ Γ : Mori.PrimeDivisor Y, y ∈ (Γ.support : Set Y) →
      0 ≤ Y.ord q Γ.genericPoint := by
    intro Γ hΓ
    have h1 := le_ordForm_of_mem_logPluricanonicalSections hmB hτ hτ0 Γ
    have h2 := hgenU Γ hΓ
    rw [← hq, Γ.ordForm_smul (sX := sY) hd hq0 hτU0] at h1
    push_cast at h1 h2
    have : (0 : ℚ) ≤ (Y.ord q Γ.genericPoint : ℚ) := by linarith
    exact_mod_cast this
  obtain ⟨c, hc⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord y hq0
    hordq
  -- `c` is a unit at `y`
  have hcu : IsUnit c := by
    by_contra hcu
    have hc1 : IsUnit (c - 1) := by
      by_contra h1
      have hm1 : c - 1 ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
        (IsLocalRing.mem_maximalIdeal _).mpr h1
      have hmc : c ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
        (IsLocalRing.mem_maximalIdeal _).mpr hcu
      have := Ideal.sub_mem _ hmc hm1
      rw [sub_sub_cancel] at this
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have hu := hc1.map (Y.presheaf.stalkSpecializes (hsp P₀ hy)).hom
    have h0 := P₀.ord_algebraMap_of_isUnit hu
    rw [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes', map_sub, map_one, hc] at h0
    omega
  intro Γ hΓ
  have hu := hcu.map (Y.presheaf.stalkSpecializes (hsp Γ hΓ)).hom
  have h0 := Γ.ord_algebraMap_of_isUnit hu
  rw [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes', hc] at h0
  rw [← hq, Γ.ordForm_smul (sX := sY) hd hq0 hτU0, h0, zero_add]
  exact hgenU Γ hΓ

/-- **Cartier descent of the adjoint.** In the two-floor Mori setting, for every sufficiently
divisible `m > 0` there are a nonzero rational `m`-canonical form `α` on `Y` and a Cartier
divisor `M` on `V` with `div α + mB = r^*M`, and `mB` is integral. -/
private theorem exists_descentForm
    {k : Type} [Field k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {r : Y ⟶ V} {K : Divisor Y} {Γ : QDivisor Y}
    (hr : IsMoriFibreSpace sY sV K Γ r) (hΓ : MMP.Fourfold.IsKltPair sY Γ) (hQ : IsQFactorial sY)
    (hY : topologicalKrullDim Y = 3) (hV : topologicalKrullDim V = 2)
    {B : QDivisor Y} (hlc : MMP.Intersection.IsLogCanonicalPair sY B)
    (hnef : QDivisor.IsRelativelyNef sY r (Divisor.toQDivisor K + B))
    (hnef' : QDivisor.IsRelativelyNef sY r (-(Divisor.toQDivisor K + B)))
    (hklt : ∃ ε : ℚ, 0 < ε ∧ MMP.Fourfold.IsKltPair sY (B - ε • Divisor.toQDivisor B.roundDown))
    {F : {P : Mori.PrimeDivisor Y // B.coeff P = 1} → Scheme.{0}} [∀ P, IsIntegral (F P)]
    (j : ∀ P, F P ⟶ Y) [∀ P, IsClosedImmersion (j P)]
    (hj : ∀ P, Set.range (j P).base = (P.1.support : Set Y))
    (hdeg : ∑ᶠ (P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}) (_ : IsDominant (j P ≫ r)),
      (letI : IsDominant (j P ≫ r) := ‹_›
       letI := functionFieldMapAlgebra (j P ≫ r)
       Module.finrank V.functionField (F P).functionField) = 2) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m →
      (∀ P, ((m : ℚ) * B.coeff P).den = 1) ∧
      ∃ (α : RationalPluriForms sY 3 m) (M : Divisor V) (hM : M.IsCartier)
        (hrM : ∀ W : irreducibleComponents Y, r (componentGenericPoint Y W) ∉ M.supp)
        (rM : Divisor Y), M.IsPullback r hrM rM ∧ α ≠ 0 ∧
        (∀ P : Mori.PrimeDivisor Y, (P.ordForm α : ℚ) + (m : ℚ) * B.coeff P = (rM.coeff P : ℚ)) ∧
        ∃ ω : RationalPluriForms sV 2 m, ω ≠ 0 ∧
        ∀ (U : Scheme.{0}) [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
          (p : U ⟶ Y) [IsDominant p] (Δ : QDivisor U), IsProjectiveMorphism p →
          (∃ (KY : Divisor Y) (hU : IsNormalVariety k (p ≫ sY)) (hp : IsBirationalMorphism p),
            IsCrepantBoundary sY 3 KY B p hU hp Δ) →
          MMP.Intersection.IsDltPair (p ≫ sY) Δ →
          -- the residues of `p^*α` on the horizontal floor branches are pull-backs of `ω`
          (∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
            (j : S ⟶ U) (BS : QDivisor S) [IsDominant (j ≫ p ≫ r)],
            IsAdjunctionStep (p ≫ sY) Δ j BS →
            ∀ (ψ : FunctionFieldHom (p ≫ sY) sY) (φ : FunctionFieldHom (j ≫ p ≫ sY) sV),
              (∀ x, ψ x = functionFieldMap p x) →
              (∀ x, φ x = functionFieldMap (j ≫ p ≫ r) x) →
              IsPoincareResidue (p ≫ sY) j 2 m (pluriformPullback (p ≫ sY) sY ψ 3 m α)
                (pluriformPullback (j ≫ p ≫ sY) sV φ 2 m ω)) ∧
          -- the Stein degrees of the horizontal floor of `Δ` sum to two
          (open scoped Classical in
            ∑ P ∈ Δ.support with Δ P = 1 ∧ (p ≫ r).base '' (P.support : Set U) = Set.univ,
              (letI := ((p ≫ r).residueFieldMap P.genericPoint).hom.toAlgebra;
                Module.finrank (V.residueField ((p ≫ r) P.genericPoint))
                  (U.residueField P.genericPoint)) = 2) ∧
          -- two distinct horizontal branches are crepant birationally identified over `V`
          (∀ (S₁ : Scheme.{0}) [IsIntegral S₁] [IsLocallyNoetherian S₁] [IsNormal S₁]
            (j₁ : S₁ ⟶ U) (B₁ : QDivisor S₁) [IsDominant (j₁ ≫ p ≫ r)]
            (S₂ : Scheme.{0}) [IsIntegral S₂] [IsLocallyNoetherian S₂] [IsNormal S₂]
            (j₂ : S₂ ⟶ U) (B₂ : QDivisor S₂) [IsDominant (j₂ ≫ p ≫ r)],
            IsAdjunctionStep (p ≫ sY) Δ j₁ B₁ → IsAdjunctionStep (p ≫ sY) Δ j₂ B₂ →
            Set.range j₁.base ≠ Set.range j₂.base →
            ∃ σ : FunctionFieldEquiv (j₁ ≫ p ≫ sY) (j₂ ≫ p ≫ sY),
              IsCrepantBirationalMap (j₁ ≫ p ≫ sY) (j₂ ≫ p ≫ sY) B₁ B₂ σ ∧
              ∀ x : V.functionField,
                σ (functionFieldMap (j₂ ≫ p ≫ r) x) = functionFieldMap (j₁ ≫ p ≫ r) x) ∧
          -- a horizontal branch of degree two has a crepant involution over `V`
          (∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
            (j : S ⟶ U) (BS : QDivisor S) [IsDominant (j ≫ p ≫ r)],
            IsAdjunctionStep (p ≫ sY) Δ j BS →
            (letI := functionFieldMapAlgebra (j ≫ p ≫ r);
              Module.finrank V.functionField S.functionField) = 2 →
            ∃ σ : FunctionFieldEquiv (j ≫ p ≫ sY) (j ≫ p ≫ sY),
              σ ≠ 1 ∧ σ * σ = 1 ∧
              IsCrepantBirationalMap (j ≫ p ≫ sY) (j ≫ p ≫ sY) BS BS σ ∧
              ∀ x : V.functionField,
                σ (functionFieldMap (j ≫ p ≫ r) x) = functionFieldMap (j ≫ p ≫ r) x) := by
  classical
  have hYv := hr.isProjectiveVariety
  haveI : QuasiCompact sY := hYv.toQuasiCompact
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.isContraction.isProjectiveMorphism
  obtain ⟨n, hK⟩ := hr.isCanonicalDivisor
  have hD := isNumericallyTrivialOver_of_isRelativelyNef hnef hnef'
  have hdeg' := sum_residueDegree_eq_two (sY := sY) j hj hdeg
  haveI : IsAlgClosed k := hΓ.1.isAlgClosed
  haveI : CharZero k := hΓ.1.charZero
  obtain ⟨m₁, hm₁, hdesc⟩ :=
    MMP.Fourfold.TwoFloorK.IsContraction.exists_isPoincareResidue_of_floor_degree_eq_two
    hr.isContraction hYv hr.isProjectiveVariety_target hY hV hQ hr.relativePicardNumber_eq_one hK
    hΓ hr.hasRelativelyAmpleMultiple hlc hD hklt hdeg'
  set D : ℕ := ∏ P ∈ B.support, (B.coeff P).den with hDdef
  have hDpos : 0 < D := Finset.prod_pos fun P _ => (B.coeff P).den_pos
  refine ⟨2 * m₁ * D, by positivity, fun m hm hdvd => ⟨fun P => ?_, ?_⟩⟩
  · by_cases hP : P ∈ B.support
    · have hden : (B.coeff P).den ∣ m :=
        (Finset.dvd_prod_of_mem _ hP).trans ((Dvd.intro_left _ rfl).trans hdvd)
      obtain ⟨c, hc⟩ := hden
      have : (m : ℚ) * B.coeff P = ((c * (B.coeff P).num : ℤ) : ℚ) := by
        rw [hc]
        push_cast
        rw [mul_comm ((B.coeff P).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
      rw [this, Rat.den_intCast]
    · have : B.coeff P = 0 := Finsupp.notMem_support_iff.mp hP
      rw [this, mul_zero]
      rfl
  · have heven : Even m :=
      even_iff_two_dvd.mpr ((Dvd.intro _ (mul_assoc 2 m₁ D).symm).trans hdvd)
    have hm₁d : m₁ ∣ m := (Dvd.intro (2 * D) (by ring : m₁ * (2 * D) = 2 * m₁ * D)).trans hdvd
    obtain ⟨α, ω, M, hM, hrM, hα, hω, hord, hlift⟩ := hdesc m hm hm₁d heven
    exact ⟨α, M, hM, hrM, _, Divisor.isPullback_pullback hM hrM, hα, hord, ω, hω,
      hlift⟩

/-- **Uniqueness of the extension.** In the two-floor Mori setting, with `div α + mB = r^*M`, two
global sections of `m(K_Y + B)` having the same Poincaré residues along every floor prime agree:
their difference has no residue on the horizontal floor, which dominates `V`. -/
private theorem eq_of_forall_isPoincareResidue
    {k : Type} [Field k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {r : Y ⟶ V} {K : Divisor Y} {Γ : QDivisor Y}
    (hr : IsMoriFibreSpace sY sV K Γ r) (hΓ : MMP.Fourfold.IsKltPair sY Γ)
    (hY : topologicalKrullDim Y = 3) (hV : topologicalKrullDim V = 2) {B : QDivisor Y}
    {F : {P : Mori.PrimeDivisor Y // B.coeff P = 1} → Scheme.{0}} [∀ P, IsIntegral (F P)]
    (j : ∀ P, F P ⟶ Y) [∀ P, IsClosedImmersion (j P)]
    (hj : ∀ P, Set.range (j P).base = (P.1.support : Set Y))
    (hdeg : ∑ᶠ (P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}) (_ : IsDominant (j P ≫ r)),
      (letI : IsDominant (j P ≫ r) := ‹_›
       letI := functionFieldMapAlgebra (j P ≫ r)
       Module.finrank V.functionField (F P).functionField) = 2)
    {m : ℕ} (hm : 0 < m) (α : RationalPluriForms sY 3 m) (M : Divisor V) (hM : M.IsCartier)
    (hrM : ∀ W : irreducibleComponents Y, r (componentGenericPoint Y W) ∉ M.supp)
    (rM : Divisor Y) (hrMp : M.IsPullback r hrM rM) (hα : α ≠ 0)
    (hαM : ∀ P : Mori.PrimeDivisor Y, (P.ordForm α : ℚ) + (m : ℚ) * B.coeff P = (rM.coeff P : ℚ))
    (hmB : ∀ P, ((m : ℚ) * B.coeff P).den = 1)
    (ρ : ∀ P, RationalPluriForms (j P ≫ sY) 2 m) {τ₁ τ₂ : RationalPluriForms sY 3 m}
    (h₁ : τ₁ ∈ logPluricanonicalSections sY 3 m B) (h₂ : τ₂ ∈ logPluricanonicalSections sY 3 m B)
    (hρ₁ : ∀ P, IsPoincareResidue sY (j P) 2 m τ₁ (ρ P))
    (hρ₂ : ∀ P, IsPoincareResidue sY (j P) 2 m τ₂ (ρ P)) : τ₁ = τ₂ := by
  classical
  haveI : CharZero k := hΓ.1.charZero
  have hYv := hr.isProjectiveVariety
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  -- a horizontal floor prime
  obtain ⟨P₀, hdom⟩ : ∃ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}, IsDominant (j P ≫ r) :=
    exists_of_finsum_finsum_ne_zero hdeg two_ne_zero
  have hjT := map_genericPoint_eq_of_range (j P₀) P₀.1 (hj P₀)
  have hP₀ : r P₀.1.genericPoint = genericPoint V := by
    rw [← hjT, ← Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
  haveI : LocallyOfFiniteType (j P₀ ≫ sY) := inferInstance
  have hT : topologicalKrullDim (F P₀) = 2 := by
    letI := functionFieldAlgebra sY
    letI := functionFieldAlgebra (j P₀ ≫ sY)
    have h1 := trdeg_add_one_of_eq_genericPoint (sY := sY) (j := j P₀) P₀.1 hjT
    have h2 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (d := 3)
      (by rw [hY]; rfl)
    rw [topologicalKrullDim_eq_toNat_trdeg (j P₀ ≫ sY)]
    have : (Algebra.trdeg k (F P₀).functionField).toNat = 2 := by omega
    rw [this]
    rfl
  obtain ⟨M', rfl⟩ : ∃ M', m = M' + 1 := Nat.exists_eq_succ_of_ne_zero hm.ne'
  -- the forms have at most an `m`-fold pole along `P₀`
  have hpole : ∀ τ : RationalPluriForms sY 3 ((M' + 1 : ℕ) : ℤ),
      τ ∈ logPluricanonicalSections sY 3 (M' + 1) B →
        τ = 0 ∨ -((M' + 1 : ℕ) : ℤ) ≤ P₀.1.ordForm τ := by
    intro τ hτ
    by_cases hτ0 : τ = 0
    · exact Or.inl hτ0
    right
    have := (mem_logPluricanonicalSections (sX := sY)).mp hτ |>.2 P₀.1
      ((P₀.1.genericPoint_mem_iff ⊤).mp trivial) hτ0
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, P₀.2, zsmul_eq_mul,
      mul_one] at this
    have h3 : ⌊(((M' + 1 : ℕ) : ℤ) : ℚ)⌋ = ((M' + 1 : ℕ) : ℤ) := Int.floor_intCast _
    rw [h3] at this
    omega
  have hsub := isPoincareResidue_sub (n := 2) sY (by rw [hY]; rfl) (j P₀) hT P₀.1 hjT M'
    (hpole τ₁ h₁) (hpole τ₂ h₂) (hρ₁ P₀) (hρ₂ P₀)
  rcases hsub with h | h
  · exact h
  have := eq_zero_of_le_ordForm hr.isContraction hY α M hrM rM hrMp hα hαM hmB
    (sub_mem h₁ h₂) P₀.1 P₀.2 hP₀ (Or.inr h)
  exact sub_eq_zero.mp this

/-- **Generation descends.** In the two-floor Mori setting, if every floor section `s a` extends
to a global section of `m(K_Y + B)` and the floor sections generate at every floor point, then
over a neighbourhood of every point of `V` some extension generates `m(K_Y + B)`: the descended
section of `M` does not vanish at the image point, so its pull-back generates over its preimage. -/
private theorem exists_generatesOn_of_forall_exists
    {k : Type} [Field k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {r : Y ⟶ V} {K : Divisor Y} {Γ : QDivisor Y}
    (hr : IsMoriFibreSpace sY sV K Γ r) (hΓ : MMP.Fourfold.IsKltPair sY Γ)
    (hY : topologicalKrullDim Y = 3) (hV : topologicalKrullDim V = 2) {B : QDivisor Y}
    {F : {P : Mori.PrimeDivisor Y // B.coeff P = 1} → Scheme.{0}} [∀ P, IsIntegral (F P)]
    (j : ∀ P, F P ⟶ Y) [∀ P, IsClosedImmersion (j P)]
    (hj : ∀ P, Set.range (j P).base = (P.1.support : Set Y))
    (hdeg : ∑ᶠ (P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}) (_ : IsDominant (j P ≫ r)),
      (letI : IsDominant (j P ≫ r) := ‹_›
       letI := functionFieldMapAlgebra (j P ≫ r)
       Module.finrank V.functionField (F P).functionField) = 2)
    {m : ℕ} (hm : 0 < m) (α : RationalPluriForms sY 3 m) (M : Divisor V) (hM : M.IsCartier)
    (hrM : ∀ W : irreducibleComponents Y, r (componentGenericPoint Y W) ∉ M.supp)
    (rM : Divisor Y) (hrMp : M.IsPullback r hrM rM) (hα : α ≠ 0)
    (hαM : ∀ P : Mori.PrimeDivisor Y, (P.ordForm α : ℚ) + (m : ℚ) * B.coeff P = (rM.coeff P : ℚ))
    (hmB : ∀ P, ((m : ℚ) * B.coeff P).den = 1)
    {A : Type v} (s : A → ∀ P, RationalPluriForms (j P ≫ sY) 2 m)
    (hext : ∀ a, ∃ τ : RationalPluriForms sY 3 m, τ ∈ logPluricanonicalSections sY 3 m B ∧
      ∀ P, IsPoincareResidue sY (j P) 2 m τ (s a P))
    (hgen : ∀ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}, ∀ y ∈ (P.1.support : Set Y),
      ∃ (a : A) (U : Y.Opens), y ∈ U ∧
        ∃ τ ∈ pluricanonicalSections sY 3 m (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) U,
          GeneratesOn B m U τ ∧ ∀ P₁, ((P₁.1.support : Set Y) ∩ U).Nonempty →
            IsPoincareResidue sY (j P₁) 2 m τ (s a P₁)) (v : V) :
    ∃ (a : A) (τ : RationalPluriForms sY 3 m),
      τ ∈ logPluricanonicalSections sY 3 m B ∧
      (∀ P, IsPoincareResidue sY (j P) 2 m τ (s a P)) ∧
      ∃ U : V.Opens, v ∈ U ∧ GeneratesOn B m (r ⁻¹ᵁ U) τ := by
  classical
  haveI : CharZero k := hΓ.1.charZero
  have hYv := hr.isProjectiveVariety
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.isContraction.isProjectiveMorphism
  haveI : IsDominant r := ⟨hr.isContraction.surjective.denseRange⟩
  letI := functionFieldAlgebra sY
  have hd : (Algebra.trdeg k Y.functionField).toNat = 3 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; rfl)
  -- a horizontal floor prime, which surjects onto `V`
  obtain ⟨P₀, hdom⟩ : ∃ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}, IsDominant (j P ≫ r) :=
    exists_of_finsum_finsum_ne_zero hdeg two_ne_zero
  have hjT := map_genericPoint_eq_of_range (j P₀) P₀.1 (hj P₀)
  haveI : LocallyOfFiniteType (j P₀ ≫ sY) := inferInstance
  have hT : topologicalKrullDim (F P₀) = 2 := by
    letI := functionFieldAlgebra (j P₀ ≫ sY)
    have h1 := trdeg_add_one_of_eq_genericPoint (sY := sY) (j := j P₀) P₀.1 hjT
    rw [topologicalKrullDim_eq_toNat_trdeg (j P₀ ≫ sY)]
    have : (Algebra.trdeg k (F P₀).functionField).toNat = 2 := by omega
    rw [this]
    rfl
  obtain ⟨y, hy, hyv⟩ : ∃ y ∈ (P₀.1.support : Set Y), r y = v := by
    have hrange : Set.range (j P₀ ≫ r).base = r.base '' (P₀.1.support : Set Y) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hj]
    have hcl : IsClosed (r.base '' (P₀.1.support : Set Y)) :=
      r.isClosedMap _ (hj P₀ ▸ (j P₀).isClosedEmbedding.isClosed_range)
    have hdense := hdom.denseRange
    rw [DenseRange, hrange] at hdense
    have huniv := hcl.closure_eq ▸ hdense.closure_eq
    have hv : v ∈ r.base '' (P₀.1.support : Set Y) := huniv ▸ Set.mem_univ v
    obtain ⟨y, hy, hyv⟩ := hv
    exact ⟨y, hy, hyv⟩
  -- the floor sections generating at `y`, and the extension of the chosen one
  obtain ⟨a, U, hyU, τU, -, hgenU, hresU⟩ := hgen P₀ y hy
  obtain ⟨τ, hτ, hτres⟩ := hext a
  obtain ⟨hτ0, hloc⟩ := ordForm_add_eq_zero_of_generatesOn hY hm hmB (j P₀) hT P₀.1 P₀.2 (hj P₀)
    hy hyU hgenU hτ (hτres P₀) (hresU P₀ ⟨y, hy, hyU⟩)
  refine ⟨a, τ, hτ, hτres, ?_⟩
  -- `τ = h α`
  have hrank : Module.finrank Y.functionField (RationalPluriForms sY 3 m) = 1 :=
    finrank_rationalPluriForms_eq_one_of_topologicalKrullDim sY (d := 3) (by rw [hY]; rfl) _
  obtain ⟨h, hh⟩ := (finrank_eq_one_iff_of_nonzero' α hα).mp hrank τ
  have hh0 : h ≠ 0 := by rintro rfl; exact hτ0 (by rw [← hh, zero_smul])
  have hG : ∀ Γ : Mori.PrimeDivisor Y, (Γ.ordForm τ : ℚ) + (m : ℚ) * B.coeff Γ =
      (Y.ord h Γ.genericPoint : ℚ) + (rM.coeff Γ : ℚ) := by
    intro Γ
    rw [← hh, Γ.ordForm_smul (sX := sY) hd hh0 hα, ← hαM Γ]
    push_cast
    ring
  -- a local equation of `M` near `v`
  obtain ⟨W, hvW, φ, hφ⟩ := hM v
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents V) :=
    ⟨⟨Set.univ, (irreducibleComponents_eq_singleton (X := V)).symm ▸ rfl⟩⟩
  set φ₀ := MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions V) with hφ₀
  have hφ₀0 : φ₀ ≠ 0 := (φ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z)).ne_zero
  have hrφ₀0 : functionFieldMap r φ₀ ≠ 0 := (map_ne_zero _).mpr hφ₀0
  set H := h * functionFieldMap r φ₀ with hHdef
  have hH0 : H ≠ 0 := mul_ne_zero hh0 hrφ₀0
  have hHG : ∀ Γ : Mori.PrimeDivisor Y, (Γ.support ∩ r ⁻¹ᵁ W).Nonempty →
      (Y.ord H Γ.genericPoint : ℚ) = (Γ.ordForm τ : ℚ) + (m : ℚ) * B.coeff Γ := by
    intro Γ hΓ
    rw [hG Γ, coeff_eq_ord_of_isPullback hrMp hφ Γ hΓ Z, hHdef, Scheme.ord_mul hh0 hrφ₀0]
    push_cast
    ring
  have hyW : y ∈ r ⁻¹ᵁ W := by
    change r y ∈ W
    rw [hyv]; exact hvW
  haveI : Nonempty (r ⁻¹ᵁ W) := ⟨⟨y, hyW⟩⟩
  obtain ⟨g, hg⟩ := exists_app_eq_of_zero_le_ord hr.isContraction W H fun Γ hΓ => by
    have h1 := hHG Γ hΓ
    have h2 := le_ordForm_of_mem_logPluricanonicalSections hmB hτ hτ0 Γ
    have : (0 : ℚ) ≤ (Y.ord H Γ.genericPoint : ℚ) := by linarith
    exact_mod_cast this
  -- `H` is a unit at `y`, so `g` is a unit at `v`
  have hHy : ∀ Γ : Mori.PrimeDivisor Y, y ∈ (Γ.support : Set Y) → Y.ord H Γ.genericPoint = 0 := by
    intro Γ hΓ
    have := hHG Γ ⟨y, hΓ, hyW⟩
    rw [hloc Γ hΓ] at this
    exact_mod_cast this
  obtain ⟨u, hu, huH⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero y hH0 hHy
  have hry : r y ∈ W := hyW
  have hst : algebraMap (Y.presheaf.stalk y) Y.functionField
      ((r.stalkMap y).hom (V.presheaf.germ W (r y) hry g)) = H := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hyW (r.app W g)).trans hg
  have hueq : (r.stalkMap y).hom (V.presheaf.germ W (r y) hry g) = u :=
    IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField (hst.trans huH.symm)
  have hgu : IsUnit (V.presheaf.germ W (r y) hry g) :=
    isUnit_of_map_unit (r.stalkMap y).hom _ (hueq ▸ hu)
  refine ⟨V.basicOpen g, ?_, hτ0, fun Γ hΓ => ?_⟩
  · rw [← hyv]; exact (V.mem_basicOpen g (r y) hry).mpr hgu
  -- along a prime meeting `r⁻¹ D(g)`, the function `H` is a unit
  have hηΓ : Γ.genericPoint ∈ r ⁻¹ᵁ V.basicOpen g := (Γ.genericPoint_mem_iff _).mpr hΓ
  have hηW : r Γ.genericPoint ∈ W := V.basicOpen_le g hηΓ
  have hgη : IsUnit (V.presheaf.germ W (r Γ.genericPoint) hηW g) :=
    (V.mem_basicOpen g _ hηW).mp hηΓ
  have hstΓ : algebraMap (Y.presheaf.stalk Γ.genericPoint) Y.functionField
      ((r.stalkMap Γ.genericPoint).hom (V.presheaf.germ W (r Γ.genericPoint) hηW g)) = H := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (Scheme.algebraMap_germ_eq_germToFunctionField (X := Y)
      (show Γ.genericPoint ∈ r ⁻¹ᵁ W from hηW) (r.app W g)).trans hg
  have h0 := Γ.ord_algebraMap_of_isUnit (hgη.map (r.stalkMap Γ.genericPoint).hom)
  rw [hstΓ] at h0
  have hΓW : (Γ.support ∩ r ⁻¹ᵁ W).Nonempty := (Γ.genericPoint_mem_iff _).mp hηW
  rw [← hHG Γ hΓW, h0]
  rfl

/-- Specialization between two equal points reflects units. -/
private theorem isUnit_of_isUnit_stalkSpecializes {V : Scheme.{0}} {v w : V} (hvw : v = w)
    (h : w ⤳ v) (b : V.presheaf.stalk v) (hb : IsUnit ((V.presheaf.stalkSpecializes h).hom b)) :
    IsUnit b := by
  subst hvw
  rwa [TopCat.Presheaf.stalkSpecializes_refl] at hb

/-- The `k`-algebra structure of a stalk is pulled back along a morphism over `k`. -/
private theorem algebraMap_stalkAlgebra_comp {k : Type} [Field k] {F V : Scheme.{0}}
    {sF : F ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} (f : F ⟶ V) (hf : f ≫ sV = sF) (y : F)
    (c : k) :
    (letI := stalkAlgebra sF y; algebraMap k (F.presheaf.stalk y) c) =
      (f.stalkMap y).hom (letI := stalkAlgebra sV (f y); algebraMap k _ c) := by
  subst hf
  simp only [stalkAlgebra, RingHom.algebraMap_toAlgebra]
  rw [Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- **Detection on a proper fibre.** Let `f : F ⟶ V` be a proper morphism of varieties over `k`
and `ξ = f(η_F)`. A rational function `g` on `F` which is regular at every point of the fibre
`f⁻¹(ξ)` and vanishes at one of them is zero. Every valuation ring of `k(F)` containing the image
`L ≅ κ(ξ)` of `𝒪_{V,ξ}` has a centre on the fibre (valuative criterion), so contains `g`; hence `g`
is integral over the field `L`, and the constant term of its minimal polynomial, a nonzero
element of `L` and so a unit at the point, is a multiple of `g`. -/
private theorem eq_zero_of_isProper_of_mem_maximalIdeal {k : Type} [Field k] {F V : Scheme.{0}}
    {sF : F ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} (hF : Mori.IsVariety k sF)
    (hV : Mori.IsVariety k sV) (f : F ⟶ V) [IsProper f] (hf : f ≫ sV = sF) :
    haveI : IsIntegral F := hF.toIsIntegral
    ∀ (g : F.functionField),
      (∀ x : F, f x = f (genericPoint F) →
        ∃ a : F.presheaf.stalk x, algebraMap _ F.functionField a = g) →
      ∀ (y : F), f y = f (genericPoint F) → ∀ a : F.presheaf.stalk y,
        algebraMap _ F.functionField a = g → a ∈ IsLocalRing.maximalIdeal _ → g = 0 := by
  haveI : IsIntegral F := hF.toIsIntegral
  haveI : IsIntegral V := hV.toIsIntegral
  intro g hreg y hy a ha hm
  by_contra hg0
  have hηy : genericPoint F ⤳ y := (genericPoint_spec F).specializes (Set.mem_univ y)
  have h1 : f (genericPoint F) ⤳ f y := hηy.map f.base.hom.continuous
  -- the composite `𝒪_{V, f y} → 𝒪_{F, y} → k(F)`
  let ψ : V.presheaf.stalk (f y) →+* F.functionField :=
    (algebraMap (F.presheaf.stalk y) F.functionField).comp (f.stalkMap y).hom
  have hψ : ∀ b, (V.presheaf.stalkSpecializes h1 ≫ f.stalkMap (genericPoint F)).hom b = ψ b := by
    intro b
    have := Scheme.Hom.stalkSpecializes_stalkMap f (genericPoint F) y hηy
    exact congrArg (fun φ => φ.hom b) this
  have hψu : ∀ b, ψ b ≠ 0 → IsUnit b := by
    intro b hb
    rw [← hψ, CommRingCat.comp_apply] at hb
    exact isUnit_of_isUnit_stalkSpecializes hy _ _ (isUnit_of_map_unit _ _ (Ne.isUnit hb))
  -- its image is a subfield `L` of `k(F)`
  let L : Subfield F.functionField :=
    { ψ.range with
      inv_mem' := by
        rintro _ ⟨b, rfl⟩
        by_cases hb : ψ b = 0
        · exact ⟨0, by rw [map_zero, hb, inv_zero]⟩
        obtain ⟨u, rfl⟩ := hψu b hb
        exact ⟨(u⁻¹ : (V.presheaf.stalk (f y))ˣ), by
          rw [← map_units_inv]⟩ }
  have hLmem : ∀ z ∈ L, ∃ b, ψ b = z := fun z hz => hz
  have hkL : ∀ c : k, (letI := functionFieldAlgebra sF;
      algebraMap k F.functionField c) ∈ L := by
    intro c
    letI := stalkAlgebra sF y
    letI := functionFieldAlgebra sF
    haveI := isScalarTower_stalk_functionField sF y
    rw [IsScalarTower.algebraMap_apply k (F.presheaf.stalk y) F.functionField,
      algebraMap_stalkAlgebra_comp f hf y c]
    exact ⟨_, rfl⟩
  -- every valuation ring containing `L` has a centre on the fibre, hence contains `g`
  have hval : ∀ R : ValuationSubring F.functionField, (L : Set F.functionField) ⊆ R → g ∈ R := by
    intro R hR
    have hle1 : ∀ b, R.valuation
        ((V.presheaf.stalkSpecializes h1 ≫ f.stalkMap (genericPoint F)).hom b) ≤ 1 := by
      intro b
      rw [hψ]
      exact (R.valuation_le_one_iff _).mpr (hR ⟨b, rfl⟩)
    have hlt1 : ∀ b ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk (f y)), R.valuation
        ((V.presheaf.stalkSpecializes h1 ≫ f.stalkMap (genericPoint F)).hom b) < 1 := by
      intro b hb
      have h0 : ψ b = 0 := by
        by_contra h0
        exact (IsLocalRing.mem_maximalIdeal _).mp hb (hψu b h0)
      rw [hψ, h0, map_zero]
      exact zero_lt_one
    obtain ⟨v, hv, hle, -⟩ := (MMP.existsUnique_center_of_isProper hF hV f hf).1 R
      (fun c => hR (hkL c)) (f y) h1 hle1 hlt1
    obtain ⟨b, hb⟩ := hreg v (hv.trans hy)
    rw [← hb]
    exact (R.valuation_le_one_iff _).mp (hle b)
  have hmem : g ∈ (⨅ R : {R : ValuationSubring F.functionField //
      (L : Set F.functionField) ⊆ R.toSubring}, R.1.toSubring) :=
    Subring.mem_iInf.mpr fun R => hval R.1 R.2
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral L g := by
    obtain ⟨p, hp, hpg⟩ := hmem
    have hle : Subring.closure (L : Set F.functionField) ≤ L.toSubring :=
      Subring.closure_le.mpr fun z hz => hz
    refine ⟨p.map (Subring.inclusion hle), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpg
  -- the constant term of the minimal polynomial is a unit at `y` and a multiple of `g`
  have hc := minpoly.coeff_zero_ne_zero hint hg0
  have hev := minpoly.aeval L g
  rw [← Polynomial.X_mul_divX_add (minpoly L g), map_add, map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C] at hev
  let S := (algebraMap (F.presheaf.stalk y) F.functionField).range
  have hgS : g ∈ S := ⟨a, ha⟩
  have hLS : ∀ z ∈ L, z ∈ S := by
    intro z hz
    obtain ⟨b, rfl⟩ := hLmem z hz
    exact ⟨_, rfl⟩
  have hq : Polynomial.aeval g (minpoly L g).divX ∈ S := by
    rw [Polynomial.aeval_eq_sum_range]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Subring.mul_mem _ (hLS _ (Subtype.prop _)) (Subring.pow_mem _ hgS _)
  obtain ⟨t, ht⟩ := hq
  obtain ⟨b0, hb0⟩ := hLmem _ ((minpoly L g).coeff 0).2
  have hb0ne : ψ b0 ≠ 0 := by
    rw [hb0]
    exact fun h => hc (Subtype.ext h)
  obtain ⟨u, hu⟩ := hψu b0 hb0ne
  have heq : (f.stalkMap y).hom b0 = -(a * t) := by
    apply IsFractionRing.injective (F.presheaf.stalk y) F.functionField
    change ψ b0 = _
    rw [hb0, map_neg, map_mul, ha, ht]
    change _ = -(g * _)
    rwa [eq_neg_iff_add_eq_zero, add_comm]
  have hmem' : (f.stalkMap y).hom b0 ∈ IsLocalRing.maximalIdeal (F.presheaf.stalk y) := by
    rw [heq]
    exact Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hm)
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem' (hu ▸ (u.isUnit.map _))

/-- **Detection of a floor section on a vertical floor prime.** Let `τ` be a global section of
`m(K_Y + B)`, with `div α + mB = r^*M`, and `E`, `P₀` floor primes. Suppose that near every point
of `E` the floor section `(s_E, s₀)` lifts to a local section of `m(K_Y + B)`, that `τ` has residue
`s₀` along `P₀`, and that `E ∩ P₀` contains a point `y` over `r(η_E)`. Then `τ` has residue `s_E`
along `E`. Writing all forms near the fibre over `ξ = r(η_E)` as multiples `h · α (r^*φ)⁻¹` of a
local generator, the difference of the coefficients of `τ` and of the local lifts restricts to one
function on `E`, regular along the proper fibre `E_ξ` and vanishing at `y`; it is zero by
`eq_zero_of_isProper_of_mem_maximalIdeal`. -/
private theorem isPoincareResidue_of_mem_support_inter
    {k : Type} [Field k] [CharZero k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    {sV : V ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [LocallyOfFiniteType sY] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    (hYv : Mori.IsVariety k sY) (hVv : Mori.IsVariety k sV)
    {r : Y ⟶ V} [IsProper r] [IsDominant r] (hrs : r ≫ sV = sY)
    (hY : topologicalKrullDim Y = 3) {B : QDivisor Y} {m : ℕ} (hm : 0 < m)
    (hmB : ∀ P, ((m : ℚ) * B.coeff P).den = 1)
    (α : RationalPluriForms sY 3 m) (M : Divisor V) (hM : M.IsCartier)
    (hrM : ∀ W : irreducibleComponents Y, r (componentGenericPoint Y W) ∉ M.supp)
    (rM : Divisor Y) (hrMp : M.IsPullback r hrM rM) (hα : α ≠ 0)
    (hαM : ∀ P : Mori.PrimeDivisor Y, (P.ordForm α : ℚ) + (m : ℚ) * B.coeff P = (rM.coeff P : ℚ))
    {T T₀ : Scheme.{0}} [IsIntegral T] [IsIntegral T₀] (j : T ⟶ Y) (j₀ : T₀ ⟶ Y)
    [IsClosedImmersion j] [IsClosedImmersion j₀]
    (hT : topologicalKrullDim T = 2) (hT₀ : topologicalKrullDim T₀ = 2)
    (E P₀ : Mori.PrimeDivisor Y) (hBE : B.coeff E = 1) (hB₀ : B.coeff P₀ = 1)
    (hjE : Set.range j.base = (E.support : Set Y))
    (hj₀ : Set.range j₀.base = (P₀.support : Set Y))
    (sE : RationalPluriForms (j ≫ sY) 2 m) (s₀ : RationalPluriForms (j₀ ≫ sY) 2 m)
    {y : Y} (hyE : y ∈ (E.support : Set Y)) (hy₀ : y ∈ (P₀.support : Set Y))
    (hry : r y = r E.genericPoint)
    (hloc : ∀ x ∈ (E.support : Set Y), ∃ U : Y.Opens, x ∈ U ∧
      ∃ τ ∈ pluricanonicalSections sY 3 m (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) U,
        IsPoincareResidue sY j 2 m τ sE ∧
          (((P₀.support : Set Y) ∩ U).Nonempty → IsPoincareResidue sY j₀ 2 m τ s₀))
    {τ : RationalPluriForms sY 3 m} (hτ : τ ∈ logPluricanonicalSections sY 3 m B)
    (hτ₀ : IsPoincareResidue sY j₀ 2 m τ s₀) : IsPoincareResidue sY j 2 m τ sE := by
  classical
  obtain ⟨M', rfl⟩ : ∃ M', m = M' + 1 := Nat.exists_eq_succ_of_ne_zero hm.ne'
  letI := functionFieldAlgebra sY
  have hd : (Algebra.trdeg k Y.functionField).toNat = 3 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; rfl)
  have hjT := map_genericPoint_eq_of_range j E hjE
  have hjT₀ := map_genericPoint_eq_of_range j₀ P₀ hj₀
  obtain ⟨y', rfl⟩ : ∃ y', j y' = y := by
    rw [← hjE] at hyE
    exact hyE
  -- the rank-one space of `m`-canonical forms
  have hrank : Module.finrank Y.functionField
      (RationalPluriForms sY 3 ((M' + 1 : ℕ) : ℤ)) = 1 :=
    finrank_rationalPluriForms_eq_one_of_topologicalKrullDim sY (d := 3) (by rw [hY]; rfl) _
  -- a local equation `φ` of `M` near `ξ = r(η_E)` and the local generator `α (r^*φ)⁻¹`
  obtain ⟨W, hξW, φ, hφ⟩ := hM (r E.genericPoint)
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents V) :=
    ⟨⟨Set.univ, (irreducibleComponents_eq_singleton (X := V)).symm ▸ rfl⟩⟩
  set φ₀ := MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions V) with hφ₀
  have hφ₀0 : φ₀ ≠ 0 := (φ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z)).ne_zero
  have hrφ₀0 : functionFieldMap r φ₀ ≠ 0 := (map_ne_zero _).mpr hφ₀0
  set gen := (functionFieldMap r φ₀)⁻¹ • α with hgendef
  have hgen0 : gen ≠ 0 := smul_ne_zero (inv_ne_zero hrφ₀0) hα
  have hmBint : ∀ Γ : Mori.PrimeDivisor Y,
      ((⌊((M' + 1 : ℕ) : ℤ) • B.coeff Γ⌋ : ℤ) : ℚ) = ((M' + 1 : ℕ) : ℚ) * B.coeff Γ := by
    intro Γ
    rw [zsmul_eq_mul, Int.cast_natCast]
    have hq := Rat.coe_int_num_of_den_eq_one (hmB Γ)
    conv_lhs => rw [← hq]
    rw [Int.floor_intCast]
    exact hq
  -- the coefficient of a local section along the local generator is regular
  have hcoef : ∀ (U : Y.Opens) (z : Y), z ∈ U → r z ∈ W →
      ∀ τ' ∈ pluricanonicalSections sY 3 ((M' + 1 : ℕ) : ℤ)
        (DivisorWithCoeffs.roundDown (((M' + 1 : ℕ) : ℤ) • B)) U,
      ∃ d : Y.presheaf.stalk z, τ' = algebraMap _ Y.functionField d • gen := by
    intro U z hzU hzW τ' hτ'
    by_cases hτ'0 : τ' = 0
    · exact ⟨0, by rw [hτ'0, map_zero, zero_smul]⟩
    obtain ⟨h', hh'⟩ := (finrank_eq_one_iff_of_nonzero' α hα).mp hrank τ'
    have hh'0 : h' ≠ 0 := by rintro rfl; exact hτ'0 (by rw [← hh', zero_smul])
    have hH0 : h' * functionFieldMap r φ₀ ≠ 0 := mul_ne_zero hh'0 hrφ₀0
    have hτ'H : τ' = (h' * functionFieldMap r φ₀) • gen := by
      rw [hgendef, smul_smul, mul_assoc, mul_inv_cancel₀ hrφ₀0, mul_one, hh']
    obtain ⟨d, hd'⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord z hH0
      fun Γ hΓ => by
        have hΓW : (Γ.support ∩ r ⁻¹ᵁ W).Nonempty := ⟨z, hΓ, hzW⟩
        have h1 := hτ'.2 Γ ⟨z, hΓ, hzU⟩ hτ'0
        rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at h1
        have h2 := hαM Γ
        have h3 := coeff_eq_ord_of_isPullback hrMp hφ Γ hΓW Z
        have h4 : Γ.ordForm τ' = Y.ord h' Γ.genericPoint + Γ.ordForm α := by
          rw [← hh', Γ.ordForm_smul (sX := sY) hd hh'0 hα]
        rw [Scheme.ord_mul hh'0 hrφ₀0, hφ₀, ← h3]
        have h1' : (0 : ℚ) ≤ ((Γ.ordForm τ' : ℤ) : ℚ) +
            ((⌊((M' + 1 : ℕ) : ℤ) • B.coeff Γ⌋ : ℤ) : ℚ) := by exact_mod_cast h1
        rw [hmBint, h4] at h1'
        push_cast at h1' h2
        have : (0 : ℚ) ≤ ((Y.ord h' Γ.genericPoint + rM.coeff Γ : ℤ) : ℚ) := by
          push_cast; linarith
        exact_mod_cast this
    exact ⟨d, by rw [hd', hτ'H]⟩
  -- the local generator has a pole of order exactly `m` along the floor primes near `ξ`
  have hgenord : ∀ Q : Mori.PrimeDivisor Y, B.coeff Q = 1 → (Q.support ∩ r ⁻¹ᵁ W).Nonempty →
      Q.ordForm gen = -((M' + 1 : ℕ) : ℤ) := by
    intro Q hBQ hQW
    have h3 := coeff_eq_ord_of_isPullback hrMp hφ Q hQW Z
    have h2 := hαM Q
    rw [hBQ, mul_one] at h2
    have hinv : Y.ord (functionFieldMap r φ₀)⁻¹ Q.genericPoint =
        -Y.ord (functionFieldMap r φ₀) Q.genericPoint := by
      have := Scheme.ord_mul (inv_ne_zero hrφ₀0) hrφ₀0 (x := Q.genericPoint)
      rw [inv_mul_cancel₀ hrφ₀0, Scheme.ord_one] at this
      omega
    rw [hgendef, Q.ordForm_smul (sX := sY) hd (inv_ne_zero hrφ₀0) hα, hinv, hφ₀, ← h3]
    have : ((Q.ordForm α : ℤ) : ℚ) = ((rM.coeff Q - ((M' + 1 : ℕ) : ℤ) : ℤ) : ℚ) := by
      push_cast at h2 ⊢; linarith
    have := Int.cast_injective this
    omega
  have hyW : r (j y') ∈ W := by rw [hry]; exact hξW
  have hEW : (E.support ∩ r ⁻¹ᵁ W).Nonempty := ⟨j y', hyE, hyW⟩
  have h₀W : (P₀.support ∩ r ⁻¹ᵁ W).Nonempty := ⟨j y', hy₀, hyW⟩
  obtain ⟨ρE, hρE, hρE0⟩ := exists_isPoincareResidue sY (n := 2) (by rw [hY]; rfl) j hT E hjT M'
    (Or.inr (hgenord E hBE hEW).ge)
  have hρE0' := hρE0 hgen0 (hgenord E hBE hEW)
  obtain ⟨ρ₀, hρ₀, hρ₀0⟩ := exists_isPoincareResidue sY (n := 2) (by rw [hY]; rfl) j₀ hT₀ P₀ hjT₀
    M' (Or.inr (hgenord P₀ hB₀ h₀W).ge)
  have hρ₀0' := hρ₀0 hgen0 (hgenord P₀ hB₀ h₀W)
  -- residues of regular multiples of the local generator
  have hspE : ∀ z ∈ (E.support : Set Y), j (genericPoint T) ⤳ z := fun z hz =>
    (specializes_of_eq hjT).trans (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
      exact specializes_iff_mem_closure.mpr hz)
  have hsp₀ : ∀ z ∈ (P₀.support : Set Y), j₀ (genericPoint T₀) ⤳ z := fun z hz =>
    (specializes_of_eq hjT₀).trans (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
      exact specializes_iff_mem_closure.mpr hz)
  have hresE : ∀ (z : Y) (hz : j (genericPoint T) ⤳ z) (d : Y.presheaf.stalk z),
      IsPoincareResidue sY j 2 (M' + 1) (algebraMap _ Y.functionField d • gen)
        ((j.stalkMap (genericPoint T)).hom ((Y.presheaf.stalkSpecializes hz).hom d) • ρE) := by
    intro z hz d
    have := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρE
      ((Y.presheaf.stalkSpecializes hz).hom d)
    rwa [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' Y hz d] at this
  have hres₀ : ∀ (z : Y) (hz : j₀ (genericPoint T₀) ⤳ z) (d : Y.presheaf.stalk z),
      IsPoincareResidue sY j₀ 2 (M' + 1) (algebraMap _ Y.functionField d • gen)
        ((j₀.stalkMap (genericPoint T₀)).hom ((Y.presheaf.stalkSpecializes hz).hom d) • ρ₀) := by
    intro z hz d
    have := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ₀
      ((Y.presheaf.stalkSpecializes hz).hom d)
    rwa [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' Y hz d] at this
  have hτtop : τ ∈ pluricanonicalSections sY 3 ((M' + 1 : ℕ) : ℤ)
      (DivisorWithCoeffs.roundDown (((M' + 1 : ℕ) : ℤ) • B)) ⊤ := hτ
  -- restriction to `E` read at the generic point
  have hcompat : ∀ (x' : T) (e : Y.presheaf.stalk (j x')),
      algebraMap _ T.functionField ((j.stalkMap x').hom e) =
        (j.stalkMap (genericPoint T)).hom
          ((Y.presheaf.stalkSpecializes (hspE (j x') (hjE ▸ ⟨x', rfl⟩))).hom e) := by
    intro x' e
    have hηx : genericPoint T ⤳ x' := (genericPoint_spec T).specializes (Set.mem_univ x')
    exact (congrArg (fun φ => φ.hom e) (Scheme.Hom.stalkSpecializes_stalkMap j _ x' hηx)).symm
  -- the local lift at `y` and the coefficients at `y`
  obtain ⟨Uy, hyUy, τy, hτy, hτyE, hτy₀⟩ := hloc (j y') hyE
  obtain ⟨dy, hdy⟩ := hcoef Uy (j y') hyUy hyW τy hτy
  obtain ⟨dτ, hdτ⟩ := hcoef ⊤ (j y') trivial hyW τ hτtop
  -- along `P₀` the two coefficients agree, so their difference vanishes at `y`
  have e₁ := hres₀ _ (hsp₀ _ hy₀) dτ
  rw [← hdτ] at e₁
  have e₂ := hres₀ _ (hsp₀ _ hy₀) dy
  rw [← hdy] at e₂
  have hc₀ := smul_left_injective T₀.functionField hρ₀0'
    ((IsPoincareResidue.unique_of_isClosedImmersion P₀ hjT₀ hτ₀ e₁).symm.trans
      (IsPoincareResidue.unique_of_isClosedImmersion P₀ hjT₀ (hτy₀ ⟨j y', hy₀, hyUy⟩) e₂))
  have hdm : dτ - dy ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (j y')) := by
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    have hu' := (hu.map (Y.presheaf.stalkSpecializes (hsp₀ _ hy₀)).hom).map
      (j₀.stalkMap (genericPoint T₀)).hom
    rw [map_sub, map_sub] at hu'
    change IsUnit (_ - _) at hu'
    rw [hc₀, sub_self] at hu'
    exact not_isUnit_zero hu'
  -- along `E`
  have hτres := hresE _ (hspE _ hyE) dτ
  rw [← hdτ] at hτres
  have eE := IsPoincareResidue.unique_of_isClosedImmersion E hjT hτyE
    (by have := hresE _ (hspE _ hyE) dy; rwa [← hdy] at this)
  set cτ := (j.stalkMap (genericPoint T)).hom
    ((Y.presheaf.stalkSpecializes (hspE _ hyE)).hom dτ) with hcτ
  set cy := (j.stalkMap (genericPoint T)).hom
    ((Y.presheaf.stalkSpecializes (hspE _ hyE)).hom dy) with hcy
  suffices hc : cτ = cy by
    rw [eE, ← hc]
    exact hτres
  -- the difference of the coefficients is regular along the proper fibre over `ξ`
  haveI : AlgebraicGeometry.IsVariety k sY := hYv
  have hFv : Mori.IsVariety k (j ≫ sY) := ⟨⟩
  have hfs : (j ≫ r) ≫ sV = j ≫ sY := by rw [Category.assoc, hrs]
  have hξ : ∀ x' : T, (j ≫ r) x' = (j ≫ r) (genericPoint T) → r (j x') ∈ W := by
    intro x' hx'
    change r (j x') = r (j (genericPoint T)) at hx'
    rw [hx', hjT]
    exact hξW
  have key := eq_zero_of_isProper_of_mem_maximalIdeal hFv hVv (j ≫ r) hfs (cτ - cy)
    (fun x' hx' => ?_) y' (by
      change r (j y') = r (j (genericPoint T))
      rw [hjT, hry]) ((j.stalkMap y').hom (dτ - dy)) (by
        rw [hcompat, map_sub, map_sub]) ((IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
          (IsLocalRing.mem_maximalIdeal _).mp hdm (isUnit_of_map_unit _ _ hu))
  · exact sub_eq_zero.mp key
  have hxE : j x' ∈ (E.support : Set Y) := hjE ▸ ⟨x', rfl⟩
  have hxW := hξ x' hx'
  obtain ⟨Ux, hxUx, τx, hτx, hτxE, -⟩ := hloc (j x') hxE
  obtain ⟨dx, hdx⟩ := hcoef Ux (j x') hxUx hxW τx hτx
  obtain ⟨dτx, hdτx⟩ := hcoef ⊤ (j x') trivial hxW τ hτtop
  have eEx := IsPoincareResidue.unique_of_isClosedImmersion E hjT hτxE
    (by have := hresE _ (hspE _ hxE) dx; rwa [← hdx] at this)
  have hcx := smul_left_injective T.functionField hρE0' (eEx.symm.trans eE)
  have hτx : (Y.presheaf.stalkSpecializes (hspE _ hxE)).hom dτx =
      (Y.presheaf.stalkSpecializes (hspE _ hyE)).hom dτ := by
    apply IsFractionRing.injective (Y.presheaf.stalk (j (genericPoint T))) Y.functionField
    rw [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes',
      MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes']
    exact smul_left_injective Y.functionField hgen0 (hdτx.symm.trans hdτ)
  refine ⟨(j.stalkMap x').hom (dτx - dx), ?_⟩
  rw [hcompat, map_sub, map_sub, hτx]
  change cτ - _ = cτ - cy
  rw [← hcx]

/-- A floor component has dimension two. -/
private theorem topologicalKrullDim_floor_eq_two {k : Type} [Field k] [CharZero k]
    {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = 3) [IsIntegral T]
    (j : T ⟶ Y) [IsClosedImmersion j] (P : Mori.PrimeDivisor Y)
    (hjP : Set.range j.base = (P.support : Set Y)) : topologicalKrullDim T = 2 := by
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  have hjT := map_genericPoint_eq_of_range j P hjP
  have h1 := trdeg_add_one_of_eq_genericPoint (sY := sY) (j := j) P hjT
  have h2 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (d := 3)
    (by rw [hY]; rfl)
  rw [topologicalKrullDim_eq_toNat_trdeg (j ≫ sY)]
  have : (Algebra.trdeg k T.functionField).toNat = 2 := by omega
  rw [this]
  rfl

/-- The pull-back of an invertible sheaf has degree zero on a contracted curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type} [Field k] {Y V : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [IsSeparated sV] (r : Y ⟶ V)
    (hr : r ≫ sV = sY) (M : V.Modules) [SheafOfModules.IsInvertible V.presheaf V.ringCatSheaf.2 M]
    (C : ProperCurve sY) (hC : C.IsContractedBy r) :
    degreeOn k sY C.ι C.dim_le ((Scheme.Modules.pullback r).obj M) = 0 := by
  have hc : (C.ι ≫ r) ≫ sV = C.ι ≫ sY := by rw [Category.assoc, hr]
  haveI : IsProper ((C.ι ≫ r) ≫ sV) := hc ▸ inferInstance
  haveI : AlgebraicGeometry.IsCurve k ((C.ι ≫ r) ≫ sV) := hc ▸ C.isCurve
  rw [degreeOn_pullback_eq_degreeOn_comp sY sV r C.ι hr]
  refine degreeOn_eq_zero_of_range_eq_singleton sV (C.ι ≫ r) M ⟨r C.point, ?_⟩
  ext v
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ProperCurve.range_ι,
    Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hC x hx
  · rintro rfl; exact ⟨C.point, subset_closure rfl, rfl⟩

/-- **Two Cartier divisors are numerically dependent over a base of relative Picard number one.**
If `ρ(Y/V) = 1`, then for Cartier divisors `L₁, L₂` on `Y` there are reals `a, b`, not both zero,
with `a (L₁ · C) + b (L₂ · C) = 0` for every curve `C` contracted by `r`. -/
private theorem exists_mul_add_mul_eq_zero {k : Type} [Field k] {Y V : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [QuasiCompact sY] [IsSeparated sV] (r : Y ⟶ V) (hr : r ≫ sV = sY)
    (hρ : relativePicardNumberN1 sY r = 1) (L₁ L₂ : Divisor Y) (h₁ : L₁.IsCartier)
    (h₂ : L₂.IsCartier) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ C : ProperCurve sY, C.IsContractedBy r →
      a * (L₁.degreeOn k sY C.ι C.dim_le h₁ : ℝ) + b * (L₂.degreeOn k sY C.ι C.dim_le h₂ : ℝ) =
        0 := by
  obtain ⟨E₁, hE₁⟩ := MMP.Flips.exists_cartierDivisor_degree_eq sY L₁ h₁
  obtain ⟨E₂, hE₂⟩ := MMP.Flips.exists_cartierDivisor_degree_eq sY L₂ h₂
  set P := pullbackNumericalClasses sY r
  have hfin : Module.finrank ℝ (NumericalDivisorClasses sY ⧸ P) = 1 :=
    Module.finrank_eq_of_rank_eq (by rw [Cardinal.toENat_eq_one.mp hρ]; rfl)
  haveI := Module.finite_of_finrank_eq_succ hfin
  let c : Fin 2 → NumericalDivisorClasses sY :=
    ![numericalDivisorClass sY (KCartierDivisor.ofCartier ℝ E₁),
      numericalDivisorClass sY (KCartierDivisor.ofCartier ℝ E₂)]
  have hli : ¬ LinearIndependent ℝ (fun i => P.mkQ (c i)) := fun h => by
    have := h.fintype_card_le_finrank
    rw [hfin, Fintype.card_fin] at this
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hli
  have hmem : g 0 • c 0 + g 1 • c 1 ∈ P := by
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [Fin.sum_univ_two] using hg
  refine ⟨g 0, g 1, ?_, fun C hC => ?_⟩
  · by_contra h
    push Not at h
    fin_cases i <;> simp_all
  -- the pairing with `C` on `N¹(Y)`, which vanishes on pull-backs
  let φ : NumericalDivisorClasses sY →ₗ[ℝ] ℝ :=
    (numericallyTrivialDivisors sY).liftQ
      ((OneCycle.intersectionPairing (sX := sY)).flip (C.cycle ℝ)) fun D hD =>
        LinearMap.mem_ker.mpr ((mem_numericallyTrivialDivisors.mp hD) C)
  have hφ : ∀ D, φ (numericalDivisorClass sY D) = (C.cycle ℝ).intersectionNumber D := fun D => rfl
  have hP : P ≤ LinearMap.ker φ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨E, M, hM, ⟨e⟩, rfl⟩
    change φ _ = 0
    rw [hφ, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
      OneCycle.degree_cycle]
    haveI := hM
    have : ProperCurve.degree k C (MMP.CartierDivisor.sheaf E) = 0 := by
      rw [ProperCurve.degree, degreeOn_eq_of_iso k sY C.ι C.dim_le e]
      exact degreeOn_pullback_eq_zero r hr M C hC
    rw [this, Int.cast_zero]
  have h0 := hP hmem
  rw [LinearMap.mem_ker, map_add, map_smul, map_smul] at h0
  simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, hφ, hE₁, hE₂,
    smul_eq_mul] at h0
  exact h0

/-- **A connected closed set meeting a closed set `S` without lying in it has a point outside `S`
specializing into `S`.** In a Noetherian quasi-sober space, write `F` as a finite union of
irreducible closed sets; if none of those not contained in `S` met `S`, the two partial unions
would disconnect `F`. -/
private theorem exists_closure_inter_nonempty_of_isPreconnected {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {F S : Set X} (hF : IsClosed F)
    (hFc : IsPreconnected F) (hS : IsClosed S) (hFS : (F ∩ S).Nonempty) {x : X} (hxF : x ∈ F)
    (hxS : x ∉ S) : ∃ η ∈ F, η ∉ S ∧ (closure {η} ∩ S).Nonempty := by
  by_contra hcon
  push Not at hcon
  obtain ⟨𝒮, hfin, hcl, hirr, hFeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  have hdisj : ∀ t ∈ 𝒮, ¬ t ⊆ S → t ∩ S = ∅ := by
    intro t ht hts
    obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hirr t ht) (hcl t ht)
    rw [← hζ.def] at hts ⊢
    have hζS : ζ ∉ S := fun h => hts (closure_minimal (Set.singleton_subset_iff.mpr h) hS)
    have hζF : ζ ∈ F := hFeq ▸ Set.mem_sUnion_of_mem (hζ.def ▸ subset_closure rfl) ht
    exact hcon ζ hζF hζS
  set A := ⋃₀ {t ∈ 𝒮 | t ⊆ S}
  set B := ⋃₀ {t ∈ 𝒮 | ¬ t ⊆ S}
  have hA : IsClosed A :=
    Set.Finite.isClosed_sUnion (hfin.subset fun t ht => ht.1) fun t ht => hcl t ht.1
  have hB : IsClosed B :=
    Set.Finite.isClosed_sUnion (hfin.subset fun t ht => ht.1) fun t ht => hcl t ht.1
  have hAS : A ⊆ S := Set.sUnion_subset fun t ht => ht.2
  have hBS : B ∩ S = ∅ := by
    ext z
    simp only [B, Set.mem_inter_iff, Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro ⟨t, ⟨ht, hts⟩, hzt⟩ hzS
    have := hdisj t ht hts
    exact (Set.eq_empty_iff_forall_notMem.mp this) z ⟨hzt, hzS⟩
  have hcover : F ⊆ A ∪ B := by
    intro z hz
    rw [hFeq] at hz
    obtain ⟨t, ht, hzt⟩ := hz
    by_cases hts : t ⊆ S
    · exact Or.inl ⟨t, ⟨ht, hts⟩, hzt⟩
    · exact Or.inr ⟨t, ⟨ht, hts⟩, hzt⟩
  have hAB : Disjoint A B := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.eq_empty_of_subset_empty fun z hz => hBS ▸ ⟨hz.2, hAS hz.1⟩
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hF).mp hFc A B hA hB hcover hAB
    with h | h
  · exact hxS (hAS (h hxF))
  · obtain ⟨z, hzF, hzS⟩ := hFS
    exact (Set.eq_empty_iff_forall_notMem.mp hBS) z ⟨h hzF, hzS⟩

/-- **A contracted curve through a specialization.** Let `r : Y ⟶ V` with `Y` proper over `k`, and
`η ⤳ p` with `p` closed and `r(η)` closed. For a closed set `Z ∋ p` not containing `η` there is a
proper curve `C` contracted by `r`, with generic point a specialization of `η` outside `Z`,
passing through `p`. -/
private theorem exists_properCurve_isContractedBy {k : Type} [Field k] {Y V : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsProper sY] [IsLocallyNoetherian Y] (r : Y ⟶ V) {η p : Y}
    (hηp : η ⤳ p) (hp : IsClosed ({p} : Set Y)) (hv : IsClosed ({r η} : Set V)) {Z : Set Y}
    (hZ : IsClosed Z) (hpZ : p ∈ Z) (hηZ : η ∉ Z) :
    ∃ C : ProperCurve sY, C.IsContractedBy r ∧ C.point ∉ Z ∧
      p ∈ closure ({C.point} : Set Y) ∧ η ⤳ C.point := by
  obtain ⟨y, hηy, hyp, hyZ, hy⟩ := exists_isProperCurve_of_specializes sY hηp hp hZ hpZ hηZ
  have hfib : ∀ x, η ⤳ x → r x = r η := fun x hx => by
    have h1 : r x ∈ closure ({r η} : Set V) :=
      specializes_iff_mem_closure.mp (hx.map r.base.hom.continuous)
    rw [hv.closure_eq] at h1
    exact h1
  refine ⟨⟨y, hy⟩, fun x hx => ?_, hyZ, specializes_iff_mem_closure.mp hyp, hηy⟩
  rw [hfib x (hηy.trans (specializes_iff_mem_closure.mpr hx)), hfib y hηy]

/-- **Numerical triviality from one disjoint contracted curve.** With `ρ(Y/V) = 1` and a Cartier
divisor `A` positive on contracted curves, an effective Cartier divisor `L` missing one contracted
curve `C₀` has degree zero on every contracted curve. -/
private theorem degreeOn_eq_zero_of_forall_notMem_supp {k : Type} [Field k] {Y V : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [QuasiCompact sY] [IsSeparated sV] (r : Y ⟶ V) (hr : r ≫ sV = sY)
    (hρ : relativePicardNumberN1 sY r = 1) {A : Divisor Y} (hA : A.IsCartier)
    (hApos : ∀ C : ProperCurve sY, C.IsContractedBy r → 0 < A.degreeOn k sY C.ι C.dim_le hA)
    {L : Divisor Y} (hL : L.IsCartier) (hL0 : 0 ≤ L) (C₀ : ProperCurve sY)
    (hC₀ : C₀.IsContractedBy r) (hC₀L : ∀ c, C₀.ι c ∉ L.supp) (C : ProperCurve sY)
    (hC : C.IsContractedBy r) : L.degreeOn k sY C.ι C.dim_le hL = 0 := by
  haveI : IsIntegral C₀.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  obtain ⟨a, b, hab, h⟩ := exists_mul_add_mul_eq_zero r hr hρ L A hL hA
  obtain ⟨c₀, -⟩ : C₀.point ∈ Set.range C₀.ι := C₀.range_ι ▸ subset_closure rfl
  have h0 := ((MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sY C₀.ι C₀.dim_le L hL hL0
    ⟨c₀, hC₀L c₀⟩).2).mpr hC₀L
  have hb : b = 0 := by
    have := h C₀ hC₀
    rw [h0, Int.cast_zero, mul_zero, zero_add] at this
    have hpos : (0 : ℝ) < A.degreeOn k sY C₀.ι C₀.dim_le hA := by exact_mod_cast hApos C₀ hC₀
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hpos.ne'
  have ha : a ≠ 0 := hab.resolve_right (not_not.mpr hb)
  have := h C hC
  rw [hb, zero_mul, add_zero] at this
  exact_mod_cast (mul_eq_zero.mp this).resolve_left ha

/-- **A numerically trivial vertical prime divisor contains every fibre it meets.** Let
`r : Y ⟶ V` be proper with `r_* 𝒪_Y = 𝒪_V` and `Y` proper over `k`, and `L ≥ 0` a Cartier divisor
supported on a prime divisor `E` with `L · C = 0` for every contracted curve `C`. Then `E`
contains the whole fibre over every closed point of `r(E)`: otherwise the connected fibre has a
contracted curve meeting `E` without lying in it, on which `L` has positive degree. -/
private theorem preimage_singleton_subset_support {k : Type} [Field k] {Y V : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsProper sY]
    (r : Y ⟶ V) [IsProper r] (hO : ∀ U : V.Opens, IsIso (r.app U)) {S : Set Y} (hS : IsClosed S)
    {L : Divisor Y} (hL : L.IsCartier) (hL0 : 0 ≤ L) (hLS : (L.supp : Set Y) = S)
    (htriv : ∀ C : ProperCurve sY, C.IsContractedBy r → L.degreeOn k sY C.ι C.dim_le hL = 0)
    {v : V} (hv : IsClosed ({v} : Set V)) (hvS : v ∈ r.base '' S) : r.base ⁻¹' {v} ⊆ S := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  intro x hx
  by_contra hxS
  have hFcl : IsClosed (r.base ⁻¹' {v}) := hv.preimage r.base.hom.continuous
  have hFc := r.isConnected_preimage_singleton_of_isIso_app hO v
  obtain ⟨y, hyS, hyv⟩ := hvS
  obtain ⟨η, hηF, hηS, q, hqη, hqS⟩ := exists_closure_inter_nonempty_of_isPreconnected hFcl
    hFc.isPreconnected hS ⟨y, hyv, hyS⟩ hx hxS
  obtain ⟨p, hpq, hp⟩ := (isClosed_closure (s := ({q} : Set Y))).exists_closed_singleton
    ⟨q, subset_closure rfl⟩
  have hpS : p ∈ S := closure_minimal (Set.singleton_subset_iff.mpr hqS) hS hpq
  have hηp : η ⤳ p :=
    (specializes_iff_mem_closure.mpr hqη).trans (specializes_iff_mem_closure.mpr hpq)
  have hrη : r η = v := hηF
  obtain ⟨C, hC, hCS, hpC, -⟩ := exists_properCurve_isContractedBy (sY := sY) r hηp hp
    (by rw [hrη]; exact hv) hS hpS hηS
  haveI : IsIntegral C.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  obtain ⟨c₀, hc₀⟩ : C.point ∈ Set.range C.ι := C.range_ι ▸ subset_closure rfl
  have key := MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sY C.ι C.dim_le L hL hL0
    ⟨c₀, by rw [hc₀]; change C.point ∉ (L.supp : Set Y); rw [hLS]; exact hCS⟩
  have hall := key.2.mp (htriv C hC)
  have : p ∈ Set.range C.ι := by rw [ProperCurve.range_ι]; exact hpC
  obtain ⟨c, hc⟩ := this
  exact hall c (by rw [hc]; change p ∈ (L.supp : Set Y); rw [hLS]; exact hpS)

/-- A Noetherian, quasi-sober `T₁` space is discrete: each of its finitely many irreducible
components is the closure of a generic point, hence a single point. -/
private theorem discreteTopology_of_noetherianSpace_of_t1Space {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] [QuasiSober α] [T1Space α] : DiscreteTopology α := by
  haveI : Finite α := by
    have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)
    have hC : ∀ C ∈ irreducibleComponents α, C.Finite := fun C hC => by
      obtain ⟨c, hc⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
      rw [← isGenericPoint_def.mp hc, closure_singleton]
      exact Set.finite_singleton c
    have := hfin.sUnion hC
    rw [sUnion_irreducibleComponents] at this
    exact Set.finite_univ_iff.mp this
  infer_instance

/-- **Every closed fibre of a fibration of a threefold over a surface contains a contracted
curve.** Let `r : Y ⟶ V` be a surjective morphism of varieties over `k`, `Y` proper, with
`dim Y = 3` and `dim V = 2`. Over every closed point `v` there is a proper curve contracted by
`r` lying in `r⁻¹(v)`: otherwise every point of the fibre is closed, the fibre is finite and
discrete, against the lower bound `dim Y ≤ dim (component of the fibre) + dim V`. -/
private theorem exists_properCurve_subset_preimage_singleton {k : Type} [Field k]
    {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sY] [AlgebraicGeometry.IsVariety k sV] [IsProper sY]
    (r : Y ⟶ V) [IsProper r] (hr : r ≫ sV = sY) (hsurj : Function.Surjective r)
    (hY : topologicalKrullDim Y = 3) (hV : topologicalKrullDim V = 2) {v : V}
    (hv : IsClosed ({v} : Set V)) :
    ∃ C : ProperCurve sY, C.IsContractedBy r ∧ closure ({C.point} : Set Y) ⊆ r.base ⁻¹' {v} := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  by_contra hcon
  -- every point over `v` is closed
  have hcl : ∀ x, r x = v → IsClosed ({x} : Set Y) := by
    intro x hx
    by_contra hxc
    obtain ⟨p, hpx, hp⟩ := (isClosed_closure (s := ({x} : Set Y))).exists_closed_singleton
      ⟨x, subset_closure rfl⟩
    have hpne : x ≠ p := fun h => hxc (h ▸ hp)
    obtain ⟨C, hC, -, -, hxC⟩ := exists_properCurve_isContractedBy (sY := sY) r
      (specializes_iff_mem_closure.mpr hpx) hp (by rw [hx]; exact hv) hp rfl hpne
    refine hcon ⟨C, hC, fun z hz => ?_⟩
    have h1 : r C.point ∈ closure ({r x} : Set V) :=
      specializes_iff_mem_closure.mp (hxC.map r.base.hom.continuous)
    rw [hx, hv.closure_eq] at h1
    change r z = v
    rw [hC z hz]
    exact h1
  -- the fibre is discrete
  haveI : T1Space (r.fiber v) := by
    rw [t1Space_iff_specializes_imp_eq]
    intro a b hab
    have hmem : ∀ c, r (r.fiberι v c) = v := fun c => by
      have : r.fiberι v c ∈ r.base ⁻¹' {v} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨c, rfl⟩
      exact this
    have hab' := hab.map (r.fiberι v).base.hom.continuous
    have := (hcl _ (hmem a)).closure_eq ▸ specializes_iff_mem_closure.mp hab'
    exact ((r.fiberι v).isEmbedding.injective this).symm
  haveI : IsLocallyNoetherian (r.fiber v) :=
    inferInstanceAs (IsLocallyNoetherian (Limits.pullback _ _))
  haveI : IsNoetherian (r.fiber v) := {}
  haveI := discreteTopology_of_noetherianSpace_of_t1Space (α := r.fiber v)
  haveI : IsDominant r := ⟨hsurj.denseRange⟩
  obtain ⟨x, hx⟩ := hsurj v
  obtain ⟨z, -⟩ : ∃ z, r.fiberι v z = x := by
    have : x ∈ r.base ⁻¹' {v} := hx
    rw [← Scheme.Hom.range_fiberι] at this
    exact this
  have h1 := (MMP.topologicalKrullDim_fiber_of_isDominant k sY sV r hr).1 v _
    (irreducibleComponent_mem_irreducibleComponents z)
  have h2 : topologicalKrullDim (irreducibleComponent z) ≤ topologicalKrullDim (r.fiber v) :=
    Topology.IsInducing.subtypeVal.topologicalKrullDim_le
  have h2' := h2.trans (topologicalKrullDim_zero_of_discreteTopology (r.fiber v))
  rw [hY, hV] at h1
  have h3 := h1.trans (add_le_add_left h2' _)
  norm_num at h3

/-- **A descended coefficient is regular.** Let `div α + mB = r^*M` and `P₀` a floor prime
surjecting onto `V`, along which a floor section `s₀` lifts locally near every point. If
`r^*f · α` has residue `s₀` along `P₀`, then `r^*f · α` is a global section of `m(K_Y + B)`. Near
a point of `V` write `r^*f · α = r^*(f φ) · α (r^*φ)⁻¹` for a local equation `φ` of `M`; if `f φ`
had a pole along a curve `C ⊆ V`, then at a point `y ∈ P₀` over `η_C` the local lift
`d · α (r^*φ)⁻¹` would give `(f φ)⁻¹ d ≡ 1` along `P₀` with `(f φ)⁻¹ d` in the maximal ideal at
`y`. So `f φ` is regular in codimension one on the normal `V`, hence regular (Hartogs), and its
pull-back is regular along every prime divisor of `Y`. -/
private theorem mem_logPluricanonicalSections_of_isPoincareResidue
    {k : Type} [Field k] [CharZero k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sY]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {r : Y ⟶ V} [IsDominant r] (hY : topologicalKrullDim Y = 3) {B : QDivisor Y} {m : ℕ}
    (hm : 0 < m) (hmB : ∀ P, ((m : ℚ) * B.coeff P).den = 1)
    (α : RationalPluriForms sY 3 m) (M : Divisor V) (hM : M.IsCartier)
    (hrM : ∀ W : irreducibleComponents Y, r (componentGenericPoint Y W) ∉ M.supp)
    (rM : Divisor Y) (hrMp : M.IsPullback r hrM rM) (hα : α ≠ 0)
    (hαM : ∀ P : Mori.PrimeDivisor Y, (P.ordForm α : ℚ) + (m : ℚ) * B.coeff P = (rM.coeff P : ℚ))
    {T₀ : Scheme.{0}} [IsIntegral T₀] (j₀ : T₀ ⟶ Y) [IsClosedImmersion j₀]
    (hT₀ : topologicalKrullDim T₀ = 2) (P₀ : Mori.PrimeDivisor Y) (hB₀ : B.coeff P₀ = 1)
    (hj₀ : Set.range j₀.base = (P₀.support : Set Y))
    (hP₀ : r.base '' (P₀.support : Set Y) = Set.univ)
    (s₀ : RationalPluriForms (j₀ ≫ sY) 2 m)
    (hloc : ∀ y ∈ (P₀.support : Set Y), ∃ U : Y.Opens, y ∈ U ∧
      ∃ τ ∈ pluricanonicalSections sY 3 m (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) U,
        IsPoincareResidue sY j₀ 2 m τ s₀)
    (f : V.functionField) (hf : IsPoincareResidue sY j₀ 2 m (functionFieldMap r f • α) s₀) :
    functionFieldMap r f • α ∈ logPluricanonicalSections sY 3 m B := by
  classical
  obtain ⟨M', rfl⟩ : ∃ M', m = M' + 1 := Nat.exists_eq_succ_of_ne_zero hm.ne'
  letI := functionFieldAlgebra sY
  have hd : (Algebra.trdeg k Y.functionField).toNat = 3 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; rfl)
  have hjT₀ := map_genericPoint_eq_of_range j₀ P₀ hj₀
  by_cases hf0 : f = 0
  · rw [hf0, map_zero, zero_smul]
    exact zero_mem _
  have hrf0 : functionFieldMap r f ≠ 0 := (map_ne_zero _).mpr hf0
  have hτ0 : functionFieldMap r f • α ≠ 0 := smul_ne_zero hrf0 hα
  have hrank : Module.finrank Y.functionField
      (RationalPluriForms sY 3 ((M' + 1 : ℕ) : ℤ)) = 1 :=
    finrank_rationalPluriForms_eq_one_of_topologicalKrullDim sY (d := 3) (by rw [hY]; rfl) _
  have hmBint : ∀ Γ : Mori.PrimeDivisor Y,
      ((⌊((M' + 1 : ℕ) : ℤ) • B.coeff Γ⌋ : ℤ) : ℚ) = ((M' + 1 : ℕ) : ℚ) * B.coeff Γ := by
    intro Γ
    rw [zsmul_eq_mul, Int.cast_natCast]
    have hq := Rat.coe_int_num_of_den_eq_one (hmB Γ)
    conv_lhs => rw [← hq]
    rw [Int.floor_intCast]
    exact hq
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents V) :=
    ⟨⟨Set.univ, (irreducibleComponents_eq_singleton (X := V)).symm ▸ rfl⟩⟩
  have hsp₀ : ∀ z ∈ (P₀.support : Set Y), j₀ (genericPoint T₀) ⤳ z := fun z hz =>
    (specializes_of_eq hjT₀).trans (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
      exact specializes_iff_mem_closure.mpr hz)
  -- residues of regular multiples
  have hresX : ∀ {X : RationalPluriForms sY 3 ((M' + 1 : ℕ) : ℤ)}
      {ρ : RationalPluriForms (j₀ ≫ sY) 2 ((M' + 1 : ℕ) : ℤ)},
      IsPoincareResidue sY j₀ 2 (M' + 1) X ρ →
      ∀ (z : Y) (hz : j₀ (genericPoint T₀) ⤳ z) (d : Y.presheaf.stalk z),
      IsPoincareResidue sY j₀ 2 (M' + 1) (algebraMap _ Y.functionField d • X)
        ((j₀.stalkMap (genericPoint T₀)).hom ((Y.presheaf.stalkSpecializes hz).hom d) • ρ) := by
    intro X ρ hX z hz d
    have := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hX
      ((Y.presheaf.stalkSpecializes hz).hom d)
    rwa [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' Y hz d] at this
  -- `f φ` is regular along every curve of `V` meeting the domain of a local equation `φ`
  have hcurve : ∀ (W : V.Opens) (φ : (RationalFunctions V)ˣ), M.IsLocalEquation W φ →
      ∀ Γ' : Mori.PrimeDivisor V, Γ'.genericPoint ∈ W →
        0 ≤ V.ord (f * MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions V))
          Γ'.genericPoint := by
    intro W φ hφ Γ' hΓ'W
    set φ₀ := MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions V) with hφ₀
    have hφ₀0 : φ₀ ≠ 0 := (φ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z)).ne_zero
    have hrφ₀0 : functionFieldMap r φ₀ ≠ 0 := (map_ne_zero _).mpr hφ₀0
    have hg0 : f * φ₀ ≠ 0 := mul_ne_zero hf0 hφ₀0
    by_contra hneg
    push Not at hneg
    -- `(f φ)⁻¹` lies in the maximal ideal at `η_C`
    have hinv0 : (f * φ₀)⁻¹ ≠ 0 := inv_ne_zero hg0
    have hordinv : V.ord (f * φ₀)⁻¹ Γ'.genericPoint = -V.ord (f * φ₀) Γ'.genericPoint := by
      have := Scheme.ord_mul hinv0 hg0 (x := Γ'.genericPoint)
      rw [inv_mul_cancel₀ hg0, Scheme.ord_one] at this
      omega
    obtain ⟨e₀, he₀⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg Γ' hinv0
      (by omega)
    have he₀m : e₀ ∈ IsLocalRing.maximalIdeal Γ'.localRing := by
      have : Γ'.divisorialValuation (algebraMap _ V.functionField e₀) < 1 := by
        rw [he₀, Γ'.divisorialValuation_eq_exp_neg_ord hinv0, ← WithZero.exp_zero,
          WithZero.exp_lt_exp]
        omega
      exact (Γ'.divisorialValuation_algebraMap_lt_one_iff e₀).mp this
    -- a point of `P₀` over `η_C` and the local lift there
    obtain ⟨y, hy, hyv⟩ : Γ'.genericPoint ∈ r.base '' (P₀.support : Set Y) :=
      hP₀ ▸ Set.mem_univ _
    obtain ⟨y', rfl⟩ : ∃ y', j₀ y' = y := by
      have : y ∈ Set.range j₀.base := hj₀ ▸ hy
      exact this
    have hyW : r (j₀ y') ∈ W := by rw [hyv]; exact hΓ'W
    obtain ⟨U, hyU, τy, hτy, hresy⟩ := hloc _ hy
    set gen := (functionFieldMap r φ₀)⁻¹ • α with hgendef
    have hgen0 : gen ≠ 0 := smul_ne_zero (inv_ne_zero hrφ₀0) hα
    -- `τ_y = d · gen` with `d` regular at `y`
    obtain ⟨d, hdτ⟩ :
        ∃ d : Y.presheaf.stalk (j₀ y'), τy = algebraMap _ Y.functionField d • gen := by
      by_cases hτ'0 : τy = 0
      · exact ⟨0, by rw [hτ'0, map_zero, zero_smul]⟩
      obtain ⟨h', hh'⟩ := (finrank_eq_one_iff_of_nonzero' α hα).mp hrank τy
      have hh'0 : h' ≠ 0 := by rintro rfl; exact hτ'0 (by rw [← hh', zero_smul])
      have hH0 : h' * functionFieldMap r φ₀ ≠ 0 := mul_ne_zero hh'0 hrφ₀0
      have hτ'H : τy = (h' * functionFieldMap r φ₀) • gen := by
        rw [hgendef, smul_smul, mul_assoc, mul_inv_cancel₀ hrφ₀0, mul_one, hh']
      obtain ⟨d, hd'⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord
        (j₀ y') hH0 fun Γ hΓ => by
          have hΓW : (Γ.support ∩ r ⁻¹ᵁ W).Nonempty := ⟨_, hΓ, hyW⟩
          have h1 := hτy.2 Γ ⟨_, hΓ, hyU⟩ hτ'0
          rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at h1
          have h2 := hαM Γ
          have h3 := coeff_eq_ord_of_isPullback hrMp hφ Γ hΓW Z
          have h4 : Γ.ordForm τy = Y.ord h' Γ.genericPoint + Γ.ordForm α := by
            rw [← hh', Γ.ordForm_smul (sX := sY) hd hh'0 hα]
          rw [Scheme.ord_mul hh'0 hrφ₀0, hφ₀, ← h3]
          have h1' : (0 : ℚ) ≤ ((Γ.ordForm τy : ℤ) : ℚ) +
              ((⌊((M' + 1 : ℕ) : ℤ) • B.coeff Γ⌋ : ℤ) : ℚ) := by exact_mod_cast h1
          rw [hmBint, h4] at h1'
          push_cast at h1' h2
          have : (0 : ℚ) ≤ ((Y.ord h' Γ.genericPoint + rM.coeff Γ : ℤ) : ℚ) := by
            push_cast; linarith
          exact_mod_cast this
      exact ⟨d, by rw [hd', hτ'H]⟩
    -- the residue of the local generator along `P₀`
    have hgenord : P₀.ordForm gen = -((M' + 1 : ℕ) : ℤ) := by
      have h3 := coeff_eq_ord_of_isPullback hrMp hφ P₀ ⟨_, hy, hyW⟩ Z
      have h2 := hαM P₀
      rw [hB₀, mul_one] at h2
      have hinv : Y.ord (functionFieldMap r φ₀)⁻¹ P₀.genericPoint =
          -Y.ord (functionFieldMap r φ₀) P₀.genericPoint := by
        have := Scheme.ord_mul (inv_ne_zero hrφ₀0) hrφ₀0 (x := P₀.genericPoint)
        rw [inv_mul_cancel₀ hrφ₀0, Scheme.ord_one] at this
        omega
      rw [hgendef, P₀.ordForm_smul (sX := sY) hd (inv_ne_zero hrφ₀0) hα, hinv, hφ₀, ← h3]
      have : ((P₀.ordForm α : ℤ) : ℚ) = ((rM.coeff P₀ - ((M' + 1 : ℕ) : ℤ) : ℤ) : ℚ) := by
        push_cast at h2 ⊢; linarith
      have := Int.cast_injective this
      omega
    obtain ⟨ρ₀, hρ₀, hρ₀0⟩ := exists_isPoincareResidue sY (n := 2) (by rw [hY]; rfl) j₀ hT₀ P₀
      hjT₀ M' (Or.inr hgenord.ge)
    have hρ₀0' := hρ₀0 hgen0 hgenord
    -- `(f φ)⁻¹` pulled back to the stalk at `y`, in its maximal ideal
    have h1 : r (j₀ y') ⤳ Γ'.genericPoint := specializes_of_eq hyv
    set e := (V.presheaf.stalkSpecializes h1).hom e₀ with hedef
    have he : algebraMap _ V.functionField e = (f * φ₀)⁻¹ := by
      rw [hedef, MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes', he₀]
    have hem : ¬ IsUnit e := fun hu => (IsLocalRing.mem_maximalIdeal _).mp he₀m
      (isUnit_of_isUnit_stalkSpecializes hyv.symm h1 e₀ hu)
    set ey := (r.stalkMap (j₀ y')).hom e with heydef
    have hey : algebraMap _ Y.functionField ey = functionFieldMap r (f * φ₀)⁻¹ := by
      rw [heydef, ← functionFieldMap_algebraMap_stalk, he]
    have heyu : ¬ IsUnit ey := fun hu => hem (isUnit_of_map_unit _ _ hu)
    -- `gen = (r^*(f φ))⁻¹ · r^*f · α`
    have hgen : gen = algebraMap _ Y.functionField ey • (functionFieldMap r f • α) := by
      rw [hey, smul_smul, map_inv₀, map_mul, hgendef]
      congr 1
      field_simp
    have hz := hsp₀ _ hy
    have r₁ := hresX hf _ hz ey
    rw [← hgen] at r₁
    have r₂ := hresX hρ₀ _ hz d
    rw [← hdτ] at r₂
    have e₁ := IsPoincareResidue.unique_of_isClosedImmersion P₀ hjT₀ hρ₀ r₁
    have e₂ := IsPoincareResidue.unique_of_isClosedImmersion P₀ hjT₀ hresy r₂
    set ψ : Y.presheaf.stalk (j₀ y') →+* T₀.functionField :=
      (j₀.stalkMap (genericPoint T₀)).hom.comp (Y.presheaf.stalkSpecializes hz).hom with hψ
    have hone : ψ (ey * d) = 1 := by
      refine smul_left_injective T₀.functionField hρ₀0' ?_
      change ψ (ey * d) • ρ₀ = (1 : T₀.functionField) • ρ₀
      rw [one_smul, map_mul, mul_smul]
      have e₁' : ρ₀ = ψ ey • s₀ := e₁
      have e₂' : s₀ = ψ d • ρ₀ := e₂
      rw [← e₂', ← e₁']
    -- but `ey · d` lies in the maximal ideal at `y`
    have hcompat : algebraMap _ T₀.functionField ((j₀.stalkMap y').hom (ey * d)) = ψ (ey * d) := by
      have hηx : genericPoint T₀ ⤳ y' := (genericPoint_spec T₀).specializes (Set.mem_univ y')
      exact (congrArg (fun φ => φ.hom (ey * d))
        (Scheme.Hom.stalkSpecializes_stalkMap j₀ _ y' hηx)).symm
    rw [hone, ← map_one (algebraMap (T₀.presheaf.stalk y') T₀.functionField)] at hcompat
    have h1' := IsFractionRing.injective (T₀.presheaf.stalk y') T₀.functionField hcompat
    have hu : IsUnit ((j₀.stalkMap y').hom (ey * d)) := h1' ▸ isUnit_one
    exact heyu (isUnit_of_mul_isUnit_left (isUnit_of_map_unit _ _ hu))
  -- every prime divisor of `Y`
  refine (mem_logPluricanonicalSections (sX := sY)).mpr ⟨fun h => ?_, fun Γ _ _ => ?_⟩
  · exact absurd (h ▸ (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)) (by simp)
  obtain ⟨W, hcW, φ, hφ⟩ := hM (r Γ.genericPoint)
  set φ₀ := MMP.Threefold.Mori.Helpers.evalFF Z (φ : RationalFunctions V) with hφ₀
  have hφ₀0 : φ₀ ≠ 0 := (φ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z)).ne_zero
  have hrφ₀0 : functionFieldMap r φ₀ ≠ 0 := (map_ne_zero _).mpr hφ₀0
  have hg0 : f * φ₀ ≠ 0 := mul_ne_zero hf0 hφ₀0
  obtain ⟨g, hg⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord
    (r Γ.genericPoint) hg0 fun Γ' hΓ' => hcurve W φ hφ Γ' (by
      have : Γ'.genericPoint ⤳ r Γ.genericPoint := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ'
        exact specializes_iff_mem_closure.mpr hΓ'
      exact this.mem_open W.isOpen hcW)
  have hrg0 : functionFieldMap r (f * φ₀) ≠ 0 := (map_ne_zero _).mpr hg0
  have hord : 0 ≤ Y.ord (functionFieldMap r (f * φ₀)) Γ.genericPoint := by
    have hle : Γ.divisorialValuation (functionFieldMap r (f * φ₀)) ≤ 1 := by
      rw [Γ.divisorialValuation_le_one_iff, ← hg, functionFieldMap_algebraMap_stalk]
      exact ⟨_, rfl⟩
    rw [Γ.divisorialValuation_eq_exp_neg_ord hrg0, ← WithZero.exp_zero, WithZero.exp_le_exp]
      at hle
    omega
  have h3 := coeff_eq_ord_of_isPullback hrMp hφ Γ
    ⟨Γ.genericPoint, (Γ.genericPoint_mem_iff ⊤).mp trivial |>.choose_spec.1 |> fun _ => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
      hcW⟩ Z
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul,
    Γ.ordForm_smul (sX := sY) hd hrf0 hα]
  have h2 := hαM Γ
  have h3' : rM.coeff Γ = Y.ord (functionFieldMap r φ₀) Γ.genericPoint := h3
  rw [map_mul, Scheme.ord_mul hrf0 hrφ₀0, ← h3'] at hord
  have hfl : (0 : ℚ) ≤ ((Y.ord (functionFieldMap r f) Γ.genericPoint + Γ.ordForm α : ℤ) : ℚ) +
      ((⌊((M' + 1 : ℕ) : ℤ) • B.coeff Γ⌋ : ℤ) : ℚ) := by
    rw [hmBint]
    push_cast at h2 ⊢
    have : (0 : ℚ) ≤ ((Y.ord (functionFieldMap r f) Γ.genericPoint + rM.coeff Γ : ℤ) : ℚ) := by
      exact_mod_cast hord
    push_cast at this
    linarith
  exact_mod_cast hfl

/-- **The horizontal floor meets every vertical floor prime over its generic image.** In the
two-floor Mori setting, for a floor prime `E` not dominating `V`, with image curve `C`, some
horizontal floor prime `P₀` meets `E` at a point over the generic point `r(η_E)` of `C`. The
horizontal floor is relatively ample, its degree on the unique contracted ray being two, so it
meets the generic proper curve `E_{η_C}`. -/
private theorem exists_isDominant_mem_support_inter
    {k : Type} [Field k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {r : Y ⟶ V} {K : Divisor Y} {Γ : QDivisor Y}
    (hr : IsMoriFibreSpace sY sV K Γ r) (hΓ : MMP.Fourfold.IsKltPair sY Γ) (hQ : IsQFactorial sY)
    (hY : topologicalKrullDim Y = 3) (hV : topologicalKrullDim V = 2)
    {B : QDivisor Y} (hlc : MMP.Intersection.IsLogCanonicalPair sY B)
    (hnef : QDivisor.IsRelativelyNef sY r (Divisor.toQDivisor K + B))
    (hnef' : QDivisor.IsRelativelyNef sY r (-(Divisor.toQDivisor K + B)))
    {F : {P : Mori.PrimeDivisor Y // B.coeff P = 1} → Scheme.{0}} [∀ P, IsIntegral (F P)]
    (j : ∀ P, F P ⟶ Y) [∀ P, IsClosedImmersion (j P)]
    (hj : ∀ P, Set.range (j P).base = (P.1.support : Set Y))
    (hdeg : ∑ᶠ (P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}) (_ : IsDominant (j P ≫ r)),
      (letI : IsDominant (j P ≫ r) := ‹_›
       letI := functionFieldMapAlgebra (j P ≫ r)
       Module.finrank V.functionField (F P).functionField) = 2)
    (E : {P : Mori.PrimeDivisor Y // B.coeff P = 1}) (hE : ¬ IsDominant (j E ≫ r)) :
    ∃ P₀ : {P : Mori.PrimeDivisor Y // B.coeff P = 1}, IsDominant (j P₀ ≫ r) ∧
      ∃ y ∈ (E.1.support : Set Y), y ∈ (P₀.1.support : Set Y) ∧ r y = r E.1.genericPoint := by
  classical
  haveI := hr.isProjectiveVariety
  haveI := hr.isProjectiveVariety_target
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY IsProjectiveVariety.isProjective
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.isContraction.isProjectiveMorphism
  haveI : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace sV
  have hsurj := hr.isContraction.surjective
  have hrs := hr.isContraction.comp_eq
  -- a relatively ample Cartier divisor
  obtain ⟨n, -, A, hA, -, hAamp⟩ := hr.hasRelativelyAmpleMultiple
  have hApos : ∀ C : ProperCurve sY, C.IsContractedBy r →
      0 < A.degreeOn k sY C.ι C.dim_le hA := by
    intro C hC
    haveI := hA.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy r _ hAamp
      C hC
  -- a Cartier multiple of `E`
  obtain ⟨N, hN, hNc⟩ := hQ.2 (Finsupp.single E.1 1)
  have hL0 : 0 ≤ (N : ℤ) • (Finsupp.single E.1 1 : Divisor Y) := fun P => by
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul]
    split_ifs <;> omega
  have hEcl : IsClosed (E.1.support : Set Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hLS : (DivisorWithCoeffs.supp ((N : ℤ) • (Finsupp.single E.1 1 : Divisor Y)) : Set Y) =
      E.1.support := by
    ext x
    rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
    constructor
    · rintro ⟨P, hP, hxP⟩
      have : P = E.1 := by
        by_contra hne
        apply hP
        simp [DivisorWithCoeffs.coeff, Finsupp.single_apply, Ne.symm hne]
      exact this ▸ hxP
    · intro hx
      refine ⟨E.1, ?_, hx⟩
      simp [DivisorWithCoeffs.coeff, Finsupp.single_apply]
      omega
  -- the image of `E` is a proper closed subset of `V`
  have hrE : IsClosed (r.base '' (E.1.support : Set Y)) := r.isClosedMap _ hEcl
  have hrEne : (r.base '' (E.1.support : Set Y))ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    apply hE
    have hrange : Set.range (j E ≫ r).base = r.base '' (E.1.support : Set Y) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hj]
    exact ⟨by rw [DenseRange, hrange, h]; exact dense_univ⟩
  obtain ⟨v₀, hv₀, hv₀c⟩ := nonempty_inter_closedPoints hrEne hrE.isOpen_compl.isLocallyClosed
  obtain ⟨C₀, hC₀, hC₀v⟩ := exists_properCurve_subset_preimage_singleton r hrs hsurj hY hV
    (mem_closedPoints_iff.mp hv₀c)
  have hC₀L : ∀ c,
      C₀.ι c ∉ DivisorWithCoeffs.supp ((N : ℤ) • (Finsupp.single E.1 1 : Divisor Y)) := by
    intro c hc
    have hc' : C₀.ι c ∈ (E.1.support : Set Y) := hLS ▸ hc
    have hcv : C₀.ι c ∈ r.base ⁻¹' {v₀} := hC₀v (C₀.range_ι ▸ ⟨c, rfl⟩)
    exact hv₀ ⟨_, hc', hcv⟩
  have htriv := degreeOn_eq_zero_of_forall_notMem_supp r hrs hr.relativePicardNumber_eq_one hA
    hApos hNc hL0 C₀ hC₀ hC₀L
  have hfib : ∀ v : V, IsClosed ({v} : Set V) → v ∈ r.base '' (E.1.support : Set Y) →
      r.base ⁻¹' {v} ⊆ E.1.support := fun v hv hvE =>
    preimage_singleton_subset_support r hr.isContraction.isIso_app hEcl hNc hL0 hLS htriv hv hvE
  -- a horizontal floor prime, which surjects onto `V`
  obtain ⟨P₀, hdom⟩ : ∃ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}, IsDominant (j P ≫ r) :=
    exists_of_finsum_finsum_ne_zero hdeg two_ne_zero
  have hP₀ : r.base '' (P₀.1.support : Set Y) = Set.univ := by
    have hrange : Set.range (j P₀ ≫ r).base = r.base '' (P₀.1.support : Set Y) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hj]
    have hcl : IsClosed (r.base '' (P₀.1.support : Set Y)) :=
      r.isClosedMap _ (hj P₀ ▸ (j P₀).isClosedEmbedding.isClosed_range)
    have hdense := hdom.denseRange
    rw [DenseRange, hrange] at hdense
    exact hcl.closure_eq ▸ hdense.closure_eq
  -- `r(P₀ ∩ E)` contains every closed point of `r(E)`, hence all of it
  have hK : IsClosed (r.base '' ((P₀.1.support : Set Y) ∩ E.1.support)) :=
    r.isClosedMap _ ((hj P₀ ▸ (j P₀).isClosedEmbedding.isClosed_range).inter hEcl)
  have hsub : r.base '' (E.1.support : Set Y) ⊆
      r.base '' ((P₀.1.support : Set Y) ∩ E.1.support) := by
    rw [← closure_inter_closedPoints hrE]
    refine closure_minimal ?_ hK
    rintro v ⟨hvE, hvc⟩
    obtain ⟨y, hy, hyv⟩ : v ∈ r.base '' (P₀.1.support : Set Y) := hP₀ ▸ Set.mem_univ v
    exact ⟨y, ⟨hy, hfib v (mem_closedPoints_iff.mp hvc) hvE hyv⟩, hyv⟩
  have hηE : E.1.genericPoint ∈ (E.1.support : Set Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨y, ⟨hy₀, hyE⟩, hyξ⟩ := hsub ⟨_, hηE, rfl⟩
  exact ⟨P₀, hdom, y, hyE, hy₀, hyξ⟩

/-- **Agreement on the vertical floor.** In the two-floor Mori setting, with `div α + mB = r^*M`,
a global section `τ` of `m(K_Y + B)` whose residues along the horizontal floor primes are the
restrictions of a floor section `s` has residue `s` along every floor prime. For a vertical floor
prime `E` the horizontal floor meets `E` over the generic point of its image curve
(`exists_isDominant_mem_support_inter`), and detection on the proper fibre
(`isPoincareResidue_of_mem_support_inter`) gives the residue along `E`. -/
private theorem isPoincareResidue_of_forall_isDominant
    {k : Type} [Field k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    {r : Y ⟶ V} {K : Divisor Y} {Γ : QDivisor Y}
    (hr : IsMoriFibreSpace sY sV K Γ r) (hΓ : MMP.Fourfold.IsKltPair sY Γ) (hQ : IsQFactorial sY)
    (hY : topologicalKrullDim Y = 3) (hV : topologicalKrullDim V = 2)
    {B : QDivisor Y} (hlc : MMP.Intersection.IsLogCanonicalPair sY B)
    (hnef : QDivisor.IsRelativelyNef sY r (Divisor.toQDivisor K + B))
    (hnef' : QDivisor.IsRelativelyNef sY r (-(Divisor.toQDivisor K + B)))
    {F : {P : Mori.PrimeDivisor Y // B.coeff P = 1} → Scheme.{0}} [∀ P, IsIntegral (F P)]
    (j : ∀ P, F P ⟶ Y) [∀ P, IsClosedImmersion (j P)]
    (hj : ∀ P, Set.range (j P).base = (P.1.support : Set Y))
    (hdeg : ∑ᶠ (P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}) (_ : IsDominant (j P ≫ r)),
      (letI : IsDominant (j P ≫ r) := ‹_›
       letI := functionFieldMapAlgebra (j P ≫ r)
       Module.finrank V.functionField (F P).functionField) = 2)
    {m : ℕ} (hm : 0 < m) (hmB : ∀ P, ((m : ℚ) * B.coeff P).den = 1)
    (α : RationalPluriForms sY 3 m) (M : Divisor V) (hM : M.IsCartier)
    (hrM : ∀ W : irreducibleComponents Y, r (componentGenericPoint Y W) ∉ M.supp)
    (rM : Divisor Y) (hrMp : M.IsPullback r hrM rM) (hα : α ≠ 0)
    (hαM : ∀ P : Mori.PrimeDivisor Y, (P.ordForm α : ℚ) + (m : ℚ) * B.coeff P = (rM.coeff P : ℚ))
    (s : ∀ P, RationalPluriForms (j P ≫ sY) 2 m)
    (hloc : ∀ (P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}), ∀ y ∈ (P.1.support : Set Y),
      ∃ U : Y.Opens, y ∈ U ∧
        ∃ τ ∈ pluricanonicalSections sY 3 m (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) U,
          ∀ P₁, ((P₁.1.support : Set Y) ∩ U).Nonempty → IsPoincareResidue sY (j P₁) 2 m τ (s P₁))
    {τ : RationalPluriForms sY 3 m} (hτ : τ ∈ logPluricanonicalSections sY 3 m B)
    (hhor : ∀ P, IsDominant (j P ≫ r) → IsPoincareResidue sY (j P) 2 m τ (s P)) :
    ∀ P, IsPoincareResidue sY (j P) 2 m τ (s P) := by
  intro E
  by_cases hE : IsDominant (j E ≫ r)
  · exact hhor E hE
  haveI : CharZero k := hΓ.1.charZero
  have hYv := hr.isProjectiveVariety
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.isContraction.isProjectiveMorphism
  haveI : IsDominant r := ⟨hr.isContraction.surjective.denseRange⟩
  have hVv := hr.isContraction.isNormalVariety_target
  obtain ⟨P₀, hP₀, y, hyE, hy₀, hry⟩ :=
    exists_isDominant_mem_support_inter hr hΓ hQ hY hV hlc hnef hnef' j hj hdeg E hE
  exact isPoincareResidue_of_mem_support_inter hYv.1 hVv.1 hr.isContraction.comp_eq hY hm hmB α M
    hM hrM rM hrMp hα hαM (j E) (j P₀)
    (topologicalKrullDim_floor_eq_two (sY := sY) hY (j E) E.1 (hj E))
    (topologicalKrullDim_floor_eq_two (sY := sY) hY (j P₀) P₀.1 (hj P₀)) E.1 P₀.1 E.2 P₀.2
    (hj E) (hj P₀)
    (s E) (s P₀) hyE hy₀ hry (fun x hx => by
      obtain ⟨U, hxU, τU, hτU, hres⟩ := hloc E x hx
      exact ⟨U, hxU, τU, hτU, hres E ⟨x, hx, hxU⟩, hres P₀⟩) hτ (hhor P₀ hP₀)

/-- A Galois extension of degree two has a nontrivial automorphism. -/
private theorem exists_algEquiv_ne_one_of_finrank_eq_two {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (h2 : Module.finrank K L = 2) :
    ∃ σ : L ≃ₐ[K] L, σ ≠ 1 := by
  by_contra hno
  push Not at hno
  have : Subsingleton (L ≃ₐ[K] L) := ⟨fun a b => (hno a).trans (hno b).symm⟩
  have h := IsGalois.card_aut_eq_finrank K L
  rw [Nat.card_of_subsingleton (1 : L ≃ₐ[K] L)] at h
  omega

/-- **Fixed points of the involution of a quadratic extension.** If `L / K` has degree two and
`σ ≠ 1` is a `K`-automorphism of `L`, every element fixed by `σ` lies in `K`: otherwise `1, x`
is a `K`-basis of `L` fixed by the `K`-linear map `σ`. -/
private theorem mem_range_algebraMap_of_apply_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) (x : L) (hx : σ x = x) :
    x ∈ Set.range (algebraMap K L) := by
  by_contra hxK
  have hli : LinearIndependent K ![(1 : L), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_contra hne
    have ht : t ≠ 0 := by
      rintro rfl
      simp only [zero_smul, add_zero] at hst
      exact hne ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    apply hxK
    refine ⟨-s / t, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    rw [map_div₀, map_neg]
    have htL : algebraMap K L t ≠ 0 := (map_ne_zero _).mpr ht
    rw [div_eq_iff htL]
    linear_combination -hst
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  apply hσ
  have : σ.toLinearEquiv.toLinearMap = LinearMap.id := by
    apply b.ext
    intro i
    fin_cases i <;> simp [b, hx]
  ext y
  exact congrArg (fun f : L →ₗ[K] L => f y) this

/-- The extension of function fields `f^* : k(X) → k(Y)` of a dominant morphism `f : Y ⟶ X`
over `k`, as a `k`-homomorphism, for any structure morphism `s_Y = f ≫ s_X` of `Y`. -/
private noncomputable def functionFieldHomOfComp {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (h : f ≫ sX = sY) : FunctionFieldHom sY sX := by
  subst h
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  letI := functionFieldMapAlgebra f
  haveI := isScalarTower_functionFieldMap sX f
  exact IsScalarTower.toAlgHom k X.functionField Y.functionField

private theorem functionFieldHomOfComp_apply {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (h : f ≫ sX = sY) (x : X.functionField) :
    functionFieldHomOfComp f h x = functionFieldMap f x := by
  subst h
  rfl

/-- A morphism of irreducible schemes sending the generic point to the generic point is
dominant. -/
private theorem isDominant_of_map_genericPoint_eq {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) : IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hy : y ∈ closure ({genericPoint Y} : Set Y) := by
    rw [(genericPoint_spec Y).def]; trivial
  have hmem : genericPoint Y ∈ Set.range f.base := ⟨genericPoint X, h⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) hy

/-- A nonzero rational function on the base pulls back to a function of order zero along a prime
divisor dominating the base. -/
private theorem ord_functionFieldMap_eq_zero {Y V : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] (r : Y ⟶ V) [IsDominant r]
    (P : Mori.PrimeDivisor Y) (hP : r P.genericPoint = genericPoint V) {x : V.functionField}
    (hx : x ≠ 0) : Y.ord (functionFieldMap r x) P.genericPoint = 0 := by
  have hsp : r P.genericPoint ⤳ genericPoint V := specializes_of_eq hP
  set b := (V.presheaf.stalkSpecializes hsp).hom x with hb
  have hbx : algebraMap _ V.functionField b = x := by
    rw [hb, MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes',
      MMP.CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint]
  have hfield : IsField (V.presheaf.stalk (r P.genericPoint)) := by
    rw [hP]; exact Field.toIsField V.functionField
  have hb0 : b ≠ 0 := by
    rintro hb0
    rw [hb0, map_zero] at hbx
    exact hx hbx.symm
  obtain ⟨c, hc⟩ := hfield.mul_inv_cancel hb0
  have hbu : IsUnit b := IsUnit.of_mul_eq_one c hc
  rw [← hbx, functionFieldMap_algebraMap_stalk]
  exact P.ord_algebraMap_of_isUnit (hbu.map _)

/-- Pluriform pull-back along `φ` is `φ`-semilinear. -/
private theorem pluriformPullback_smul' {k : Type} [Field k] {X X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
    (φ : FunctionFieldHom sX sX') {d : ℕ} {m : ℤ} (c : X'.functionField)
    (τ : RationalPluriForms sX' d m) :
    pluriformPullback sX sX' φ d m (c • τ) = φ c • pluriformPullback sX sX' φ d m τ := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  exact pullbackForms_smul (K := X'.functionField) (K' := X.functionField) c τ

/-- Pull-back of forms along a dominant morphism commutes with subtraction. -/
private theorem pullbackRationalPluriForms_sub {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] {d : ℕ}
    {m : ℤ} (τ τ' : RationalPluriForms sX d m) :
    pullbackRationalPluriForms sX f (τ - τ') =
      pullbackRationalPluriForms sX f τ - pullbackRationalPluriForms sX f τ' := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  letI := functionFieldMapAlgebra f
  haveI := isScalarTower_functionFieldMap sX f
  exact eq_sub_of_add_eq ((pullbackForms_add (K := X.functionField) (K' := Y.functionField)
    (τ - τ') τ').symm.trans (congrArg _ (sub_add_cancel τ τ')))

/-- Pull-back of forms along a dominant morphism is `f^*`-semilinear. -/
private theorem pullbackRationalPluriForms_smul {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsDominant f] {d : ℕ}
    {m : ℤ} (c : X.functionField) (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms sX f (c • τ) =
      functionFieldMap f c • pullbackRationalPluriForms sX f τ := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  letI := functionFieldMapAlgebra f
  haveI := isScalarTower_functionFieldMap sX f
  exact pullbackForms_smul (K := X.functionField) (K' := Y.functionField) c τ

/-- **Forms agreeing to first order have the same residue.** Along an integral closed subscheme
`j : T ⟶ Y` of a normal variety of dimension `n + 1` over a field of characteristic zero, with
generic point that of the prime divisor `P`, let `τ₁, τ₂` be `m`-canonical forms with at most an
`m`-fold pole along `P` (`m = M + 1`) whose difference has order at least `1 - m`. Then `τ₁` and
`τ₂` have the same Poincaré residue: writing `τᵢ = cᵢ σ` along the `m`-th power `σ` of a
logarithmic frame, `c₁ - c₂` lies in the maximal ideal, so `c̄₁ = c̄₂`. -/
private theorem isPoincareResidue_of_le_ordForm_sub {k : Type} [Field k] [CharZero k]
    {Y T : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType sY] {n : ℕ} (hY : topologicalKrullDim Y = n + 1)
    (j : T ⟶ Y) [IsClosedImmersion j] [IsIntegral T] [LocallyOfFiniteType (j ≫ sY)]
    (hT : topologicalKrullDim T = n)
    (P : Mori.PrimeDivisor Y) (hjT : j (genericPoint T) = P.genericPoint) (M : ℕ)
    {τ₁ τ₂ : RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)}
    (h₁ : τ₁ = 0 ∨ -((M + 1 : ℕ) : ℤ) ≤ P.ordForm τ₁)
    (h₂ : τ₂ = 0 ∨ -((M + 1 : ℕ) : ℤ) ≤ P.ordForm τ₂)
    (hδ : τ₁ = τ₂ ∨ 1 - ((M + 1 : ℕ) : ℤ) ≤ P.ordForm (τ₁ - τ₂))
    {ρ : RationalPluriForms (j ≫ sY) n ((M + 1 : ℕ) : ℤ)}
    (hρ : IsPoincareResidue sY j n (M + 1) τ₁ ρ) : IsPoincareResidue sY j n (M + 1) τ₂ ρ := by
  classical
  rcases hδ with hδ | hδ
  · exact hδ ▸ hρ
  letI := stalkAlgebra sY (j (genericPoint T))
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  have hd : (Algebra.trdeg k Y.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; norm_cast)
  obtain ⟨σ₁, hσ₁ord, ρ₁, hσρ₁, hρ₁0⟩ := exists_logFrame sY hd j P hjT
  have hσ₁0 : σ₁ ≠ 0 := by
    rintro rfl
    rw [PrimeDivisor.ordForm_zero] at hσ₁ord
    omega
  set σ := MMP.CyclicChartDifferent.Aux.pluriPow σ₁ M with hσdef
  have hσ0 : σ ≠ 0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero (by exact_mod_cast hY) hσ₁0 M
  have hσord : P.ordForm σ = -((M + 1 : ℕ) : ℤ) := by
    rw [hσdef, MMP.CyclicChartDifferent.Aux.ordForm_pluriPow (by exact_mod_cast hY) hσ₁0 P M,
      hσ₁ord]
    ring
  have hσρ := MMP.CyclicChartDifferent.Aux.isPoincareResidue_pluriPow P hjT
    (by exact_mod_cast hY) hσρ₁ M
  have hrank : Module.finrank Y.functionField
      (RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ)) = 1 :=
    finrank_rationalPluriForms_eq_one_of_topologicalKrullDim sY (d := n + 1)
      (by exact_mod_cast hY) _
  have hspP : j (genericPoint T) ⤳ P.genericPoint := specializes_of_eq hjT
  have hspP' : P.genericPoint ⤳ j (genericPoint T) := specializes_of_eq hjT.symm
  have hmul : ∀ τ : RationalPluriForms sY (n + 1) ((M + 1 : ℕ) : ℤ),
      (τ = 0 ∨ -((M + 1 : ℕ) : ℤ) ≤ P.ordForm τ) →
      ∃ c : Y.presheaf.stalk (j (genericPoint T)), τ = algebraMap _ Y.functionField c • σ := by
    intro τ hτ
    by_cases hτ0 : τ = 0
    · exact ⟨0, by rw [hτ0, map_zero, zero_smul]⟩
    have hτord := hτ.resolve_left hτ0
    obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' σ hσ0).mp hrank τ
    have hf0 : f ≠ 0 := by rintro rfl; exact hτ0 (by rw [← hf, zero_smul])
    have hford : 0 ≤ Y.ord f P.genericPoint := by
      have := P.ordForm_smul (sX := sY) hd hf0 hσ0
      rw [hf, hσord] at this
      omega
    obtain ⟨a, ha⟩ := MMP.CyclicChartDifferent.Aux.exists_algebraMap_eq_of_ord_nonneg P hf0 hford
    refine ⟨(Y.presheaf.stalkSpecializes hspP).hom a, ?_⟩
    rw [MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' Y hspP, ha, hf]
  obtain ⟨c₁, hc₁⟩ := hmul τ₁ h₁
  obtain ⟨c₂, hc₂⟩ := hmul τ₂ h₂
  have hr₁ := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hσρ c₁
  have hr₂ := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hσρ c₂
  rw [← hc₁] at hr₁
  rw [← hc₂] at hr₂
  have e₁ := IsPoincareResidue.unique_of_isClosedImmersion P hjT hρ hr₁
  -- `c₁ - c₂` lies in the maximal ideal, so has zero restriction to `T`
  have hc : (j.stalkMap (genericPoint T)).hom (c₁ - c₂) = 0 := by
    by_contra hne
    have hδσ : τ₁ - τ₂ = algebraMap _ Y.functionField (c₁ - c₂) • σ := by
      rw [hc₁, hc₂, map_sub, sub_smul]
    have hg : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField (c₁ - c₂) ≠ 0 := by
      intro hg
      apply hne
      rw [(IsFractionRing.injective (Y.presheaf.stalk (j (genericPoint T))) Y.functionField
        (hg.trans (map_zero _).symm)), map_zero]
    rw [hδσ, P.ordForm_smul (sX := sY) hd hg hσ0, hσord] at hδ
    set a := (Y.presheaf.stalkSpecializes hspP').hom (c₁ - c₂) with hadef
    have haK : algebraMap _ Y.functionField a =
        algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField (c₁ - c₂) :=
      MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes' Y hspP' _
    have hlt : P.divisorialValuation (algebraMap _ Y.functionField a) < 1 := by
      rw [haK, P.divisorialValuation_eq_exp_neg_ord hg, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hamax := (P.divisorialValuation_algebraMap_lt_one_iff a).mp hlt
    have hback : (Y.presheaf.stalkSpecializes hspP).hom a = c₁ - c₂ := by
      rw [hadef, ← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
        TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    have hu : IsUnit ((j.stalkMap (genericPoint T)).hom (c₁ - c₂)) := Ne.isUnit hne
    have hu' : IsUnit (c₁ - c₂) := isUnit_of_map_unit _ _ hu
    rw [← hback] at hu'
    have hu'' := hu'.map (Y.presheaf.stalkSpecializes hspP').hom
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
      TopCat.Presheaf.stalkSpecializes_refl] at hu''
    exact (IsLocalRing.mem_maximalIdeal _).mp hamax hu''
  rw [map_sub, sub_eq_zero] at hc
  rw [e₁, hc]
  exact hr₂

/-- **Admissible systems are invariant under crepant maps of components.** For an admissible
section system `s` (`MMP.Fourfold.admissibleSections`) and a crepant birational map
`σ : (X_i, B_i) ⇢ (X_{i'}, B_{i'})` between two of the pairs themselves (flags of length zero),
`σ^* s_{i'} = s_i`. -/
private theorem pluriformPullback_eq_of_mem_admissibleSections {k : Type} [Field k] [CharZero k]
    {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)} [∀ i, IsIntegral (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)] {B : ∀ i, QDivisor (X i)} {n m : ℕ}
    {R : ResidueRestriction sX B n m} {s : ∀ i, logPluricanonicalSections (sX i) n m (B i)}
    (hs : s ∈ admissibleSections R) (i i' : I) (σ : FunctionFieldEquiv (sX i) (sX i'))
    (hσ : IsCrepantBirationalMap (sX i) (sX i') (B i) (B i') σ) :
    pluriformPullback (sX i) (sX i') σ.toHom n m (s i' : RationalPluriForms (sX i') n m) =
      (s i : RationalPluriForms (sX i) n m) := by
  have hp := (R.setting.isPair i).isPair
  have hp' := (R.setting.isPair i').isPair
  have hS := R.setting.topologicalKrullDim_eq i
  have hS' := R.setting.topologicalKrullDim_eq i'
  have h := hs i i' (.refl hp) (.refl hp') n (Nat.zero_le _) (Nat.zero_le _) hS hS'
  have e1 := IsIteratedResidue.unique (R.isIteratedResidue i (.refl hp) n (s i) hS)
    (IsIteratedResidue.refl hp)
  have e2 := IsIteratedResidue.unique (R.isIteratedResidue i' (.refl hp') n (s i') hS')
    (IsIteratedResidue.refl hp')
  rw [e1, e2] at h
  have key : ∀ (s₁ : X i ⟶ Spec (.of k)) (s₂ : X i' ⟶ Spec (.of k)) (h₁ : sX i = s₁)
      (h₂ : sX i' = s₂),
      (∀ σ : FunctionFieldEquiv s₁ s₂, IsCrepantBirationalMap s₁ s₂ (B i) (B i') σ →
        pluriformPullback s₁ s₂ σ.toHom n m
          (cast (congrArg (fun s => RationalPluriForms s n m) h₂)
            (s i' : RationalPluriForms (sX i') n m)) =
          cast (congrArg (fun s => RationalPluriForms s n m) h₁)
            (s i : RationalPluriForms (sX i) n m)) →
      pluriformPullback (sX i) (sX i') σ.toHom n m (s i' : RationalPluriForms (sX i') n m) =
        (s i : RationalPluriForms (sX i) n m) := by
    intro s₁ s₂ h₁ h₂ H
    subst h₁ h₂
    exact H σ hσ
  exact key _ _ (Category.id_comp _).symm (Category.id_comp _).symm h

/-- **Strict transforms on a crepant model.** Let `p : Y' ⟶ Y` be a proper birational morphism
onto a normal variety of dimension three and `B'` the crepant boundary of `(Y, B)` on `Y'`. Every
prime divisor `P` of `Y` has a strict transform `P'`: `p` maps `η_{P'}` to `η_P`, is a local
isomorphism there, and `coeff_{P'} B' = coeff_P B`, since a local generator `τ` of
`𝒪_Y(m(K_Y + B))` near `η_P` has `ord_{P'} p^*τ = ord_P τ = -m coeff_P B`. -/
private theorem exists_strictTransform {k : Type} [Field k] [PerfectField k] {Y Y' : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [LocallyOfFiniteType sY] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hY : topologicalKrullDim Y = 3) (p : Y' ⟶ Y) [IsProper p] {KY : Divisor Y}
    {B : QDivisor Y} {B' : QDivisor Y'} {hY' : IsNormalVariety k (p ≫ sY)}
    {hp : IsBirationalMorphism p} (hcb : IsCrepantBoundary sY 3 KY B p hY' hp B')
    (P : Mori.PrimeDivisor Y) :
    ∃ P' : Mori.PrimeDivisor Y', p P'.genericPoint = P.genericPoint ∧
      IsIso (p.stalkMap P'.genericPoint) ∧ B'.coeff P' = B.coeff P := by
  haveI : IsDominant p := hp.isDominant
  have hb : P.genericPoint ∈ Mori.biregularLocus p :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal p hp
      P.coheight_genericPoint.le
  obtain ⟨P', -, hη⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P hb
  haveI hiso : IsIso (p.stalkMap P'.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus p (hη ▸ hb)
  refine ⟨P', hη, hiso, ?_⟩
  obtain ⟨-, -, m, hm, -, U, hU, τ, hτ, hτa⟩ := hcb P'
  letI := functionFieldAlgebra sY
  have hd : (Algebra.trdeg k Y.functionField).toNat = 3 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; rfl)
  have hord : P'.ordForm (pullbackRationalPluriForms sY p τ) = P.ordForm τ :=
    MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p
      (MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective hp) hd P' P hη τ
  change (m : ℚ) * -B'.coeff P' = (P'.ordForm (pullbackRationalPluriForms sY p τ) : ℚ) at hτa
  have hPU : (P.support ∩ U).Nonempty :=
    (P.genericPoint_mem_iff U).mp (by rw [← hη]; exact hU)
  have h2 := hτ.2 P hPU
  rw [hord] at hτa
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have : (m : ℚ) * B'.coeff P' = m * B.coeff P := by linarith
  exact mul_left_cancel₀ hm0 this

/-- **Residues of pulled-back multiples.** If `ρ` is the Poincaré residue of `α` along `T` and
`T` dominates `V`, then the residue of `r^*f · α` is `(f|_T) · ρ` for every `f ∈ k(V)`: the
pull-back `r^*f` lies in the local ring at the generic point of `T`. -/
private theorem isPoincareResidue_functionFieldMap_smul {k : Type} [Field k] {Y V T : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral V]
    [IsIntegral T] {r : Y ⟶ V} [IsDominant r] (j : T ⟶ Y) [IsDominant (j ≫ r)] {n m : ℕ}
    {α : RationalPluriForms sY (n + 1) m} {ρ : RationalPluriForms (j ≫ sY) n m}
    (hρ : IsPoincareResidue sY j n m α ρ) (f : V.functionField) :
    IsPoincareResidue sY j n m (functionFieldMap r f • α) (functionFieldMap (j ≫ r) f • ρ) := by
  have hx : r (j (genericPoint T)) = genericPoint V := by
    rw [← Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
  have hsp : r (j (genericPoint T)) ⤳ genericPoint V := specializes_of_eq hx
  set b' := (V.presheaf.stalkSpecializes hsp).hom f with hb'
  have hb'f : algebraMap _ V.functionField b' = f := by
    rw [hb', MMP.CyclicChartDifferent.Aux.algebraMap_stalkSpecializes',
      MMP.CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint]
  have h := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ
    ((r.stalkMap (j (genericPoint T))).hom b')
  rw [← functionFieldMap_algebraMap_stalk, hb'f] at h
  convert h using 2
  have h2 := functionFieldMap_algebraMap_stalk (j ≫ r) (genericPoint T) b'
  refine (congrArg (functionFieldMap (j ≫ r)) hb'f.symm).trans (h2.trans ?_)
  rw [Scheme.Hom.stalkMap_comp]
  exact MMP.CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint T _

end Proof_lem_fourfold_mori_threefold_two_floor_section_descent

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

open MMP Proof_lem_fourfold_mori_threefold_two_floor_section_descent in
/-- **Admissible floor sections descend through a two-floor Mori curve fibration.** Let
`r : Y ⟶ V` be a Mori fibre space (`MMP.Fourfold.IsMoriFibreSpace`) from a `ℚ`-factorial
projective threefold onto a normal projective surface, with `-(K + Γ)` `r`-ample for a klt
boundary `Γ`. Let `B` be an lc boundary with `K + B` numerically trivial over `V`, with
`(Y, B - ε⌊B⌋)` klt for some `ε > 0`, whose floor components `F P` (the prime divisors with
coefficient one) dominating `V` have total degree `∑ [k(F P) : k(V)] = 2`. Then for every
sufficiently divisible even `m`, every crepant dlt model `p : Y' ⟶ Y` of `(Y, B)` with floor
components `(S, B_S)` and residue-restriction system `R`, and every family `s_a` of sections of
`m(K + B)` on the reduced floor of `Y` (families of forms `s_a P` on the `F P` that are locally
residues of local sections of `𝒪_Y(mK + ⌊mB⌋)`) whose pull-backs to the floor components of `Y'`
are admissible (`MMP.Fourfold.admissibleSections`):
* each `s_a` is the floor restriction, by Poincaré residues, of a unique global section of
  `m(K + B)`, that is, of the pull-back of a section of the invertible sheaf `M` with
  `m(K + B) = r^*M`;
* if the `s_a` generate `m(K + B)` on the floor at every point, then every point of `V` has an
  open neighbourhood `U` such that the extension of some `s_a` generates `m(K + B)` on `r⁻¹(U)`:
  the descended family generates `M` on `V`, and its pull-back generates `m(K + B)` on `Y`. -/
@[mmp "lem_fourfold_mori_threefold_two_floor_section_descent"]
public theorem IsMoriFibreSpace.existsUnique_isPoincareResidue_of_mem_admissibleSections
    {k : Type} [Field k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V]
    {r : Y ⟶ V} {K : Divisor Y} {Γ : QDivisor Y}
    (hr : IsMoriFibreSpace sY sV K Γ r) (hΓ : IsKltPair sY Γ) (hQ : IsQFactorial sY)
    (hY : topologicalKrullDim Y = 3) (hV : topologicalKrullDim V = 2)
    {B : QDivisor Y} (hlc : MMP.Intersection.IsLogCanonicalPair sY B)
    (hnef : QDivisor.IsRelativelyNef sY r (Divisor.toQDivisor K + B))
    (hnef' : QDivisor.IsRelativelyNef sY r (-(Divisor.toQDivisor K + B)))
    (hklt : ∃ ε : ℚ, 0 < ε ∧ IsKltPair sY (B - ε • Divisor.toQDivisor B.roundDown))
    {F : {P : Mori.PrimeDivisor Y // B.coeff P = 1} → Scheme.{0}} [∀ P, IsIntegral (F P)]
    (j : ∀ P, F P ⟶ Y) [∀ P, IsClosedImmersion (j P)]
    (hj : ∀ P, Set.range (j P).base = (P.1.support : Set Y))
    (hdeg : ∑ᶠ (P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}) (_ : IsDominant (j P ≫ r)),
      (letI : IsDominant (j P ≫ r) := ‹_›
       letI := functionFieldMapAlgebra (j P ≫ r)
       Module.finrank V.functionField (F P).functionField) = 2) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → Even m →
      ∀ {Y' : Scheme.{0}} [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] (p : Y' ⟶ Y)
        [IsDominant p], IsProjectiveMorphism p → ∀ {B' : QDivisor Y'},
        (∃ (KY : Divisor Y) (hY' : IsNormalVariety k (p ≫ sY)) (hp : IsBirationalMorphism p),
          IsCrepantBoundary sY 3 KY B p hY' hp B') →
        MMP.Intersection.IsDltPair (p ≫ sY) B' →
        ∀ {S : {P' : Mori.PrimeDivisor Y' // B'.coeff P' = 1} → Scheme.{0}}
          [∀ P', IsIntegral (S P')] [∀ P', IsLocallyNoetherian (S P')] [∀ P', IsNormal (S P')]
          (j' : ∀ P', S P' ⟶ Y') (BS : ∀ P', QDivisor (S P')),
          (∀ P', IsAdjunctionStep (p ≫ sY) B' (j' P') (BS P') ∧
            Set.range (j' P').base = (P'.1.support : Set Y')) →
        ∀ (R : ResidueRestriction (fun P' => j' P' ≫ p ≫ sY) BS 2 m) {A : Type v}
          (s : A → ∀ P, RationalPluriForms (j P ≫ sY) 2 m),
          (∀ (a : A) (P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}), ∀ y ∈ (P.1.support : Set Y),
            ∃ U : Y.Opens, y ∈ U ∧
            ∃ τ ∈ pluricanonicalSections sY 3 m (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) U,
              ∀ P₁, ((P₁.1.support : Set Y) ∩ U).Nonempty →
                IsPoincareResidue sY (j P₁) 2 m τ (s a P₁)) →
          (∀ a, ∃ u ∈ admissibleSections R, ∀ P' (U : Y.Opens),
            ∀ τ ∈ pluricanonicalSections sY 3 m (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) U,
              (∀ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1},
                ((P.1.support : Set Y) ∩ U).Nonempty →
                IsPoincareResidue sY (j P) 2 m τ (s a P)) →
              p P'.1.genericPoint ∈ U →
              IsPoincareResidue (p ≫ sY) (j' P') 2 m (pullbackRationalPluriForms sY p τ)
                (u P' : RationalPluriForms (j' P' ≫ p ≫ sY) 2 m)) →
          (∀ a, ∃! τ : RationalPluriForms sY 3 m, τ ∈ logPluricanonicalSections sY 3 m B ∧
            ∀ P, IsPoincareResidue sY (j P) 2 m τ (s a P)) ∧
          ((∀ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}, ∀ y ∈ (P.1.support : Set Y),
              ∃ (a : A) (U : Y.Opens), y ∈ U ∧
              ∃ τ ∈ pluricanonicalSections sY 3 m (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) U,
                GeneratesOn B m U τ ∧ ∀ P₁, ((P₁.1.support : Set Y) ∩ U).Nonempty →
                  IsPoincareResidue sY (j P₁) 2 m τ (s a P₁)) →
            ∀ v : V, ∃ (a : A) (τ : RationalPluriForms sY 3 m),
              τ ∈ logPluricanonicalSections sY 3 m B ∧
              (∀ P, IsPoincareResidue sY (j P) 2 m τ (s a P)) ∧
              ∃ U : V.Opens, v ∈ U ∧ GeneratesOn B m (r ⁻¹ᵁ U) τ) := by
  -- the base is a normal projective surface
  have hVv := hr.isContraction.isNormalVariety_target
  haveI := hVv.1
  haveI : IsNormal V := hVv.2
  haveI : LocallyOfFiniteType sV := hVv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  obtain ⟨m₀, hm₀, hdesc⟩ := exists_descentForm hr hΓ hQ hY hV hlc hnef hnef' hklt j hj hdeg
  refine ⟨m₀, hm₀, fun m hdvd heven Y' _ _ _ p _ hp B' hcrep hdlt S _ _ _ j' BS hBS R A s hloc
    hadm => ?_⟩
  have hm : 0 < m := R.setting.pos
  obtain ⟨hmB, α, M, hM, hrM, rM, hrMp, hα, hαM, ω, hω, hlift⟩ := hdesc m hm hdvd
  -- the extension: admissible floor sections are floor restrictions of global sections
  haveI : IsDominant r := ⟨hr.isContraction.surjective.denseRange⟩
  -- the residue identification: on the horizontal floor, admissibility makes the floor section
  -- the residue of `r^*f · α` for a rational function `f` on `V`
  have hres : ∀ a, ∃ f : V.functionField, ∀ P, IsDominant (j P ≫ r) →
      IsPoincareResidue sY (j P) 2 m (functionFieldMap r f • α) (s a P) := by
    intro a
    haveI : CharZero k := hΓ.1.charZero
    haveI : LocallyOfFiniteType sY := hr.isProjectiveVariety.toLocallyOfFiniteType
    have hηV : genericPoint V ∉ M.supp := by
      obtain ⟨W⟩ : Nonempty (irreducibleComponents Y) :=
        ⟨⟨Set.univ, (irreducibleComponents_eq_singleton (X := Y)).symm ▸ rfl⟩⟩
      have := hrM W
      rwa [componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant r] at this
    -- along a horizontal floor prime, `α` has a pole of order exactly `m` and a nonzero residue
    have hρ : ∀ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1}, IsDominant (j P ≫ r) →
        ∃ ρ : RationalPluriForms (j P ≫ sY) 2 m, IsPoincareResidue sY (j P) 2 m α ρ ∧ ρ ≠ 0 := by
      intro P hP
      have hjT := map_genericPoint_eq_of_range (j P) P.1 (hj P)
      have hPη : r P.1.genericPoint = genericPoint V := by
        rw [← hjT, ← Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
      have h0 := coeff_eq_zero_of_isPullback hrMp P.1 (by rw [hPη]; exact hηV)
      have hord : P.1.ordForm α = -(m : ℤ) := by
        have h1 := hαM P.1
        rw [h0, P.2] at h1
        have : ((P.1.ordForm α : ℤ) : ℚ) = ((-(m : ℤ) : ℤ) : ℚ) := by
          push_cast at h1 ⊢; linarith
        exact_mod_cast this
      obtain ⟨M', rfl⟩ : ∃ M', m = M' + 1 := Nat.exists_eq_succ_of_ne_zero hm.ne'
      obtain ⟨ρ, hρ, hρ0⟩ := exists_isPoincareResidue sY (n := 2) (by rw [hY]; rfl) (j P)
        (topologicalKrullDim_floor_eq_two (sY := sY) hY (j P) P.1 (hj P)) P.1 hjT M'
        (Or.inr hord.ge)
      exact ⟨ρ, hρ, hρ0 hα hord⟩
    choose ρ hρres hρ0 using hρ
    -- the floor section on a horizontal prime is a multiple `g_P` of the residue of `α`
    have hg : ∀ P (hP : IsDominant (j P ≫ r)), ∃ g : (F P).functionField,
        g • ρ P hP = s a P := by
      intro P hP
      letI := functionFieldAlgebra (j P ≫ sY)
      have hrank : Module.finrank (F P).functionField
          (RationalPluriForms (j P ≫ sY) 2 m) = 1 :=
        finrank_rationalPluriForms_eq_one_of_topologicalKrullDim (j P ≫ sY) (d := 2)
          (topologicalKrullDim_floor_eq_two (sY := sY) hY (j P) P.1 (hj P)) _
      exact (finrank_eq_one_iff_of_nonzero' _ (hρ0 P hP)).mp hrank (s a P)
    choose g hg using hg
    -- the residue identification: the coefficients `g_P` are the restrictions of one `f ∈ k(V)`
    obtain ⟨f, hf⟩ : ∃ f : V.functionField, ∀ P (hP : IsDominant (j P ≫ r)),
        g P hP = functionFieldMap (j P ≫ r) f := by
      haveI : IsProper r :=
        isProper_of_isProjectiveMorphism r hr.isContraction.isProjectiveMorphism
      haveI : CharZero V.functionField := by
        letI := functionFieldAlgebra sV
        exact charZero_of_injective_algebraMap (algebraMap k V.functionField).injective
      -- the degree `[k(P) : k(V)]` of a horizontal floor prime
      let d : ∀ P, IsDominant (j P ≫ r) → ℕ := fun P hP =>
        letI := hP
        letI := functionFieldMapAlgebra (j P ≫ r)
        Module.finrank V.functionField (F P).functionField
      have hfin : ∀ P (hP : IsDominant (j P ≫ r)),
          letI := hP
          letI := functionFieldMapAlgebra (j P ≫ r)
          Module.Finite V.functionField (F P).functionField := by
        intro P hP
        letI := hP
        exact MMP.Mori.finite_functionField_of_topologicalKrullDim_eq sV (j P ≫ r)
          (by rw [topologicalKrullDim_floor_eq_two (sY := sY) hY (j P) P.1 (hj P), hV])
      have hdpos : ∀ P hP, 0 < d P hP := by
        intro P hP
        letI := hP
        letI := functionFieldMapAlgebra (j P ≫ r)
        haveI := hfin P hP
        exact Module.finrank_pos
      let φ : {P : Mori.PrimeDivisor Y // B.coeff P = 1} → ℕ := fun P =>
        ∑ᶠ (hP : IsDominant (j P ≫ r)), d P hP
      have hφ : ∀ P hP, φ P = d P hP := fun P hP => by
        classical
        simp only [φ]
        rw [finsum_eq_dif, dif_pos hP]
      have hsum : ∑ᶠ P, φ P = 2 := hdeg
      have hsupp : (Function.support φ).Finite := by
        by_contra hinf
        rw [finsum_of_infinite_support hinf] at hsum
        omega
      have hle : ∀ P, φ P ≤ 2 := fun P =>
        hsum ▸ single_le_finsum P hsupp (fun _ => Nat.zero_le _)
      have hpair : ∀ P Q, P ≠ Q → φ P + φ Q ≤ 2 := by
        classical
        intro P Q hPQ
        rw [← hsum, finsum_eq_sum_of_support_subset φ (s := hsupp.toFinset ∪ {P, Q})
          (fun x hx => Finset.mem_coe.mpr (Finset.mem_union_left _ (hsupp.mem_toFinset.mpr hx))),
          ← Finset.sum_pair hPQ]
        exact Finset.sum_le_sum_of_subset Finset.subset_union_right
      -- the crepant dlt model `(Y', B')` and the admissible system `u` attached to `s a`
      obtain ⟨KY, hY'v, hpb, hcb⟩ := hcrep
      
      obtain ⟨hcl₁, -, hcl₃, hcl₄⟩ := hlift Y' p B' hp ⟨KY, hY'v, hpb, hcb⟩ hdlt
      haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
      haveI : LocallyOfFiniteType (p ≫ sY) := hY'v.1.toLocallyOfFiniteType
      haveI : IsDominant p := hpb.isDominant
      have hY'd : topologicalKrullDim Y' = 3 := by
        haveI := hr.isProjectiveVariety.1
        haveI := hY'v.1
        rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY) hpb,
          hY]
      obtain ⟨u, hu_adm, hu⟩ := hadm a
      have hci : ∀ Q, IsClosedImmersion (j' Q) := fun Q => by
        obtain ⟨-, _, -, -, hc, -⟩ := (hBS Q).1
        exact hc
      have hSd : ∀ Q, topologicalKrullDim (S Q) = 2 := fun Q =>
        topologicalKrullDim_floor_eq_two (sY := p ≫ sY) hY'd (j' Q) Q.1 (hBS Q).2
      letI := functionFieldAlgebra sY
      have hd3 : (Algebra.trdeg k Y.functionField).toNat = 3 :=
        toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) (by rw [hY]; rfl)
      obtain ⟨M', rfl⟩ : ∃ M', m = M' + 1 := Nat.exists_eq_succ_of_ne_zero hm.ne'
      -- strict transforms of the floor primes
      have hQ : ∀ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1},
          ∃ Q : {P' : Mori.PrimeDivisor Y' // B'.coeff P' = 1},
            p Q.1.genericPoint = P.1.genericPoint ∧ IsIso (p.stalkMap Q.1.genericPoint) := by
        intro P
        obtain ⟨P', h1, h2, h3⟩ := exists_strictTransform hY p hcb P.1
        exact ⟨⟨P', h3.trans P.2⟩, h1, h2⟩
      choose Q hQη hQiso using hQ
      have hjQ : ∀ P, j' (Q P) (genericPoint (S (Q P))) = (Q P).1.genericPoint := fun P =>
        map_genericPoint_eq_of_range (j' (Q P)) (Q P).1 (hBS (Q P)).2
      have hPη : ∀ P, IsDominant (j P ≫ r) → r P.1.genericPoint = genericPoint V := by
        intro P hP
        rw [← map_genericPoint_eq_of_range (j P) P.1 (hj P), ← Scheme.Hom.comp_apply,
          map_genericPoint_of_isDominant]
      have hdomQ : ∀ P, IsDominant (j P ≫ r) → IsDominant (j' (Q P) ≫ p ≫ r) := by
        intro P hP
        refine isDominant_of_map_genericPoint_eq _ ?_
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hjQ, hQη, hPη P hP]
      have hordα : ∀ P, IsDominant (j P ≫ r) → P.1.ordForm α = -((M' + 1 : ℕ) : ℤ) := by
        intro P hP
        have h0 := coeff_eq_zero_of_isPullback hrMp P.1 (by rw [hPη P hP]; exact hηV)
        have h1 := hαM P.1
        rw [h0, P.2] at h1
        have : ((P.1.ordForm α : ℤ) : ℚ) = ((-((M' + 1 : ℕ) : ℤ) : ℤ) : ℚ) := by
          push_cast at h1 ⊢; linarith
        exact_mod_cast this
      have hordQ : ∀ P (τ : RationalPluriForms sY 3 ((M' + 1 : ℕ) : ℤ)),
          (Q P).1.ordForm (pullbackRationalPluriForms sY p τ) = P.1.ordForm τ := by
        intro P τ
        haveI := hQiso P
        exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p
          (MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective hpb) hd3 (Q P).1 P.1 (hQη P) τ
      -- the residues of `p^*α` along the strict transforms of the horizontal floor primes
      have hρ' : ∀ P (hP : IsDominant (j P ≫ r)),
          ∃ ρ' : RationalPluriForms (j' (Q P) ≫ p ≫ sY) 2 ((M' + 1 : ℕ) : ℤ),
            IsPoincareResidue (p ≫ sY) (j' (Q P)) 2 (M' + 1) (pullbackRationalPluriForms sY p α)
              ρ' ∧ ρ' ≠ 0 := by
        intro P hP
        haveI := hci (Q P)
        have hord : (Q P).1.ordForm (pullbackRationalPluriForms sY p α) =
            -((M' + 1 : ℕ) : ℤ) := by rw [hordQ, hordα P hP]
        have hα0 : pullbackRationalPluriForms sY p α ≠ 0 := by
          intro h0
          rw [h0, PrimeDivisor.ordForm_zero] at hord
          omega
        obtain ⟨ρ', h1, h2⟩ := exists_isPoincareResidue (p ≫ sY) (n := 2) (by rw [hY'd]; rfl)
          (j' (Q P)) (hSd (Q P)) (Q P).1 (hjQ P) M' (Or.inr hord.ge)
        exact ⟨ρ', h1, h2 hα0 hord⟩
      choose ρ' hρ'res hρ'0 using hρ'
      -- transport of floor coefficients to the crepant model
      have hT : ∀ P (hP : IsDominant (j P ≫ r)) (x : V.functionField),
          g P hP = (letI := hP; functionFieldMap (j P ≫ r) x) ↔
            (u (Q P) : RationalPluriForms (j' (Q P) ≫ p ≫ sY) 2 ((M' + 1 : ℕ) : ℤ)) =
              (letI := hdomQ P hP; functionFieldMap (j' (Q P) ≫ p ≫ r) x) • ρ' P hP := by
        intro P hP x
        haveI := hP
        haveI := hdomQ P hP
        haveI := hci (Q P)
        have hjT := map_genericPoint_eq_of_range (j P) P.1 (hj P)
        have hT2 := topologicalKrullDim_floor_eq_two (sY := sY) hY (j P) P.1 (hj P)
        have hηmem : P.1.genericPoint ∈ (P.1.support : Set Y) := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
        obtain ⟨U, hηU, τ, hτ, hτres⟩ := hloc a P P.1.genericPoint hηmem
        have hτP := hτres P ⟨_, hηmem, hηU⟩
        have hτQ := hu (Q P) U τ hτ hτres (by rw [hQη]; exact hηU)
        set β := functionFieldMap r x • α with hβdef
        have hβP := isPoincareResidue_functionFieldMap_smul (r := r) (j P) (hρres P hP) x
        have hpβ : pullbackRationalPluriForms sY p β =
            functionFieldMap (p ≫ r) x • pullbackRationalPluriForms sY p α := by
          rw [hβdef, pullbackRationalPluriForms_smul,
            MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
        have hβQ : IsPoincareResidue (p ≫ sY) (j' (Q P)) 2 (M' + 1)
            (pullbackRationalPluriForms sY p β)
            (functionFieldMap (j' (Q P) ≫ p ≫ r) x • ρ' P hP) := by
          rw [hpβ]
          exact isPoincareResidue_functionFieldMap_smul (r := p ≫ r) (j' (Q P)) (hρ'res P hP) x
        -- the poles of `τ` and `β` along `P` have order at most `m`
        have hτpole : τ = 0 ∨ -((M' + 1 : ℕ) : ℤ) ≤ P.1.ordForm τ := by
          by_cases hτ0 : τ = 0
          · exact Or.inl hτ0
          right
          have h1 := hτ.2 P.1 ⟨_, hηmem, hηU⟩ hτ0
          rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, P.2, zsmul_eq_mul,
            mul_one] at h1
          have h3 : ⌊(((M' + 1 : ℕ) : ℤ) : ℚ)⌋ = ((M' + 1 : ℕ) : ℤ) := Int.floor_intCast _
          rw [h3] at h1
          omega
        have hβpole : β = 0 ∨ -((M' + 1 : ℕ) : ℤ) ≤ P.1.ordForm β := by
          by_cases hx : x = 0
          · left; rw [hβdef, hx, map_zero, zero_smul]
          right
          have hrx : functionFieldMap r x ≠ 0 := (map_ne_zero _).mpr hx
          rw [hβdef, P.1.ordForm_smul (sX := sY) hd3 hrx hα,
            ord_functionFieldMap_eq_zero r P.1 (hPη P hP) hx, hordα P hP]
          omega
        have hpole' : ∀ τ' : RationalPluriForms sY 3 ((M' + 1 : ℕ) : ℤ),
            (τ' = 0 ∨ -((M' + 1 : ℕ) : ℤ) ≤ P.1.ordForm τ') →
            (pullbackRationalPluriForms sY p τ' = 0 ∨
              -((M' + 1 : ℕ) : ℤ) ≤ (Q P).1.ordForm (pullbackRationalPluriForms sY p τ')) := by
          intro τ' h
          rcases h with h | h
          · left
            rw [h]
            have := pullbackRationalPluriForms_sub (sX := sY) p
              (0 : RationalPluriForms sY 3 ((M' + 1 : ℕ) : ℤ)) 0
            rwa [sub_self, sub_self] at this
          · right; rwa [hordQ]
        -- agreement to first order transfers between `P` and its strict transform
        have hm1 : -((M' + 1 : ℕ) : ℤ) < 1 - ((M' + 1 : ℕ) : ℤ) := by omega
        have hup : (τ = β ∨ 1 - ((M' + 1 : ℕ) : ℤ) ≤ P.1.ordForm (τ - β)) →
            (pullbackRationalPluriForms sY p τ = pullbackRationalPluriForms sY p β ∨
              1 - ((M' + 1 : ℕ) : ℤ) ≤ (Q P).1.ordForm
                (pullbackRationalPluriForms sY p τ - pullbackRationalPluriForms sY p β)) := by
          intro h
          right
          rw [← pullbackRationalPluriForms_sub, hordQ]
          rcases h with h | h
          · rw [h, sub_self, PrimeDivisor.ordForm_zero]; omega
          · exact h
        have hdown : (pullbackRationalPluriForms sY p τ = pullbackRationalPluriForms sY p β ∨
              1 - ((M' + 1 : ℕ) : ℤ) ≤ (Q P).1.ordForm
                (pullbackRationalPluriForms sY p τ - pullbackRationalPluriForms sY p β)) →
            (τ = β ∨ 1 - ((M' + 1 : ℕ) : ℤ) ≤ P.1.ordForm (τ - β)) := by
          intro h
          right
          rw [← hordQ, pullbackRationalPluriForms_sub]
          rcases h with h | h
          · rw [h, sub_self, PrimeDivisor.ordForm_zero]; omega
          · exact h
        constructor
        · intro hgx
          have hβP' : IsPoincareResidue sY (j P) 2 (M' + 1) β (s a P) := by
            rw [← hg P hP, hgx]; exact hβP
          have h1 := isPoincareResidue_sub (n := 2) sY (by rw [hY]; rfl) (j P) hT2 P.1 hjT M'
            hτpole hβpole hτP hβP'
          have h2 := isPoincareResidue_of_le_ordForm_sub (n := 2) (p ≫ sY) (by rw [hY'd]; rfl)
            (j' (Q P)) (hSd (Q P)) (Q P).1 (hjQ P) M' (hpole' τ hτpole) (hpole' β hβpole)
            (hup h1) hτQ
          exact IsPoincareResidue.unique (hBS (Q P)).1 h2 hβQ
        · intro hux
          have hβQ' : IsPoincareResidue (p ≫ sY) (j' (Q P)) 2 (M' + 1)
              (pullbackRationalPluriForms sY p β) (u (Q P)) := by rw [hux]; exact hβQ
          have h1 := isPoincareResidue_sub (n := 2) (p ≫ sY) (by rw [hY'd]; rfl) (j' (Q P))
            (hSd (Q P)) (Q P).1 (hjQ P) M' (hpole' τ hτpole) (hpole' β hβpole) hτQ hβQ'
          have h2 := isPoincareResidue_of_le_ordForm_sub (n := 2) sY (by rw [hY]; rfl) (j P) hT2
            P.1 hjT M' hτpole hβpole (hdown h1) hτP
          have h3 := IsPoincareResidue.unique_of_isClosedImmersion P.1 hjT h2 hβP
          rw [← hg P hP] at h3
          exact smul_left_injective _ (hρ0 P hP) h3
      -- a floor section on a strict transform is a multiple of the residue of `p^*α`
      have hrankQ : ∀ P (hP : IsDominant (j P ≫ r)), ∃ h : (S (Q P)).functionField,
          h • ρ' P hP =
            (u (Q P) : RationalPluriForms (j' (Q P) ≫ p ≫ sY) 2 ((M' + 1 : ℕ) : ℤ)) := by
        intro P hP
        letI := functionFieldAlgebra (j' (Q P) ≫ p ≫ sY)
        have hrank : Module.finrank (S (Q P)).functionField
            (RationalPluriForms (j' (Q P) ≫ p ≫ sY) 2 ((M' + 1 : ℕ) : ℤ)) = 1 :=
          finrank_rationalPluriForms_eq_one_of_topologicalKrullDim (j' (Q P) ≫ p ≫ sY)
            (d := 2) (hSd (Q P)) _
        exact (finrank_eq_one_iff_of_nonzero' _ (hρ'0 P hP)).mp hrank _
      have hrs : r ≫ sV = sY := hr.isContraction.comp_eq
      have hφs : ∀ P, (j' (Q P) ≫ p ≫ r) ≫ sV = j' (Q P) ≫ p ≫ sY := fun P => by
        simp only [Category.assoc, hrs]
      -- the residue of `p^*α` along a horizontal strict transform is the pull-back of `ω`
      have hρ'ω : ∀ P (hP : IsDominant (j P ≫ r)), ρ' P hP =
          (letI := hdomQ P hP
           pluriformPullback (j' (Q P) ≫ p ≫ sY) sV
            (functionFieldHomOfComp (j' (Q P) ≫ p ≫ r) (hφs P)) 2 ((M' + 1 : ℕ) : ℤ) ω) := by
        intro P hP
        haveI := hdomQ P hP
        have h1 := hcl₁ (S (Q P)) (j' (Q P)) (BS (Q P)) (hBS (Q P)).1
          (functionFieldHomOfComp p rfl) (functionFieldHomOfComp (j' (Q P) ≫ p ≫ r) (hφs P))
          (fun x => functionFieldHomOfComp_apply _ _ x)
          (fun x => functionFieldHomOfComp_apply _ _ x)
        have hψα : pluriformPullback (p ≫ sY) sY (functionFieldHomOfComp p rfl) 3
            ((M' + 1 : ℕ) : ℤ) α = pullbackRationalPluriForms sY p α := rfl
        rw [hψα] at h1
        exact IsPoincareResidue.unique (hBS (Q P)).1 (hρ'res P hP) h1
      -- the degree of a strict transform over `V` is that of the floor prime
      have hfrQ : ∀ P (hP : IsDominant (j P ≫ r)), d P hP = 2 →
          (letI := hdomQ P hP
           letI := functionFieldMapAlgebra (j' (Q P) ≫ p ≫ r)
           Module.finrank V.functionField (S (Q P)).functionField) = 2 := by
        intro P hP hd2
        haveI := hP
        haveI := hdomQ P hP
        haveI := hci (Q P)
        haveI := hQiso P
        rw [finrank_functionField_eq_residueDegree (p ≫ r) (j' (Q P)) (Q P).1 (hBS (Q P)).2,
          residueDegree_comp, AlgebraicGeometry.residueDegree_eq_one_of_isIso_stalkMap p, mul_one, hQη,
          ← finrank_functionField_eq_residueDegree r (j P) P.1 (hj P)]
        exact hd2
      -- the residues on the crepant dlt model `(Y', B')`: distinct horizontal branches are
      -- crepant birationally identified over `V` compatibly with the residues of `p^*α`, and a
      -- branch of degree two has such a nontrivial involution
      have hcard₂ : ∀ P₁ P₂ (h₁ : IsDominant (j P₁ ≫ r)) (h₂ : IsDominant (j P₂ ≫ r)), P₁ ≠ P₂ →
          ∃ σ : FunctionFieldEquiv (j' (Q P₁) ≫ p ≫ sY) (j' (Q P₂) ≫ p ≫ sY),
            IsCrepantBirationalMap (j' (Q P₁) ≫ p ≫ sY) (j' (Q P₂) ≫ p ≫ sY) (BS (Q P₁))
              (BS (Q P₂)) σ ∧
            (∀ x : V.functionField,
              σ (letI := hdomQ P₂ h₂; functionFieldMap (j' (Q P₂) ≫ p ≫ r) x) =
                (letI := hdomQ P₁ h₁; functionFieldMap (j' (Q P₁) ≫ p ≫ r) x)) ∧
            pluriformPullback (j' (Q P₁) ≫ p ≫ sY) (j' (Q P₂) ≫ p ≫ sY) σ.toHom 2
              ((M' + 1 : ℕ) : ℤ) (ρ' P₂ h₂) = ρ' P₁ h₁ := by
        intro P₁ P₂ h₁ h₂ hne
        haveI := hdomQ P₁ h₁
        haveI := hdomQ P₂ h₂
        letI := functionFieldAlgebra (j' (Q P₁) ≫ p ≫ sY)
        letI := functionFieldAlgebra (j' (Q P₂) ≫ p ≫ sY)
        letI := functionFieldAlgebra sV
        have hne' : Set.range (j' (Q P₁)).base ≠ Set.range (j' (Q P₂)).base := by
          rw [(hBS (Q P₁)).2, (hBS (Q P₂)).2]
          intro heq
          apply hne
          have g1 : IsGenericPoint (Q P₁).1.genericPoint ((Q P₁).1.support : Set Y') := by
            rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
          have g2 : IsGenericPoint (Q P₂).1.genericPoint ((Q P₂).1.support : Set Y') := by
            rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
          rw [heq] at g1
          have h2 : P₁.1.genericPoint = P₂.1.genericPoint := by rw [← hQη, ← hQη, g1.eq g2]
          exact Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h2)
        obtain ⟨σ, hσ, hσV⟩ := hcl₃ (S (Q P₁)) (j' (Q P₁)) (BS (Q P₁)) (S (Q P₂)) (j' (Q P₂))
          (BS (Q P₂)) (hBS _).1 (hBS _).1 hne'
        refine ⟨σ, hσ, hσV, ?_⟩
        rw [hρ'ω P₁ h₁, hρ'ω P₂ h₂, pluriformPullback_comp (hX := hSd (Q P₁)) (hX' := hSd (Q P₂))
          (hX'' := hV)]
        have hcomp : σ.toHom.comp (functionFieldHomOfComp (j' (Q P₂) ≫ p ≫ r) (hφs P₂)) =
            functionFieldHomOfComp (j' (Q P₁) ≫ p ≫ r) (hφs P₁) := by
          refine AlgHom.ext fun x => ?_
          rw [AlgHom.comp_apply, functionFieldHomOfComp_apply, functionFieldHomOfComp_apply]
          exact hσV x
        rw [hcomp]
      have hcard₁ : ∀ P (hP : IsDominant (j P ≫ r)), d P hP = 2 →
          ∃ σ : FunctionFieldEquiv (j' (Q P) ≫ p ≫ sY) (j' (Q P) ≫ p ≫ sY), σ ≠ 1 ∧
            IsCrepantBirationalMap (j' (Q P) ≫ p ≫ sY) (j' (Q P) ≫ p ≫ sY) (BS (Q P))
              (BS (Q P)) σ ∧
            (∀ x : V.functionField,
              σ (letI := hdomQ P hP; functionFieldMap (j' (Q P) ≫ p ≫ r) x) =
                (letI := hdomQ P hP; functionFieldMap (j' (Q P) ≫ p ≫ r) x)) ∧
            pluriformPullback (j' (Q P) ≫ p ≫ sY) (j' (Q P) ≫ p ≫ sY) σ.toHom 2
              ((M' + 1 : ℕ) : ℤ) (ρ' P hP) = ρ' P hP := by
        intro P hP hd2
        haveI := hdomQ P hP
        letI := functionFieldAlgebra (j' (Q P) ≫ p ≫ sY)
        letI := functionFieldAlgebra sV
        obtain ⟨σ, hσ1, -, hσ, hσV⟩ := hcl₄ (S (Q P)) (j' (Q P)) (BS (Q P)) (hBS _).1
          (hfrQ P hP hd2)
        refine ⟨σ, hσ1, hσ, hσV, ?_⟩
        rw [hρ'ω P hP, pluriformPullback_comp (hX := hSd (Q P)) (hX' := hSd (Q P)) (hX'' := hV)]
        have hcomp : σ.toHom.comp (functionFieldHomOfComp (j' (Q P) ≫ p ≫ r) (hφs P)) =
            functionFieldHomOfComp (j' (Q P) ≫ p ≫ r) (hφs P) := by
          refine AlgHom.ext fun x => ?_
          rw [AlgHom.comp_apply, functionFieldHomOfComp_apply]
          exact hσV x
        rw [hcomp]
      -- (D1) on a branch of degree two, `g_P` is fixed by the Galois involution over `k(V)`
      have hD1 : ∀ P (hP : IsDominant (j P ≫ r)), d P hP = 2 →
          letI := hP
          letI := functionFieldMapAlgebra (j P ≫ r)
          ∀ θ : (F P).functionField ≃ₐ[V.functionField] (F P).functionField,
            θ (g P hP) = g P hP := by
        intro P hP hd2
        haveI := hP
        haveI := hdomQ P hP
        haveI := hci (Q P)
        haveI := hQiso P
        letI := functionFieldAlgebra (j' (Q P) ≫ p ≫ sY)
        obtain ⟨σ, hσ1, hσ, hσV, hσρ⟩ := hcard₁ P hP hd2
        obtain ⟨h, hh⟩ := hrankQ P hP
        have hadmσ := pluriformPullback_eq_of_mem_admissibleSections hu_adm (Q P) (Q P) σ hσ
        rw [← hh, pluriformPullback_smul', hσρ] at hadmσ
        have hfix : σ h = h := smul_left_injective _ (hρ'0 P hP) hadmσ
        obtain ⟨x, hx⟩ : ∃ x, functionFieldMap (j' (Q P) ≫ p ≫ r) x = h := by
          letI := functionFieldMapAlgebra (j' (Q P) ≫ p ≫ r)
          let σ' : (S (Q P)).functionField ≃ₐ[V.functionField] (S (Q P)).functionField :=
            { σ.toRingEquiv with commutes' := hσV }
          have hσ'1 : σ' ≠ 1 := by
            intro h1
            apply hσ1
            exact AlgEquiv.ext fun z => DFunLike.congr_fun h1 z
          exact mem_range_algebraMap_of_apply_eq (hfrQ P hP hd2) σ' hσ'1 h hfix
        letI := functionFieldMapAlgebra (j P ≫ r)
        intro θ
        have hgx := (hT P hP x).mpr (by rw [← hh, hx])
        rw [hgx]
        exact θ.commutes x
      -- (D2) on two distinct horizontal branches the coefficients `g_P` agree over `k(V)`
      have hD2 : ∀ P Q' (hP : IsDominant (j P ≫ r)) (hQ' : IsDominant (j Q' ≫ r)), P ≠ Q' →
          ∀ x : V.functionField, g P hP = (letI := hP; functionFieldMap (j P ≫ r) x) →
            g Q' hQ' = (letI := hQ'; functionFieldMap (j Q' ≫ r) x) := by
        intro P₁ P₂ h₁ h₂ hne x hx
        letI := functionFieldAlgebra (j' (Q P₁) ≫ p ≫ sY)
        letI := functionFieldAlgebra (j' (Q P₂) ≫ p ≫ sY)
        obtain ⟨σ, hσ, hσV, hσρ⟩ := hcard₂ P₁ P₂ h₁ h₂ hne
        have hu₁ := (hT P₁ h₁ x).mp hx
        obtain ⟨h, hh⟩ := hrankQ P₂ h₂
        have hadmσ := pluriformPullback_eq_of_mem_admissibleSections hu_adm (Q P₁) (Q P₂) σ hσ
        rw [← hh, pluriformPullback_smul', hσρ, hu₁] at hadmσ
        have h1 := smul_left_injective _ (hρ'0 P₁ h₁) hadmσ
        have hh' : h = (letI := hdomQ P₂ h₂; functionFieldMap (j' (Q P₂) ≫ p ≫ r) x) :=
          σ.injective (h1.trans (hσV x).symm)
        exact (hT P₂ h₂ x).mpr (by rw [← hh, hh'])
      -- a horizontal floor prime
      obtain ⟨P₀, h₀⟩ : ∃ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1},
          IsDominant (j P ≫ r) :=
        exists_of_finsum_finsum_ne_zero hdeg two_ne_zero
      have hd₀ : d P₀ h₀ = 1 ∨ d P₀ h₀ = 2 := by
        have h1 := hle P₀
        rw [hφ P₀ h₀] at h1
        have := hdpos P₀ h₀
        omega
      letI := h₀
      letI := functionFieldMapAlgebra (j P₀ ≫ r)
      obtain ⟨x, hx⟩ : ∃ x, functionFieldMap (j P₀ ≫ r) x = g P₀ h₀ := by
        rcases hd₀ with h1 | h2
        · exact ((Algebra.finrank_eq_one_iff_bijective_algebraMap (F := V.functionField)
            (E := (F P₀).functionField)).mp h1).2 (g P₀ h₀)
        · haveI := hfin P₀ h₀
          haveI : Algebra.IsQuadraticExtension V.functionField (F P₀).functionField :=
            { finrank_eq_two' := h2 }
          obtain ⟨θ, hθ⟩ := exists_algEquiv_ne_one_of_finrank_eq_two h2
          exact mem_range_algebraMap_of_apply_eq h2 θ hθ _ (hD1 P₀ h₀ h2 θ)
      refine ⟨x, fun P hP => ?_⟩
      by_cases hPP : P₀ = P
      · subst hPP
        exact hx.symm
      rcases hd₀ with h1 | h2
      · exact hD2 P₀ P h₀ hP hPP x hx.symm
      · have h3 := hpair P₀ P hPP
        rw [hφ P₀ h₀, hφ P hP] at h3
        have := hdpos P hP
        omega
    refine ⟨f, fun P hP => ?_⟩
    haveI := hP
    have := isPoincareResidue_functionFieldMap_smul (r := r) (j P) (hρres P hP) f
    rwa [← hf P hP, hg P hP] at this
  -- horizontal descent: such an `r^*f · α` is a global section
  have hhor : ∀ a, ∃ f : V.functionField,
      functionFieldMap r f • α ∈ logPluricanonicalSections sY 3 m B ∧
      ∀ P, IsDominant (j P ≫ r) →
        IsPoincareResidue sY (j P) 2 m (functionFieldMap r f • α) (s a P) := by
    intro a
    obtain ⟨f, hf⟩ := hres a
    haveI : CharZero k := hΓ.1.charZero
    haveI : LocallyOfFiniteType sY := hr.isProjectiveVariety.toLocallyOfFiniteType
    haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.isContraction.isProjectiveMorphism
    obtain ⟨P₀, hdom⟩ : ∃ P : {P : Mori.PrimeDivisor Y // B.coeff P = 1},
        IsDominant (j P ≫ r) :=
      exists_of_finsum_finsum_ne_zero hdeg two_ne_zero
    have hP₀ : r.base '' (P₀.1.support : Set Y) = Set.univ := by
      have hrange : Set.range (j P₀ ≫ r).base = r.base '' (P₀.1.support : Set Y) := by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hj]
      have hcl : IsClosed (r.base '' (P₀.1.support : Set Y)) :=
        r.isClosedMap _ (hj P₀ ▸ (j P₀).isClosedEmbedding.isClosed_range)
      have hdense := hdom.denseRange
      rw [DenseRange, hrange] at hdense
      exact hcl.closure_eq ▸ hdense.closure_eq
    refine ⟨f, mem_logPluricanonicalSections_of_isPoincareResidue hY hm hmB α M hM hrM rM hrMp
      hα hαM (j P₀) (topologicalKrullDim_floor_eq_two (sY := sY) hY (j P₀) P₀.1 (hj P₀)) P₀.1
      P₀.2 (hj P₀) hP₀ (s a P₀) (fun y hy => ?_) f (hf P₀ hdom), hf⟩
    obtain ⟨U, hyU, τ, hτ, hτres⟩ := hloc a P₀ y hy
    exact ⟨U, hyU, τ, hτ, hτres P₀ ⟨y, hy, hyU⟩⟩
  -- the extension: agreement on the horizontal floor propagates to the vertical floor
  have hext : ∀ a, ∃ τ : RationalPluriForms sY 3 m, τ ∈ logPluricanonicalSections sY 3 m B ∧
      ∀ P, IsPoincareResidue sY (j P) 2 m τ (s a P) := by
    intro a
    obtain ⟨f, hf, hfres⟩ := hhor a
    exact ⟨_, hf, isPoincareResidue_of_forall_isDominant hr hΓ hQ hY hV hlc hnef hnef' j hj hdeg
      hm hmB α M hM hrM rM hrMp hα hαM (s a) (hloc a) hf hfres⟩
  refine ⟨fun a => ?_, fun hgen v =>
    exists_generatesOn_of_forall_exists hr hΓ hY hV j hj hdeg hm α M hM hrM rM hrMp hα hαM hmB s
      hext hgen v⟩
  obtain ⟨τ, hτ, hτs⟩ := hext a
  exact ⟨τ, ⟨hτ, hτs⟩, fun τ' hτ' => eq_of_forall_isPoincareResidue hr hΓ hY hV j hj hdeg hm α M
    hM hrM rM hrMp hα hαM hmB (s a) hτ'.1 hτ hτ'.2 hτs⟩

end MMP.Fourfold
