module

public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization

/-!
# A log resolution making the restricted boundary terminal

Let `(X, S + B)` be a plt pair on a normal `ℚ`-factorial variety over an algebraically closed
field of characteristic zero, with `S` prime, `B ≥ 0`, `S` not a component of `B` and all
coefficients of `B` below one. There is a log resolution `f : Y ⟶ X` with
`K_Y + Γ₀ = f^*(K_X + S + B) + E`, `Γ₀, E ≥ 0` without common components, `E` exceptional, the
strict transform `T` of `S` the only component of `Γ₀` with coefficient one, and
`Ψ₀ = (Γ₀ - T)|_T` an effective snc boundary on the smooth `T` with `(T, Ψ₀)` real terminal.

The construction has three steps.

1. *An `H`-projective log resolution.* A normal compactification of `X` (Nagata's theorem and
   normalization) is dominated, by Chow's lemma, by a projective variety; its inverse image `Z` of
   `X` carries an ample invertible sheaf and maps `H`-projectively and birationally onto `X`.
   Principalizing on `Z` the ideal of the inverse image of `Supp(S + B)` and of the locus over
   which `Z ⟶ X` is not an isomorphism gives the log resolution. Its exceptional set is a
   divisor because `X` is `ℚ`-factorial.
2. *Separating the components of positive crepant coefficient.* Writing `a(P)` for the log
   discrepancy of a configuration divisor `P`, blow up the components of `P ∩ Q` whenever
   `a(P), a(Q) > 0` and `a(P) + a(Q) < 2`. The exceptional divisor has log discrepancy at least
   `a(P) + a(Q)`, the strict transforms keep theirs, and integer weights bounding the positive
   log discrepancies from below make a multiset measure decrease for the Dershowitz–Manna order,
   so the process terminates. All blow-ups have smooth centres on a source carrying an ample
   sheaf, so `H`-projectivity persists. Afterwards two meeting configuration divisors with
   positive log discrepancies have `a(P) + a(Q) ≥ 2`. Hence the components of `Γ₀` other than
   `T`, whose log discrepancies lie in `(0, 1)`, are pairwise disjoint.
3. *The restriction to `T`.* Every component of `Ψ₀` lies in exactly one component `P` of
   `Γ₀ - T` and has the coefficient of `P`. Two components of `Ψ₀` in the same `P` are disjoint,
   since `P ∩ T` is smooth, so no two components of `Ψ₀` meet. The snc discrepancy formula then
   gives `discrep(T, Ψ₀) > 0`.

## Main results

* `MMP.Fourfold.exists_isLogResolution_isRealTerminalPair_restrictPrimeDivisor`.

## Implementation notes

The source blows up the codimension-three strata `T ∩ D_i ∩ D_j` with `b_i + b_j ≥ 1`, and bounds
the number of steps by the finiteness of the valuations of log discrepancy at most one over the
klt pair `(T, Ψ₀)`. Here the codimension-two strata `D_i ∩ D_j` of the configuration on `Y` are
blown up instead, until the components of positive crepant coefficient other than `T` are
pairwise disjoint. Termination is then the Dershowitz–Manna argument on `Y`, and the restriction
to `T` needs no further blow-up. The resolution is `H`-projective (a closed subscheme of a
projective space over `X`), which over an arbitrary variety `X` needs the detour through a
projective model given by Chow's lemma.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], 2.31
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12
-/

open CategoryTheory AlgebraicGeometry
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

section Opens

open MMP.Mori

/-! ### Isomorphisms over opens -/

/-- A morphism which is an isomorphism over a nonempty open has points over it. -/
private theorem nonempty_preimage_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  exact ⟨((inv (g ∣_ V)) ⟨x, hx⟩).1, ((inv (g ∣_ V)) ⟨x, hx⟩).2⟩

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : IsBirationalMorphism g := by
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    (nonempty_preimage_of_isIso_restrict g V hV) hV le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- A composite of isomorphisms over `V` and over its inverse image is an isomorphism over `V`. -/
private theorem isIso_restrict_comp {X Y W : Scheme.{u}} (h : W ⟶ Y) (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] [IsIso (h ∣_ g ⁻¹ᵁ V)] : IsIso ((h ≫ g) ∣_ V) := by
  rw [morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›

end Opens

open CategoryTheory AlgebraicGeometry MMP MMP.Flips TopologicalSpace
open MMP.Mori hiding IsLogResolution exceptionalSet

section Setup

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  (n : ℕ) (K : Divisor X) (D : RDivisor X)

/-- `(X, D)` is *sub-lc*: `X` is a normal variety, `K` is a canonical divisor, `K + D` is
`ℝ`-Cartier and `a_ℓ(F, D) ≥ 0` for every divisor `F` of `k(X)` with nonempty center on `X`. Unlike
`MMP.Flips.IsKawamataLogTerminal`, the divisor `D` is not required to be a boundary. -/
private def IsSubLc : Prop :=
  IsNormalVariety k sX ∧ K.IsCanonicalDivisor sX n ∧
    IsCartierCombination (Divisor.toRDivisor K + D) ∧
    ∀ F : Valuation X.functionField ℤᵐ⁰, HasNonemptyCenter k sX F →
      ∀ b : ℝ, IsLogDiscrepancy sX n K D F b → 0 ≤ b

/-- The configuration `Ex(f) ∪ f⁻¹(Supp D)` of a morphism `f : Y ⟶ X`. -/
private def cfg {Y : Scheme.{u}} (f : Y ⟶ X) : Closeds Y :=
  Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous

/-- `a` is a log discrepancy over `(X, D)` of the prime divisor `P` of the model `f : Y ⟶ X`. -/
private def IsLD {Y : Scheme.{u}} (f : Y ⟶ X) (P : Mori.PrimeDivisor Y) (a : ℝ) : Prop :=
  ∃ (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (hp : IsProper f),
    IsLogDiscrepancy sX n K D (ProperDivisorOver.mk ⟨Y, f, hY, hf, P⟩ hp).valuation a

/-- A *bad* triple `(P, Q, W)`: `P ≠ Q` configuration divisors, `W` a component of `P ∩ Q`, and
log discrepancies of `P` and `Q` with sum `< 2`. -/
private def IsBad {Y : Scheme.{u}} (f : Y ⟶ X)
    (t : Mori.PrimeDivisor Y × Mori.PrimeDivisor Y × Set Y) : Prop :=
  (t.1.support : Set Y) ⊆ cfg D f ∧ (t.2.1.support : Set Y) ⊆ cfg D f ∧ t.1 ≠ t.2.1 ∧
    t.2.2 ∈ Resolution.componentsOf (t.1.support ∩ t.2.1.support : Set Y) ∧
    ∃ a b, IsLD sX n K D f t.1 a ∧ IsLD sX n K D f t.2.1 b ∧ 0 < a ∧ 0 < b ∧ a + b < 2

/-- The invariant of the blow-up procedure: a Kollár–Mori log resolution together with weights
`w ≥ 1` on the configuration divisors bounding their log discrepancies below by `c · w`. -/
private structure Good (c : ℝ) {Y : Scheme.{u}} (f : Y ⟶ X) (w : Mori.PrimeDivisor Y → ℕ) :
    Prop where
  log : Mori.IsLogResolution sX D f
  proj : IsProjectiveMorphism f
  ample : ∃ (L : Y.Modules) (hL : Stacks.Ample.IsInvertibleModule Y L),
    letI : Stacks.Ample.IsInvertibleModule Y L := hL
    Stacks.Ample.IsAmple Y L
  weight : ∀ P : Mori.PrimeDivisor Y, (P.support : Set Y) ⊆ cfg D f →
    1 ≤ w P ∧ ∀ a, IsLD sX n K D f P a → 0 < a → c * w P ≤ a

open Classical in
/-- The multiset of the numbers `N - (w P + w Q)` over the bad triples `(P, Q, W)`. -/
private noncomputable def measure (N : ℕ) {Y : Scheme.{u}} (f : Y ⟶ X)
    (w : Mori.PrimeDivisor Y → ℕ) : Multiset ℕ :=
  if h : (setOf (IsBad sX n K D f)).Finite then
    h.toFinset.val.map fun t => N - (w t.1 + w t.2.1)
  else 0

end Setup

section Helpers

open MMP.Fourfold.SNCWeight

/-! ### Prime divisors and closed sets -/

/-- A prime divisor lies in a closed set exactly when its generic point does. -/
private theorem support_subset_iff {Y : Scheme.{u}} (P : Mori.PrimeDivisor Y) {T : Set Y}
    (hT : IsClosed T) : (P.support : Set Y) ⊆ T ↔ P.genericPoint ∈ T := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ⟨fun h => h (subset_closure rfl),
    fun h => closure_minimal (Set.singleton_subset_iff.mpr h) hT⟩

/-- A prime divisor whose generic point lies on another one is that one. -/
private theorem eq_of_genericPoint_mem_support {Y : Scheme.{u}} {P Q : Mori.PrimeDivisor Y}
    (h : P.genericPoint ∈ (Q.support : Set Y)) : P = Q :=
  PrimeDivisorUnion.eq_of_support_subset
    ((support_subset_iff P (PrimeDivisorUnion.isClosed_support Q)).mpr h)

/-- A prime divisor lies in a finite union of prime divisors only if it is one of them. -/
private theorem mem_of_support_subset_iUnion {Y : Scheme.{u}} {s : Finset (Mori.PrimeDivisor Y)}
    {P : Mori.PrimeDivisor Y} (h : (P.support : Set Y) ⊆ ⋃ E ∈ s, (E.support : Set Y)) :
    P ∈ s := by
  obtain ⟨E, hE, hPE⟩ := PrimeDivisorUnion.exists_subset_of_isIrreducible
    (fun E _ => PrimeDivisorUnion.isClosed_support E)
    (PrimeDivisorUnion.isIrreducible_support P) h
  rwa [PrimeDivisorUnion.eq_of_support_subset hPE]

/-- The prime divisors contained in `⋃_{E ∈ s} E` are the members of `s`. -/
private theorem support_subset_iUnion_iff {Y : Scheme.{u}} {s : Finset (Mori.PrimeDivisor Y)}
    {P : Mori.PrimeDivisor Y} :
    (P.support : Set Y) ⊆ ⋃ E ∈ s, (E.support : Set Y) ↔ P ∈ s :=
  ⟨mem_of_support_subset_iUnion, fun h => Set.subset_biUnion_of_mem
    (u := fun E : Mori.PrimeDivisor Y => (E.support : Set Y)) h⟩

/-- The support of `∑_{E ∈ s} E` is `s`. -/
private theorem support_sum_single {Y : Scheme.{u}} (s : Finset (Mori.PrimeDivisor Y)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support = s := by
  classical
  ext P
  simp [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- The support of the reduced divisor of `s` is `s`. -/
private theorem support_reducedDivisorOf {Y : Scheme.{u}} (s : Finset (Mori.PrimeDivisor Y)) :
    (MMP.Intersection.reducedDivisorOf s).support = s := by
  classical
  ext P
  rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
    MMP.Intersection.coeff_reducedDivisorOf]
  split_ifs with h <;> simp [h]

/-- The coefficients of the reduced divisor of `s` are `0` or `1`. -/
private theorem coeff_reducedDivisorOf_eq_zero_or_eq_one {Y : Scheme.{u}}
    (s : Finset (Mori.PrimeDivisor Y)) (P : Mori.PrimeDivisor Y) :
    (MMP.Intersection.reducedDivisorOf s).coeff P = 0 ∨
      (MMP.Intersection.reducedDivisorOf s).coeff P = 1 := by
  classical
  rw [MMP.Intersection.coeff_reducedDivisorOf]
  split_ifs <;> simp

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (D : RDivisor X)

/-- The configuration of a Kollár–Mori log resolution is a finite union of prime divisors whose
reduced sum is snc. -/
private theorem exists_finset_cfg {Y : Scheme.{u}} {f : Y ⟶ X}
    (hlog : Mori.IsLogResolution sX D f) :
    ∃ s : Finset (Mori.PrimeDivisor Y), (⋃ E ∈ s, (E.support : Set Y)) = cfg D f ∧
      (MMP.Intersection.reducedDivisorOf s).IsSNC (f ≫ sX) := by
  classical
  rcases hlog.isSNCSubset with h | ⟨s, hs, hsnc⟩
  · refine ⟨∅, ?_, ?_⟩
    · change _ = ((Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous :
        Closeds Y) : Set Y)
      rw [h]
      simp
    · haveI := hlog.isSmoothScheme.smooth
      rw [DivisorWithCoeffs.isSNC_iff_of_support_eq (D' := (0 : Divisor Y))
        (by rw [support_reducedDivisorOf]; rfl)]
      exact DivisorWithCoeffs.isSNC_zero _
  · exact ⟨s, hs, (DivisorWithCoeffs.isSNC_iff_of_support_eq
      ((support_reducedDivisorOf s).trans (support_sum_single s).symm)).mpr hsnc⟩

/-! ### Transforms of prime divisors under `f⁻¹` -/

/-- **Valuative criterion at a divisor.** A proper birational morphism `f : Y ⟶ X` onto a normal
scheme is an isomorphism of local rings over the generic point of each prime divisor `Q` of `X`. -/
private theorem exists_primeDivisor_isIso_stalkMap {Y X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirationalMorphism f) (Q : Mori.PrimeDivisor X) :
    ∃ E : Mori.PrimeDivisor Y,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso {Y X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (E : Mori.PrimeDivisor Y) (Q : Mori.PrimeDivisor X)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Mori.PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- Outside `Ex(f)`, a prime divisor lies over a prime divisor with the same valuation. -/
private theorem exists_valuationOver_eq {Y X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (P : Mori.PrimeDivisor Y) (hP : P.genericPoint ∉ (Mori.exceptionalSet f : Set Y)) :
    ∃ Γ : Mori.PrimeDivisor X, f P.genericPoint = Γ.genericPoint ∧
      P.valuationOver f = Γ.divisorialValuation := by
  have hb : f P.genericPoint ∈ Mori.biregularLocus f := not_not.mp hP
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb, P.coheight_genericPoint]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm, ?_⟩
  have := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f hb
  exact valuationOver_eq_of_isIso f P _
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm

end Helpers

section Exceptional

/-- If `a ≫ b` is an isomorphism, `a` is dominant, the source of `b` is reduced and `b` is
separated, then `b` is an isomorphism. -/
private lemma isIso_of_isIso_comp {A B V : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ V) [IsIso (a ≫ b)]
    [IsDominant a] [IsReduced B] [IsSeparated b] : IsIso b := by
  refine ⟨⟨inv (a ≫ b) ≫ a, ?_, by simp⟩⟩
  refine ext_of_isDominant_of_isSeparated b ?_ a ?_
  · simp
  · rw [← Category.assoc, IsIso.hom_inv_id_assoc, Category.comp_id]

/-- If `h ≫ g` is an isomorphism over `V`, with `h` dominant, `X'` reduced and `g` separated,
then `g` is an isomorphism over `V` and `h` over `g⁻¹(V)`. -/
private lemma isBiregular_of_isBiregular_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] {V : X.Opens}
    (hV : IsBiregular (h ≫ g) V) : IsBiregular g V ∧ IsBiregular h (g ⁻¹ᵁ V) := by
  unfold IsBiregular at hV ⊢
  rw [morphismRestrict_comp] at hV
  have : IsDominant (h ∣_ g ⁻¹ᵁ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant h› _
  have : IsSeparated (g ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› _
  have := @isIso_of_isIso_comp _ _ _ (h ∣_ g ⁻¹ᵁ V) (g ∣_ V) hV _ _ _
  exact ⟨this, @IsIso.of_isIso_comp_right _ _ _ _ _ _ (g ∣_ V) this hV⟩

/-- Over the biregular locus of `q`, the morphism `q` is injective. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {X Z : Scheme.{u}} (q : Z ⟶ X) {z z' : Z}
    (hz : q z ∈ biregularLocus q) (h : q z = q z') : z = z' := by
  haveI : IsIso (q ∣_ biregularLocus q) := isBiregular_biregularLocus q
  let a : (q ⁻¹ᵁ biregularLocus q).toScheme := ⟨z, hz⟩
  let b : (q ⁻¹ᵁ biregularLocus q).toScheme :=
    ⟨z', show q z' ∈ biregularLocus q from h ▸ hz⟩
  exact congrArg Subtype.val (@(q ∣_ biregularLocus q).isOpenEmbedding.injective a b
    (Subtype.ext ((morphismRestrict_base_coe q _ a).trans
      (h.trans (morphismRestrict_base_coe q _ b).symm))))

/-- The exceptional set of a composite. -/
private lemma exceptionalSet_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] [UniversallyClosed g] :
    Mori.exceptionalSet (h ≫ g) =
      Mori.exceptionalSet h ⊔ (Mori.exceptionalSet g).preimage h.continuous := by
  apply SetLike.coe_injective
  ext y
  change y ∈ Mori.exceptionalSet (h ≫ g) ↔ y ∈ Mori.exceptionalSet h ∨
    h y ∈ Mori.exceptionalSet g
  simp only [Mori.mem_exceptionalSet]
  constructor
  · intro hy
    by_contra hne
    push Not at hne
    obtain ⟨hyh, hyg⟩ := hne
    apply hy
    have hcl : IsClosed (g '' (biregularLocus h : Set X')ᶜ) :=
      g.isClosedMap _ (biregularLocus h).isOpen.isClosed_compl
    let W : X.Opens := biregularLocus g ⊓ ⟨_, hcl.isOpen_compl⟩
    have hWg : IsBiregular g W :=
      isBiregular_iff_le_biregularLocus.mpr inf_le_left
    have hWh : IsBiregular h (g ⁻¹ᵁ W) := by
      refine isBiregular_iff_le_biregularLocus.mpr ?_
      intro x hx
      by_contra hxU
      exact hx.2 ⟨x, hxU, rfl⟩
    have hiso : IsBiregular (h ≫ g) W := @isIso_restrict_comp _ _ _ h g W hWg hWh
    refine le_biregularLocus hiso ⟨hyg, ?_⟩
    rintro ⟨x, hx, hxy⟩
    exact hx (eq_of_map_eq_of_mem_biregularLocus g hyg
      (hxy.trans (Scheme.Hom.comp_apply h g y)).symm ▸ hyh)
  · intro hy hmem
    have hb := isBiregular_of_isBiregular_comp h g (isBiregular_biregularLocus (h ≫ g))
    rcases hy with hy | hy
    · exact hy (le_biregularLocus hb.2 hmem)
    · exact hy (le_biregularLocus hb.1 hmem)

end Exceptional

section Combinatorics

/-- **The Dershowitz–Manna step.** Let `φ` send the elements of `B` satisfying `p` injectively,
with the same key, into `A ∖ {a₀}`, and let every other element of `B` have key less than that of
`a₀ ∈ A`. Then the multiset of keys of `B` is smaller than that of `A` in the Dershowitz–Manna
order. -/
private theorem isDershowitzMannaLT_map {α β : Type*} [DecidableEq α] (A : Finset α)
    (B : Finset β) (key : α → ℕ) (key' : β → ℕ) (p : β → Prop) [DecidablePred p] (φ : β → α)
    (hφ : ∀ b ∈ B, p b → φ b ∈ A)
    (hinj : ∀ b ∈ B, ∀ b' ∈ B, p b → p b' → φ b = φ b' → b = b')
    (hkey : ∀ b ∈ B, p b → key (φ b) = key' b) (a₀ : α) (ha₀ : a₀ ∈ A)
    (ha₀' : ∀ b ∈ B, p b → φ b ≠ a₀) (hlt : ∀ b ∈ B, ¬ p b → key' b < key a₀) :
    Multiset.IsDershowitzMannaLT (B.val.map key') (A.val.map key) := by
  set B₁ := B.filter p with hB₁
  set B₂ := B.filter (fun b => ¬ p b) with hB₂
  set A₁ := B₁.image φ with hA₁def
  have hA₁ : A₁ ⊆ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_filter] at hb
    exact hφ b hb.1 hb.2
  have ha₀Z : a₀ ∈ A.filter (· ∉ A₁) := by
    refine Finset.mem_filter.mpr ⟨ha₀, fun h => ?_⟩
    obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp h
    rw [Finset.mem_filter] at hb
    exact ha₀' b hb.1 hb.2 hb'
  refine ⟨A₁.val.map key, B₂.val.map key', (A.filter (· ∉ A₁)).val.map key, ?_, ?_, ?_, ?_⟩
  · intro h0
    have h1 : key a₀ ∈ (A.filter (· ∉ A₁)).val.map key :=
      Multiset.mem_map_of_mem _ (Finset.mem_val.mpr ha₀Z)
    rw [h0] at h1
    exact Multiset.notMem_zero _ h1
  · have h1 : B.val = B₁.val + B₂.val := by
      rw [hB₁, hB₂, Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]
    have hinj' : Set.InjOn φ (B₁ : Set β) := by
      intro b hb b' hb' h
      rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
      exact hinj b hb.1 b' hb'.1 hb.2 hb'.2 h
    have h2 : A₁.val.map key = B₁.val.map key' := by
      rw [hA₁def, Finset.image_val_of_injOn hinj', Multiset.map_map]
      refine Multiset.map_congr rfl fun b hb => ?_
      rw [Finset.mem_val, Finset.mem_filter] at hb
      exact hkey b hb.1 hb.2
    rw [h1, Multiset.map_add, h2]
  · have h1 : A.val = (A.filter (· ∈ A₁)).val + (A.filter (· ∉ A₁)).val := by
      rw [Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]
    have h2 : A.filter (· ∈ A₁) = A₁ := by
      ext a
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun h => hA₁ h
    rw [h1, Multiset.map_add, h2]
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hy
    rw [Finset.mem_val, Finset.mem_filter] at hb
    exact ⟨key a₀, Multiset.mem_map_of_mem _ (Finset.mem_val.mpr ha₀Z), hlt b hb.1 hb.2⟩

end Combinatorics

section Main

open MMP.Fourfold.SNCWeight

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  {n : ℕ} {K : Divisor X} {D : RDivisor X}

omit [CharZero k] in
/-- Log discrepancies over a sub-lc pair are nonnegative. -/
private theorem IsLD.nonneg (hklt : IsSubLc sX n K D) {Y : Scheme.{u}} {f : Y ⟶ X}
    {P : Mori.PrimeDivisor Y} {a : ℝ} (h : IsLD sX n K D f P a) : 0 ≤ a := by
  obtain ⟨hY, hf, hp, b, hb, rfl⟩ := h
  exact hklt.2.2.2 _ hb.2.2.1 _ ⟨b, hb, rfl⟩

/-- Log discrepancies are unique. -/
private theorem IsLD.eq {Y : Scheme.{u}} {f : Y ⟶ X} {P : Mori.PrimeDivisor Y} {a a' : ℝ}
    (h : IsLD sX n K D f P a) (h' : IsLD sX n K D f P a') : a = a' := by
  obtain ⟨hY, hf, hp, b, hb, rfl⟩ := h
  obtain ⟨hY', hf', hp', b', hb', rfl⟩ := h'
  rw [IsDiscrepancy.eq hb hb']

/-- The reduced sum of the configuration is an snc divisor in the sense of FA. -/
private theorem isSNCDivisor_reducedDivisorOf {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {s : Finset (Mori.PrimeDivisor Y)} (hsnc : (MMP.Intersection.reducedDivisorOf s).IsSNC sY) :
    IsSNCDivisor sY (MMP.Intersection.reducedDivisorOf s) := by
  refine ⟨coeff_reducedDivisorOf_eq_zero_or_eq_one s, fun P hP => hsnc.1 P hP, fun p _ => hsnc.2 p⟩

/-- **The log discrepancy of a divisor over a stratum.** Let `f : Y ⟶ X` be a log resolution with
configuration `∑ H_k`, and `ν` a divisor over `Y` whose center lies in `P ∩ Q` for two distinct
configuration divisors. Then `a_ℓ(P) + a_ℓ(Q) ≤ a_ℓ(ν)` over `(X, D)`: on `Y`, with the crepant
boundary `D_Y = ∑ (1 - a_ℓ(H_k)) H_k`, the snc log discrepancy formula gives
`a_ℓ(ν) = l + ∑ n_k a_ℓ(H_k)` with `n_P, n_Q ≥ 1`. -/
private theorem add_le_of_isLogDiscrepancy (hklt : IsSubLc sX n K D)
    {Y : Scheme.{u}} [IsIntegral Y] {f : Y ⟶ X} (hlog : Mori.IsLogResolution sX D f)
    [IsDominant f] {P Q : Mori.PrimeDivisor Y} (hP : (P.support : Set Y) ⊆ cfg D f)
    (hQ : (Q.support : Set Y) ⊆ cfg D f) (hPQ : P ≠ Q)
    (ν : ProperDivisorOver k (f ≫ sX)) (hνP : (ν.center : Set Y) ⊆ P.support)
    (hνQ : (ν.center : Set Y) ⊆ Q.support) {b aP aQ : ℝ}
    (hb : IsLogDiscrepancy sX n K D (ν.valuation.comap (functionFieldMap f)) b)
    (haP : IsLD sX n K D f P aP) (haQ : IsLD sX n K D f Q aQ) : aP + aQ ≤ b := by
  classical
  have hX : IsNormalVariety k sX := hklt.1
  have hn : topologicalKrullDim X = n := hklt.2.1.topologicalKrullDim_eq
  obtain ⟨hYnv, hYdim, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
  have hfb := hlog.isBirationalMorphism
  haveI : IsProper f := hlog.isProper
  haveI := hYnv.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hYnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hYnv.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : Mori.IsVariety k (f ≫ sX) := hYnv.1
  obtain ⟨s, hs, hsnc⟩ := exists_finset_cfg sX D hlog
  have hPs : P ∈ s := support_subset_iUnion_iff.mp (hs ▸ hP)
  have hQs : Q ∈ s := support_subset_iUnion_iff.mp (hs ▸ hQ)
  -- the form and the presentation
  obtain ⟨a, ha, rfl⟩ := hb
  have ha' := ha
  obtain ⟨hK, hKD, _, E₀, ω, m, r, L, _, hωK, hw⟩ := ha'
  obtain ⟨_, _, hω0, hLc, hsum, _⟩ := hw
  subst hωK
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant f (hLc j)
  set ωY := pullbackRationalPluriForms sX f ω with hωY
  set DY : RDivisor Y := ∑ j, r j • Divisor.toRDivisor (L' j) -
    Divisor.toRDivisor (divisorOfForm ωY) with hDY
  have hDYsum : Divisor.toRDivisor (divisorOfForm ωY) + DY =
      ∑ j, r j • Divisor.toRDivisor (L' j) := by
    rw [hDY]; abel
  have hpb : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D)
      (Divisor.toRDivisor (divisorOfForm ωY) + DY) :=
    ⟨m, r, L, L', hLc, hsum, fun j => ⟨_, hL' j⟩, hDYsum⟩
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hωY0 : ωY ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
      hfb.functionFieldMap_bijective hd hω0
  have hnY : topologicalKrullDim Y = n := hYdim.trans hn
  have hKY : (divisorOfForm ωY).IsCanonicalDivisor (f ≫ sX) n := by
    obtain ⟨K₀, hK₀⟩ :=
      MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hlog.isSmoothScheme hnY
    exact hK₀.of_linearlyEquivalent <| by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYnv hK₀ hωY0
  have hKDY : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωY) + DY) :=
    ⟨m, r, L', fun j => (hL' j).isCartier (hLc j), by
      rw [hDYsum]; simp only [toRDivisor_eq_mapCoeffs]⟩
  have hcrep := isDiscrepancy_comap_functionFieldMap_iff hX hω0 hK hKD f hYnv hfb hpb hKY
  -- discrepancies of the prime divisors of `Y`
  have hprime : ∀ R : Mori.PrimeDivisor Y,
      IsDiscrepancy sX n (divisorOfForm ω) D (R.valuationOver f) (-DY.coeff R) := by
    intro R
    let ER : ProperDivisorOver k (f ≫ sX) :=
      ⟨DivisorOver.ofPrimeDivisor k hYnv R, (inferInstance : IsProper (𝟙 Y))⟩
    have hER : ER.valuation = R.divisorialValuation := Valuation.ext fun g => by
      change R.divisorialValuation (functionFieldMap (𝟙 Y) g) = _
      rw [MMP.Mori.functionFieldMap_id_apply]
    have h1 := isDiscrepancy_divisorialValuation hYnv ωY hωY0 hKY hKDY R
    rw [← hER] at h1
    have h2 := (hcrep ER _).mpr h1
    rwa [hER] at h2
  have hIsLD : ∀ R : Mori.PrimeDivisor Y,
      IsLD sX n (divisorOfForm ω) D f R (1 - DY.coeff R) :=
    fun R => ⟨hYnv, hfb, inferInstance, -DY.coeff R, hprime R, by ring⟩
  have hpos : ∀ R ∈ s, 0 ≤ 1 - DY.coeff R := fun R _ => IsLD.nonneg hklt (hIsLD R)
  have hP1 : aP = 1 - DY.coeff P := IsLD.eq haP (hIsLD P)
  have hQ1 : aQ = 1 - DY.coeff Q := IsLD.eq haQ (hIsLD Q)
  -- the crepant boundary is supported on the configuration
  have hBS : ∀ R : Mori.PrimeDivisor Y, DY.coeff R ≠ 0 →
      R ∈ (MMP.Intersection.reducedDivisorOf s).support := by
    intro R hR
    rw [support_reducedDivisorOf]
    by_contra hRs
    apply hR
    have hRc : ¬ (R.support : Set Y) ⊆ cfg D f := fun h =>
      hRs (support_subset_iUnion_iff.mp (hs ▸ h))
    rw [support_subset_iff R (cfg D f).isClosed] at hRc
    simp only [cfg, Closeds.coe_sup, Set.mem_union, Closeds.coe_preimage, Set.mem_preimage,
      not_or] at hRc
    obtain ⟨hRex, hRD⟩ := hRc
    obtain ⟨Γ, hΓ, hval⟩ := exists_valuationOver_eq f R hRex
    have h1 := hprime R
    rw [hval] at h1
    have h2 := IsDiscrepancy.eq_neg_coeff h1
    have hΓ0 : D.coeff Γ = 0 := by
      by_contra h0
      exact hRD (hΓ ▸ DivisorWithCoeffs.mem_supp_iff.mpr
        ⟨Γ, h0, Positivity.PrimeDivisor.genericPoint_mem_support' Γ⟩)
    linarith
  obtain ⟨l, nn, hbeq, -, hn0, -, -⟩ :=
    exists_logDiscrepancy_eq_add_sum_of_isSNCDivisor (f ≫ sX) hYnv.1 hlog.isSmoothScheme
      (isSNCDivisor_reducedDivisorOf hsnc) hBS ν (b := 1 + a) ⟨a, (hcrep ν a).mp ha, rfl⟩
  rw [support_reducedDivisorOf] at hbeq hn0
  have hnP : (1 : ℝ) ≤ nn P := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun h => ((hn0 P hPs).mp h) hνP
  have hnQ : (1 : ℝ) ≤ nn Q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun h => ((hn0 Q hQs).mp h) hνQ
  have hsub : ({P, Q} : Finset (Mori.PrimeDivisor Y)) ⊆ s :=
    Finset.insert_subset hPs (Finset.singleton_subset_iff.mpr hQs)
  have hle : ∑ R ∈ ({P, Q} : Finset (Mori.PrimeDivisor Y)), (nn R : ℝ) * (1 - DY.coeff R) ≤
      ∑ R ∈ s, (nn R : ℝ) * (1 - DY.coeff R) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun R hR _ =>
      mul_nonneg (Nat.cast_nonneg _) (hpos R hR)
  rw [Finset.sum_pair hPQ] at hle
  have h1 := mul_le_mul_of_nonneg_right hnP (hpos P hPs)
  have h2 := mul_le_mul_of_nonneg_right hnQ (hpos Q hQs)
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  rw [hP1, hQ1, hbeq]
  linarith

/-- The components of an snc divisor form an snc family. -/
private theorem isSNCFamily_idealSheaf_of_isSNC {Y : Scheme.{u}}
    {g : Y ⟶ Spec (.of k)} {R : Type*} [Zero R] {T : MMP.Mori.DivisorWithCoeffs R Y}
    (hT : T.IsSNC g) : Resolution.IsSNCFamily g (fun E : T.support => E.1.idealSheaf) := by
  refine ⟨fun E => ⟨?_, PrimeDivisorUnion.isPureCodimOne_support E.1, hT.1 E.1 E.2⟩,
    fun x => ?_⟩
  · haveI := E.1.integral
    infer_instance
  · obtain ⟨m, z, j, hz, hj, hI⟩ := hT.2 x
    refine ⟨m, z, fun E => j ⟨E.1.1, E.1.2, E.2⟩, hz, fun E => hI ⟨E.1.1, E.1.2, E.2⟩,
      fun E E' h => ?_⟩
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj (hj h)))

open PrimeDivisorUnion StratumBlowup SNCBlowup MMP.Threefold.Resolution in
/-- The exceptional set of the blow-up of a smooth centre of codimension two is the preimage of
the centre. -/
private theorem coe_exceptionalSet_blowUpToBase {Y : Scheme.{u}} [IsIntegral Y]
    {sY : Y ⟶ Spec (.of k)} {I : Y.IdealSheafData} (h : Resolution.IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc2 : codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) = 2) :
    (Mori.exceptionalSet (blowUpToBase I) : Set (blowUp I)) = blowUpToBase I ⁻¹' I.support := by
  have hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    rw [hc2]
    norm_num
  ext x
  constructor
  · intro hx
    by_contra hxI
    exact Mori.mem_exceptionalSet.mp hx (mem_biregularLocus_of_notMem I hxI)
  · intro hxI
    refine Mori.mem_exceptionalSet.mpr fun hb => ?_
    set E := excE sY h hirr hc
    have hxE : x ∈ (E.support : Set (blowUp I)) := by rwa [coe_support_excE]
    have hsp : E.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
      exact specializes_iff_mem_closure.mpr hxE
    have hηb : blowUpToBase I E.genericPoint ∈ Mori.biregularLocus (blowUpToBase I) :=
      (hsp.map (blowUpToBase I).continuous).mem_open (Mori.biregularLocus _).isOpen hb
    have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus (blowUpToBase I) hηb
    rw [E.coheight_genericPoint] at h1
    have hcl := BlowupCrepancy.closure_map_genericPoint_excE sY h hirr hc
    have heq : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) =
        IrreducibleCloseds.closureSingleton (blowUpToBase I E.genericPoint) :=
      IrreducibleCloseds.ext hcl.symm
    rw [heq, MMP.Flips.codimension_closureSingleton, h1] at hc2
    exact absurd hc2 (by decide)

open PrimeDivisorUnion StratumBlowup in
/-- The support of the strict transform of `G` is the closure of the preimage of `G` off the
centre. -/
private theorem coe_support_strictPrime {Y : Scheme.{u}} [IsIntegral Y] (I : Y.IdealSheafData)
    {G : Mori.PrimeDivisor Y} (hG : G.genericPoint ∉ (I.support : Set Y)) :
    ((strictPrime I G hG).support : Set (blowUp I)) =
      closure (blowUpToBase I ⁻¹' ((G.support : Set Y) \ I.support)) := by
  apply le_antisymm
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine closure_mono (Set.singleton_subset_iff.mpr ?_)
    rw [Set.mem_preimage, map_genericPoint_strictPrime I hG]
    exact ⟨Positivity.PrimeDivisor.genericPoint_mem_support' G, hG⟩
  · refine closure_minimal ?_ (isClosed_support _)
    rintro x ⟨hxG, hxI⟩
    exact mem_support_strictPrime I hG hxI hxG

open PrimeDivisorUnion StratumBlowup SNCBlowup MMP.Threefold.Resolution in
/-- **One blow-up.** Blowing up a component `W` of `P ∩ Q`, for distinct configuration divisors
`P` and `Q` of a log resolution `f : Y ⟶ X`, gives a log resolution `π ≫ f` whose configuration
divisors are the exceptional divisor `E` and the strict transforms `st G` of the configuration
divisors of `f`. The strict transforms keep their log discrepancies, `E` has log discrepancy at
least `a_ℓ(P) + a_ℓ(Q)`, and every component of `st G₁ ∩ st G₂` is the strict transform of a
component `V ≠ W` of `G₁ ∩ G₂`. -/
private theorem exists_blowup (hklt : IsSubLc sX n K D) {Y : Scheme.{u}}
    [IsIntegral Y] {f : Y ⟶ X} (hlog : Mori.IsLogResolution sX D f) {P Q : Mori.PrimeDivisor Y}
    (hP : (P.support : Set Y) ⊆ cfg D f) (hQ : (Q.support : Set Y) ⊆ cfg D f) (hPQ : P ≠ Q)
    {W : Set Y} (hW : W ∈ Resolution.componentsOf (P.support ∩ Q.support : Set Y))
    {aP aQ : ℝ} (haP : IsLD sX n K D f P aP) (haQ : IsLD sX n K D f Q aQ) :
    ∃ (Y' : Scheme.{u}) (π : Y' ⟶ Y) (E : Mori.PrimeDivisor Y')
      (st : Mori.PrimeDivisor Y → Mori.PrimeDivisor Y'),
      Mori.IsLogResolution sX D (π ≫ f) ∧
      (∀ R : Mori.PrimeDivisor Y', (R.support : Set Y') ⊆ cfg D (π ≫ f) ↔
        R = E ∨ ∃ G : Mori.PrimeDivisor Y, (G.support : Set Y) ⊆ cfg D f ∧ st G = R) ∧
      (∀ G, st G ≠ E) ∧ Function.Injective st ∧
      (∀ G a, IsLD sX n K D (π ≫ f) (st G) a ↔ IsLD sX n K D f G a) ∧
      (∀ b, IsLD sX n K D (π ≫ f) E b → aP + aQ ≤ b) ∧ AlgebraicGeometry.IsProjective π ∧
      (∀ G₁ G₂ : Mori.PrimeDivisor Y, (G₁.support : Set Y) ⊆ cfg D f →
        (G₂.support : Set Y) ⊆ cfg D f → G₁ ≠ G₂ →
        ∀ C ∈ Resolution.componentsOf ((st G₁).support ∩ (st G₂).support : Set Y'),
          ∃ V ∈ Resolution.componentsOf (G₁.support ∩ G₂.support : Set Y), V ≠ W ∧
            C = closure (π ⁻¹' (V \ W))) := by
  classical
  have hX : IsNormalVariety k sX := hklt.1
  obtain ⟨hYnv, -, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
  have hfb := hlog.isBirationalMorphism
  haveI : IsProper f := hlog.isProper
  haveI := hYnv.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hYnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hYnv.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : Smooth (f ≫ sX) := hlog.isSmoothScheme.smooth
  haveI : IsDominant f := hfb.isDominant
  obtain ⟨s, hs, hsnc⟩ := exists_finset_cfg sX D hlog
  set T := MMP.Intersection.reducedDivisorOf s
  have hTs : T.support = s := support_reducedDivisorOf s
  have hcfgT : ∀ G : Mori.PrimeDivisor Y, (G.support : Set Y) ⊆ cfg D f ↔ G ∈ T.support := by
    intro G
    rw [hTs, ← hs]
    exact support_subset_iUnion_iff
  have hPT : P ∈ T.support := (hcfgT P).mp hP
  have hQT : Q ∈ T.support := (hcfgT Q).mp hQ
  have hWcl : IsClosed W := Resolution.Aux.isClosed_of_mem_componentsOf
    ((isClosed_support P).inter (isClosed_support Q)) hW
  -- the centre
  obtain ⟨I, hirr, hIsm, hWI, hIsub, hIst, -, hIv⟩ := exists_centre (f ≫ sX) hsnc hPT hQT hPQ
    hW.1.1.2.isPreconnected hW.1.1.1
    (hW.1.2.trans Set.inter_subset_left)
    (hW.1.2.trans Set.inter_subset_right)
  have hIW : (I.support : Set Y) = W := (hW.2 ⟨hirr, hIsub⟩ hWI).antisymm hWI
  -- the snc family of the configuration, and the classification of double intersections
  let H : T.support → Y.IdealSheafData := fun E => E.1.idealSheaf
  have hH : Resolution.IsSNCFamily (f ≫ sX) H := isSNCFamily_idealSheaf_of_isSNC hsnc
  let i₁ : T.support := ⟨P, hPT⟩
  let i₂ : T.support := ⟨Q, hQT⟩
  have hne : i₁ ≠ i₂ := fun h => hPQ (congrArg Subtype.val h)
  let W' : Resolution.componentsOf ((H i₁).support ∩ (H i₂).support : Set Y) := ⟨W, hW⟩
  have hZ : Resolution.componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W' = I := by
    rw [hIv]
    unfold Resolution.componentsFamily
    congr 1
    ext1
    rw [Closeds.coe_closure]
    exact hWcl.closure_eq.trans hIW.symm
  have hclass := (Resolution.blowUp_snc_pair_stratum (f ≫ sX) H hH hne W').2.2
  subst hZ
  set I := Resolution.componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W'
  have hc2 := codimension_centre_eq_two (f ≫ sX) hsnc hPT hQT hPQ hirr hIsm hIsub hIst
  have hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    rw [hc2]
    norm_num
  have hbl : Resolution.IsSmoothBlowup (f ≫ sX) I := ⟨hlog.isSmoothScheme, hIsm⟩
  set π := blowUpToBase I
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI : IsProper π := AlgebraicGeometry.isProper_blowUpToBase (I := I)
  have hπb : IsBirationalMorphism π := isBirationalMorphism_blowUpToBase I hirr hc
  haveI : Smooth (π ≫ f ≫ sX) :=
    (Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (f ≫ sX) I hbl).1
  have hπsm : IsSmoothScheme (π ≫ f ≫ sX) := Resolution.isSmoothScheme_of_smooth _
  set E := excE (f ≫ sX) hbl hirr hc
  have hGI : ∀ G : Mori.PrimeDivisor Y, G.genericPoint ∉ (I.support : Set Y) :=
    genericPoint_notMem_of_subset_inter I hPQ hIsub
  let st : Mori.PrimeDivisor Y → Mori.PrimeDivisor (blowUp I) := fun G => strictPrime I G (hGI G)
  have hstη : ∀ G, π (st G).genericPoint = G.genericPoint := fun G =>
    map_genericPoint_strictPrime I (hGI G)
  -- the log resolution `π` of `(Y, T)`
  set Δ : RDivisor Y := Divisor.toRDivisor T with hΔ
  have hΔsupp : (DivisorWithCoeffs.supp Δ : Set Y) = ⋃ E ∈ s, (E.support : Set Y) := by
    rw [DivisorWithCoeffs.coe_supp, ← hTs]
    congr 1
    ext P
    simp [hΔ, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]
  have hExπ := coe_exceptionalSet_blowUpToBase hbl hirr hc2
  have hnew := iUnion_newPrimes (f ≫ sX) hPQ hIsub hbl hirr hc hPT
  have hIcfg : (I.support : Set Y) ⊆ cfg D f := hIsub.trans (Set.inter_subset_left.trans hP)
  have hπlog : Mori.IsLogResolution (f ≫ sX) Δ π := by
    refine ⟨⟨inferInstance, hπb, hπsm⟩, ?_, Or.inr ⟨newPrimes (f ≫ sX) hPQ hIsub hbl hirr hc T,
      ?_, ?_⟩⟩
    · have : Mori.exceptionalSet π = E.idealSheaf.support :=
        Closeds.ext (hExπ.trans (coe_support_excE (f ≫ sX) hbl hirr hc).symm)
      rw [this]
      exact isPureCodimOne_support E
    · rw [hnew, Closeds.coe_sup, hExπ, Closeds.coe_preimage, hΔsupp, hTs, ← Set.preimage_union]
      congr 1
      refine (Set.union_eq_right.mpr ?_).symm
      exact hIcfg.trans hs.symm.le
    · have := isSNC_newBoundary (f ≫ sX) hPQ hIsub hbl hirr hc hlog.isSmoothScheme hsnc hPT hQT
        hIst
      exact (DivisorWithCoeffs.isSNC_iff_of_support_eq
        ((support_sum_single _).trans (support_reducedDivisorOf _).symm)).mpr this
  have hle : Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous ≤
      DivisorWithCoeffs.supp Δ := by
    intro y hy
    change y ∈ (DivisorWithCoeffs.supp Δ : Set Y)
    rwa [hΔsupp, hs]
  have hlog' : Mori.IsLogResolution sX D (π ≫ f) := hlog.comp hle hπlog
  obtain ⟨hY'nv, -, -⟩ := hlog'.toIsSmoothResolution.isNormalVariety hX
  -- the configuration of `π ≫ f`
  have hcfg' : ∀ x : blowUp I, x ∈ (cfg D (π ≫ f) : Set (blowUp I)) ↔
      π x ∈ (cfg D f : Set Y) := by
    intro x
    have hEx : x ∈ (Mori.exceptionalSet (π ≫ f) : Set (blowUp I)) ↔
        π x ∈ (I.support : Set Y) ∨ π x ∈ (Mori.exceptionalSet f : Set Y) := by
      rw [exceptionalSet_comp π f]
      change x ∈ (Mori.exceptionalSet π : Set (blowUp I)) ∨
        π x ∈ (Mori.exceptionalSet f : Set Y) ↔ _
      rw [hExπ]
      rfl
    have hI' : π x ∈ (I.support : Set Y) → π x ∈ (cfg D f : Set Y) := fun h => hIcfg h
    simp only [cfg, Closeds.coe_sup, Closeds.coe_preimage, Set.mem_union, Set.mem_preimage,
      Scheme.Hom.comp_apply] at hI' ⊢
    rw [hEx]
    tauto
  have hcfgnew : (cfg D (π ≫ f) : Set (blowUp I)) =
      ⋃ H ∈ newPrimes (f ≫ sX) hPQ hIsub hbl hirr hc T, (H.support : Set (blowUp I)) := by
    rw [hnew]
    ext x
    rw [hcfg' x, hTs, hs]
    rfl
  have hR : ∀ R : Mori.PrimeDivisor (blowUp I), (R.support : Set (blowUp I)) ⊆ cfg D (π ≫ f) ↔
      R = E ∨ ∃ G : Mori.PrimeDivisor Y, (G.support : Set Y) ⊆ cfg D f ∧ st G = R := by
    intro R
    rw [hcfgnew, support_subset_iUnion_iff, mem_newPrimes]
    simp only [hcfgT]
    rfl
  have hstE : ∀ G, st G ≠ E := by
    intro G h
    have h1 : π E.genericPoint ∈ (I.support : Set Y) := by
      have h0 : E.genericPoint ∈ (E.support : Set (blowUp I)) :=
        Positivity.PrimeDivisor.genericPoint_mem_support' E
      rwa [coe_support_excE] at h0
    rw [← h, hstη] at h1
    exact hGI G h1
  have hstinj : Function.Injective st := fun G₁ G₂ h =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hstη G₁).symm.trans ((congrArg (fun R => π R.genericPoint) h).trans (hstη G₂)))
  -- valuations
  haveI := hY'nv.2
  haveI : LocallyOfFiniteType ((π ≫ f) ≫ sX) := hY'nv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian ((π ≫ f) ≫ sX)
  have hval : ∀ G, (st G).valuationOver (π ≫ f) = G.valuationOver f := by
    intro G
    haveI := isIso_stalkMap_of_mem_biregularLocus π (show π (st G).genericPoint ∈ _ from
      (hstη G) ▸ mem_biregularLocus_of_notMem I (hGI G))
    have h1 := valuationOver_eq_of_isIso π (st G) G (hstη G)
    refine Valuation.ext fun g => ?_
    rw [Mori.PrimeDivisor.valuationOver_apply, Mori.PrimeDivisor.valuationOver_apply,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply π f g,
      ← Mori.PrimeDivisor.valuationOver_apply (st G) π, h1]
  have hLD : ∀ G a, IsLD sX n K D (π ≫ f) (st G) a ↔ IsLD sX n K D f G a := by
    intro G a
    constructor
    · rintro ⟨h1, h2, h3, h⟩
      refine ⟨hYnv, hfb, inferInstance, ?_⟩
      have hv : (ProperDivisorOver.mk ⟨blowUp I, π ≫ f, h1, h2, st G⟩ h3).valuation =
          (ProperDivisorOver.mk ⟨Y, f, hYnv, hfb, G⟩ inferInstance).valuation := hval G
      rwa [hv] at h
    · rintro ⟨h1, h2, h3, h⟩
      refine ⟨hY'nv, hlog'.isBirationalMorphism, hlog'.isProper, ?_⟩
      have hv : (ProperDivisorOver.mk ⟨blowUp I, π ≫ f, hY'nv, hlog'.isBirationalMorphism, st G⟩
          hlog'.isProper).valuation =
          (ProperDivisorOver.mk ⟨Y, f, h1, h2, G⟩ h3).valuation := hval G
      rwa [hv]
  have hEb : ∀ b, IsLD sX n K D (π ≫ f) E b → aP + aQ ≤ b := by
    rintro b ⟨h1, h2, h3, hb⟩
    have hνnv : IsNormalVariety k (π ≫ f ≫ sX) := by rwa [← Category.assoc]
    let ν : ProperDivisorOver k (f ≫ sX) := ⟨⟨blowUp I, π, hνnv, hπb, E⟩, inferInstance⟩
    have hcen : (ν.center : Set Y) ⊆ I.support := by
      rw [ProperDivisorOver.coe_center]
      change π '' (E.support : Set (blowUp I)) ⊆ _
      rw [coe_support_excE]
      exact Set.image_preimage_subset _ _
    have hνv : ν.valuation.comap (functionFieldMap f) =
        (ProperDivisorOver.mk ⟨blowUp I, π ≫ f, h1, h2, E⟩ h3).valuation := by
      refine Valuation.ext fun g => ?_
      change E.valuationOver π (functionFieldMap f g) = E.valuationOver (π ≫ f) g
      rw [Mori.PrimeDivisor.valuationOver_apply, Mori.PrimeDivisor.valuationOver_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    exact add_le_of_isLogDiscrepancy hklt hlog hP hQ hPQ ν
      (hcen.trans (hIsub.trans Set.inter_subset_left))
      (hcen.trans (hIsub.trans Set.inter_subset_right)) (hνv ▸ hb) haP haQ
  -- components of double intersections of strict transforms
  have hstsupp : ∀ G : Mori.PrimeDivisor Y, ((st G).support : Set (blowUp I)) =
      closure (π ⁻¹' ((G.support : Set Y) \ W)) := by
    intro G
    rw [← hIW]
    exact coe_support_strictPrime I (hGI G)
  have hD : ∀ (G : Mori.PrimeDivisor Y) (hGT : G ∈ T.support),
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (π ⁻¹'
        ((H ⟨G, hGT⟩).support \ (W' : Set Y))))).support : Set (blowUp I)) = (st G).support := by
    intro G hGT
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, hstsupp]
  have hpair : ∀ G₁ G₂ : Mori.PrimeDivisor Y, (G₁.support : Set Y) ⊆ cfg D f →
      (G₂.support : Set Y) ⊆ cfg D f → G₁ ≠ G₂ →
      ∀ C ∈ Resolution.componentsOf ((st G₁).support ∩ (st G₂).support : Set (blowUp I)),
        ∃ V ∈ Resolution.componentsOf (G₁.support ∩ G₂.support : Set Y), V ≠ W ∧
          C = closure (π ⁻¹' (V \ W)) := by
    intro G₁ G₂ hG₁ hG₂ hG C hC
    have hG₁T := (hcfgT G₁).mp hG₁
    have hG₂T := (hcfgT G₂).mp hG₂
    have hne' : (some ⟨G₁, hG₁T⟩ : Option T.support) ≠ some ⟨G₂, hG₂T⟩ := fun h =>
      hG (congrArg Subtype.val (Option.some.inj h))
    have h3 := hclass (some ⟨G₁, hG₁T⟩) (some ⟨G₂, hG₂T⟩) hne' C
      (by dsimp only; rwa [hD G₁ hG₁T, hD G₂ hG₂T])
    rcases h3 with ⟨i, j, hi, hj, V, hV, hVW, hCV⟩ | ⟨j, hj, -⟩
    · obtain rfl := Option.some.inj hi
      obtain rfl := Option.some.inj hj
      exact ⟨V, hV, hVW, hCV⟩
    · rcases hj with ⟨h, -⟩ | ⟨-, h⟩ <;> cases h
  exact ⟨blowUp I, π, E, st, hlog', hR, hstE, hstinj, hLD, hEb,
    Stacks.Blowup.isProjective_blowUpToBase I
      (AlgebraicGeometry.TwoStepTower.isFiniteType_of_isLocallyNoetherian I), hpair⟩

/-- There are finitely many bad triples. -/
private theorem finite_isBad {Y : Scheme.{u}} {f : Y ⟶ X} (hlog : Mori.IsLogResolution sX D f) :
    (setOf (IsBad sX n K D f)).Finite := by
  classical
  obtain ⟨s, hs, -⟩ := exists_finset_cfg sX D hlog
  haveI : IsProper f := hlog.isProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI : Smooth (f ≫ sX) := hlog.isSmoothScheme.smooth
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNoetherian Y := {}
  refine Set.Finite.subset (s.finite_toSet.biUnion fun P _ => s.finite_toSet.biUnion fun Q _ =>
    (Set.finite_singleton P).prod ((Set.finite_singleton Q).prod
      (Resolution.Aux.finite_and_cover_componentsOf ((PrimeDivisorUnion.isClosed_support P).inter
        (PrimeDivisorUnion.isClosed_support Q))).1)) ?_
  rintro ⟨P, Q, V⟩ ⟨hP, hQ, -, hV, -⟩
  simp only [Set.mem_iUnion]
  exact ⟨P, support_subset_iUnion_iff.mp (hs ▸ hP), Q, support_subset_iUnion_iff.mp (hs ▸ hQ),
    rfl, rfl, hV⟩

/-- One blow-up of a bad component lowers the measure. -/
private theorem exists_good_lt (hklt : IsSubLc sX n K D) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 2 ≤ c * N) {Y : Scheme.{u}} {f : Y ⟶ X} {w : Mori.PrimeDivisor Y → ℕ}
    (hG : Good sX n K D c f w) {t : Mori.PrimeDivisor Y × Mori.PrimeDivisor Y × Set Y}
    (ht : IsBad sX n K D f t) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X) (w' : Mori.PrimeDivisor Y' → ℕ),
      Good sX n K D c f' w' ∧
        Multiset.IsDershowitzMannaLT (measure sX n K D N f' w') (measure sX n K D N f w) := by
  classical
  obtain ⟨P, Q, W⟩ := t
  have ht' := ht
  obtain ⟨hP, hQ, hPQ, hW, aP, aQ, haP, haQ, haP0, haQ0, -⟩ := ht'
  haveI : IsIntegral Y :=
    (hG.log.toIsSmoothResolution.isNormalVariety hklt.1).1.1.toIsIntegral
  obtain ⟨Y', π, E, st, hlog', hR, hstE, hstinj, hLD, hEb, hπproj, hpair⟩ :=
    exists_blowup hklt hG.log hP hQ hPQ hW haP haQ
  obtain ⟨L, hL, hLa⟩ := hG.ample
  have hπH : IsProjectiveMorphism π := isProjectiveMorphism_of_isProjective π L hLa hπproj
  -- the new weights
  let w' : Mori.PrimeDivisor Y' → ℕ := fun R =>
    if h : ∃ G, st G = R then w h.choose else w P + w Q
  have hw'st : ∀ G, w' (st G) = w G := by
    intro G
    have h : ∃ G', st G' = st G := ⟨G, rfl⟩
    simp only [w', dif_pos h]
    rw [hstinj h.choose_spec]
  have hw'E : w' E = w P + w Q := by
    simp only [w']
    rw [dif_neg]
    rintro ⟨G, hG⟩
    exact hstE G hG
  have hwP := hG.weight P hP
  have hwQ := hG.weight Q hQ
  have hG' : Good sX n K D c (π ≫ f) w' := by
    refine ⟨hlog', hπH.comp hG.proj,
      exists_isAmple_of_isQuasiProjective π L hLa hπproj.isQuasiProjective, fun R hR' => ?_⟩
    rcases (hR R).mp hR' with rfl | ⟨G, hG₀, rfl⟩
    · refine ⟨by rw [hw'E]; omega, fun b hb _ => ?_⟩
      rw [hw'E]
      have h0 := hEb b hb
      have h1 := hwP.2 aP haP haP0
      have h2 := hwQ.2 aQ haQ haQ0
      push_cast
      linarith
    · rw [hw'st]
      exact ⟨(hG.weight G hG₀).1, fun a ha ha0 => (hG.weight G hG₀).2 a ((hLD G a).mp ha) ha0⟩
  -- badness bounds the weights
  have hbound : ∀ b ∈ (finite_isBad (n := n) (K := K) hlog').toFinset,
      w' b.1 + w' b.2.1 < N := by
    rintro ⟨R₁, R₂, C⟩ hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨hR₁, hR₂, -, -, a, a', ha, ha', ha0, ha0', hlt⟩ := hb
    have h1 := (hG'.weight R₁ hR₁).2 a ha ha0
    have h2 := (hG'.weight R₂ hR₂).2 a' ha' ha0'
    have : (c : ℝ) * ((w' R₁ + w' R₂ : ℕ) : ℝ) < c * N := by push_cast; linarith
    exact_mod_cast lt_of_mul_lt_mul_left this hc.le
  -- the map from bad triples avoiding `E` to old bad triples
  let down : Mori.PrimeDivisor Y' → Mori.PrimeDivisor Y := fun R =>
    if h : ∃ G, st G = R then h.choose else P
  have hdown : ∀ G, down (st G) = G := by
    intro G
    have h : ∃ G', st G' = st G := ⟨G, rfl⟩
    simp only [down, dif_pos h]
    exact hstinj h.choose_spec
  let Vc : Mori.PrimeDivisor Y' × Mori.PrimeDivisor Y' × Set Y' → Set Y := fun b =>
    if h : ∃ V : Set Y, ∃ G₁ G₂ : Mori.PrimeDivisor Y, st G₁ = b.1 ∧ st G₂ = b.2.1 ∧
        V ∈ Resolution.componentsOf (G₁.support ∩ G₂.support : Set Y) ∧ V ≠ W ∧
        b.2.2 = closure (π ⁻¹' (V \ W)) then h.choose else ∅
  let φ : Mori.PrimeDivisor Y' × Mori.PrimeDivisor Y' × Set Y' →
      Mori.PrimeDivisor Y × Mori.PrimeDivisor Y × Set Y := fun b => (down b.1, down b.2.1, Vc b)
  have hdesc : ∀ b ∈ (finite_isBad (n := n) (K := K) hlog').toFinset, (b.1 ≠ E ∧ b.2.1 ≠ E) →
      ∃ G₁ G₂ : Mori.PrimeDivisor Y, (G₁.support : Set Y) ⊆ cfg D f ∧
        (G₂.support : Set Y) ⊆ cfg D f ∧ G₁ ≠ G₂ ∧ b.1 = st G₁ ∧ b.2.1 = st G₂ ∧
        φ b = (G₁, G₂, Vc b) ∧
        Vc b ∈ Resolution.componentsOf (G₁.support ∩ G₂.support : Set Y) ∧ Vc b ≠ W ∧
        b.2.2 = closure (π ⁻¹' (Vc b \ W)) := by
    rintro ⟨R₁, R₂, C⟩ hb ⟨h₁, h₂⟩
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨hR₁, hR₂, hR₁₂, hC, -⟩ := hb
    obtain ⟨G₁, hG₁, rfl⟩ := ((hR R₁).mp hR₁).resolve_left h₁
    obtain ⟨G₂, hG₂, rfl⟩ := ((hR R₂).mp hR₂).resolve_left h₂
    have hG₁₂ : G₁ ≠ G₂ := fun h => hR₁₂ (h ▸ rfl)
    obtain ⟨V₀, hV₀, hV₀W, hCV₀⟩ := hpair G₁ G₂ hG₁ hG₂ hG₁₂ C hC
    have hex : ∃ V : Set Y, ∃ G₁' G₂' : Mori.PrimeDivisor Y, st G₁' = st G₁ ∧ st G₂' = st G₂ ∧
        V ∈ Resolution.componentsOf (G₁'.support ∩ G₂'.support : Set Y) ∧ V ≠ W ∧
        C = closure (π ⁻¹' (V \ W)) := ⟨V₀, G₁, G₂, rfl, rfl, hV₀, hV₀W, hCV₀⟩
    have hVc : Vc (st G₁, st G₂, C) = hex.choose := dif_pos hex
    obtain ⟨G₁', G₂', e₁, e₂, hV1, hV2, hV3⟩ := hex.choose_spec
    obtain rfl := hstinj e₁
    obtain rfl := hstinj e₂
    refine ⟨G₁', G₂', hG₁, hG₂, hG₁₂, rfl, rfl, ?_, hVc ▸ hV1, hVc ▸ hV2, hVc ▸ hV3⟩
    simp only [φ, hdown]
  refine ⟨Y', π ≫ f, w', hG', ?_⟩
  simp only [measure, dif_pos (finite_isBad (n := n) (K := K) hG.log),
    dif_pos (finite_isBad (n := n) (K := K) hlog')]
  refine isDershowitzMannaLT_map _ _ _ _ (fun b => b.1 ≠ E ∧ b.2.1 ≠ E) φ ?_ ?_ ?_ (P, Q, W)
    ((Set.Finite.mem_toFinset _).mpr ht) ?_ ?_
  · intro b hb hpb
    obtain ⟨G₁, G₂, hG₁, hG₂, hG₁₂, e₁, e₂, hφb, hV1, -, -⟩ := hdesc b hb hpb
    rw [hφb, Set.Finite.mem_toFinset]
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨-, -, -, -, a, a', ha, ha', hlt⟩ := hb
    rw [e₁] at ha
    rw [e₂] at ha'
    exact ⟨hG₁, hG₂, hG₁₂, hV1, a, a', (hLD G₁ a).mp ha, (hLD G₂ a').mp ha', hlt⟩
  · intro b hb b' hb' hpb hpb' h
    obtain ⟨G₁, G₂, -, -, -, e₁, e₂, hφb, -, -, hC⟩ := hdesc b hb hpb
    obtain ⟨G₁', G₂', -, -, -, e₁', e₂', hφb', -, -, hC'⟩ := hdesc b' hb' hpb'
    rw [hφb, hφb'] at h
    obtain ⟨rfl, rfl, hV⟩ := Prod.ext_iff.mp h |>.imp id Prod.ext_iff.mp
    obtain ⟨R₁, R₂, C⟩ := b
    obtain ⟨R₁', R₂', C'⟩ := b'
    simp only at e₁ e₂ e₁' e₂' hC hC' hV
    rw [e₁, e₂, e₁', e₂', hC, hC', hV]
  · intro b hb hpb
    obtain ⟨G₁, G₂, -, -, -, e₁, e₂, hφb, -, -, -⟩ := hdesc b hb hpb
    rw [hφb]
    simp only [e₁, e₂, hw'st]
  · intro b hb hpb h
    obtain ⟨G₁, G₂, -, -, -, -, -, hφb, -, hVW, -⟩ := hdesc b hb hpb
    rw [hφb] at h
    exact hVW (congrArg (fun x => x.2.2) h)
  · intro b hb hpb
    have hbd := hbound b hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨hR₁, hR₂, hR₁₂, -⟩ := hb
    simp only [not_and_or, not_not] at hpb
    have h1 := (hG'.weight _ hR₁).1
    have h2 := (hG'.weight _ hR₂).1
    show N - (w' b.1 + w' b.2.1) < N - (w P + w Q)
    rcases hpb with h | h
    · rw [h, hw'E] at hbd h1 ⊢
      omega
    · rw [h, hw'E] at hbd h2 ⊢
      omega

/-- Blowing up bad components terminates. -/
private theorem exists_good_not_isBad (hklt : IsSubLc sX n K D) {c : ℝ}
    (hc : 0 < c) {N : ℕ} (hN : 2 ≤ c * N) (m : Multiset ℕ) :
    ∀ {Y : Scheme.{u}} (f : Y ⟶ X) (w : Mori.PrimeDivisor Y → ℕ), Good sX n K D c f w →
      measure sX n K D N f w = m →
      ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X), Mori.IsLogResolution sX D f' ∧
        IsProjectiveMorphism f' ∧ ∀ t, ¬ IsBad sX n K D f' t := by
  induction m using (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).induction with
  | _ m ih =>
    intro Y f w hG hm
    by_cases h : ∃ t, IsBad sX n K D f t
    · obtain ⟨t, ht⟩ := h
      obtain ⟨Y', f', w', hG', hlt⟩ := exists_good_lt hklt hc hN hG ht
      exact ih _ (hm ▸ hlt) f' w' hG' rfl
    · exact ⟨Y, f, hG.log, hG.proj, fun t ht => h ⟨t, ht⟩⟩

/-- The initial log resolution, with all weights `1`. -/
private theorem exists_good_init {Y : Scheme.{u}} {f : Y ⟶ X} (hlog : Mori.IsLogResolution sX D f)
    (hproj : IsProjectiveMorphism f)
    (hample : ∃ (L : Y.Modules) (hL : Stacks.Ample.IsInvertibleModule Y L),
      letI : Stacks.Ample.IsInvertibleModule Y L := hL
      Stacks.Ample.IsAmple Y L) :
    ∃ (c : ℝ) (_ : 0 < c), Good sX n K D c f fun _ => 1 := by
  classical
  obtain ⟨s, hs, -⟩ := exists_finset_cfg sX D hlog
  let g : Mori.PrimeDivisor Y → ℝ := fun P =>
    if h : ∃ a, IsLD sX n K D f P a ∧ 0 < a then h.choose else 1
  have hgpos : ∀ P, 0 < g P := by
    intro P
    simp only [g]
    split_ifs with h
    · exact h.choose_spec.2
    · exact one_pos
  set A : Finset ℝ := insert 1 (s.image g)
  have hA : A.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨A.min' hA, ?_, hlog, hproj, hample, fun P hP => ⟨le_rfl, fun a ha ha0 => ?_⟩⟩
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_min_image A id hA
    rw [show A.min' hA = x from le_antisymm (Finset.min'_le _ _ hx)
      (Finset.le_min' _ _ _ fun y hy => hxe y hy)]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact one_pos
    · obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hx
      exact hgpos P
  · have hPs : P ∈ s := support_subset_iUnion_iff.mp (hs ▸ hP)
    have hgP : g P = a := by
      have h : ∃ a, IsLD sX n K D f P a ∧ 0 < a := ⟨a, ha, ha0⟩
      simp only [g, dif_pos h]
      exact IsLD.eq h.choose_spec.1 ha
    rw [Nat.cast_one, mul_one, ← hgP]
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hPs))

/-- **Log resolutions with the pair condition.** Starting from an `H`-projective log resolution
of a sub-lc pair `(X, D)` whose source carries an ample invertible sheaf, blowing up the
components of the double intersections of configuration divisors with positive log
discrepancies `a, b` and `a + b < 2` terminates in an `H`-projective log resolution on which any
two distinct meeting configuration divisors with positive log discrepancies `a, b` have
`a + b ≥ 2`. -/
private theorem exists_isLogResolution_pairCondition (hklt : IsSubLc sX n K D) {Y₀ : Scheme.{u}}
    {f₀ : Y₀ ⟶ X} (hlog : Mori.IsLogResolution sX D f₀) (hproj : IsProjectiveMorphism f₀)
    (hample : ∃ (L : Y₀.Modules) (hL : Stacks.Ample.IsInvertibleModule Y₀ L),
      letI : Stacks.Ample.IsInvertibleModule Y₀ L := hL
      Stacks.Ample.IsAmple Y₀ L) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Mori.IsLogResolution sX D f ∧ IsProjectiveMorphism f ∧
      ∀ P Q : Mori.PrimeDivisor Y, P ≠ Q → (P.support : Set Y) ⊆ cfg D f →
        (Q.support : Set Y) ⊆ cfg D f → ((P.support : Set Y) ∩ Q.support).Nonempty →
        ∀ a b : ℝ, IsLD sX n K D f P a → IsLD sX n K D f Q b → 0 < a → 0 < b → 2 ≤ a + b := by
  obtain ⟨c, hc, hG⟩ := exists_good_init (n := n) (K := K) hlog hproj hample
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 / c ≤ N := exists_nat_ge _
  have hN' : 2 ≤ c * N := by
    rw [div_le_iff₀ hc] at hN
    linarith
  obtain ⟨Y, f, hlog, hproj, hno⟩ := exists_good_not_isBad hklt hc hN' _ f₀ _ hG rfl
  refine ⟨Y, f, hlog, hproj, fun P Q hPQ hP hQ hPQne a b ha hb ha0 hb0 => ?_⟩
  obtain ⟨x, hx⟩ := hPQne
  obtain ⟨W, hW, -⟩ := MMP.Resolution.exists_mem_componentsOf hx
  by_contra hlt
  exact hno (P, Q, W) ⟨hP, hQ, hPQ, hW, a, b, ha, hb, ha0, hb0, not_le.mp hlt⟩

end Main

section Lifting

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] (E : ProperDivisorOver k sX) : HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  refine ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, ?_⟩, E, rfl⟩
  rfl

end Lifting

section Dictionary

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A presentation of `div(ω) + B`, coefficientwise, is a presentation as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_sum_of_coeff {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {C : Fin m → Divisor X}
    (h : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ) :
    Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (C j) := by
  ext Γ
  have := h Γ
  change (Divisor.toRDivisor (divisorOfForm ω) + B).coeff Γ =
    (∑ j, r j • Divisor.toRDivisor (C j)).coeff Γ
  rw [coeff_sum_smul_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
    coeff_divisorOfForm]
  exact this

/-- A datum computing the discrepancy `a_ω(E, B)`, with `div(ω)` a canonical divisor, computes
the log discrepancy `1 + a_ω(E, B)`. -/
private theorem isLogDiscrepancy_one_add_of_isDiscrepancyWith {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {a : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n B ω r L E a) :
    MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver (1 + a) := by
  obtain ⟨hX, -, hω0, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω0, ⟨divisorOfForm ω, hK, fun Γ => rfl⟩, m, r, L, L', hLc,
    fun Γ => ?_, hpb, by ring⟩
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    coeff_sum_smul_toRDivisor] using congrArg (fun D : RDivisor X => D.coeff Γ) hsum

/-- Every presentation of `div(ω) + B` by Cartier divisors computes a discrepancy on every
proper model. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {B : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ a, IsDiscrepancyWith sX n B ω r L E a := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨(E.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * ((L' j).coeff E.E : ℝ), hX, hn, hω0,
    hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- A discrepancy computed with a fixed canonical divisor `K` gives the log discrepancy of any
proper model of the valuation. -/
private theorem isLogDiscrepancy_of_isDiscrepancy [PerfectField k] {n : ℕ} {K : Divisor X}
    {B : RDivisor X} {E : ProperDivisorOver k sX} {a : ℝ}
    (h : IsDiscrepancy sX n K B E.valuation a) :
    MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E', ω, m, r, L, hv, rfl, hw⟩ := h
  obtain ⟨hX, hn, hω0, hLc, hsum, -⟩ := id hw
  obtain ⟨c, hc⟩ := exists_isDiscrepancyWith hX hn hω0 hLc hsum E
  obtain rfl := hc.eq hw hv.symm
  exact isLogDiscrepancy_one_add_of_isDiscrepancyWith hK hc

/-- A log discrepancy `a` of a proper model `E` gives the discrepancy `a - 1` of its valuation,
computed with any canonical divisor `K` for which `K + B` is `ℝ`-Cartier. -/
public theorem isDiscrepancy_of_isLogDiscrepancy [PerfectField k] (hX : IsNormalVariety k sX)
    {n n' : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : IsCartierCombination (Divisor.toRDivisor K + B)) {E : ProperDivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n' B E.toDivisorOver a) :
    IsDiscrepancy sX n K B E.valuation (a - 1) := by
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨-, -, ω', hω0', ⟨K', hK', hK'ω⟩, m', r', C, C', hCc, hsum', hpb, ha⟩ := h
  obtain rfl : n = n' := by
    have h' := hK'.topologicalKrullDim_eq
    rw [hn] at h'
    exact_mod_cast h'
  have hw' : IsDiscrepancyWith sX n B ω' r' C E (a - 1) :=
    ⟨hX, hn, hω0', hCc, toRDivisor_add_eq_sum_of_coeff hsum', C', hpb, by linarith⟩
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  obtain ⟨m, r, L, hLc, hsum⟩ := hKB
  have hsum₁ : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hsum
  obtain ⟨c, hc⟩ := exists_isDiscrepancyWith hX hn hω0 hLc hsum₁ E
  rw [← hc.eq hw' rfl]
  exact ⟨hK, ⟨m, r, L, hLc, hsum⟩, hasNonemptyCenter_valuation E, E, ω, m, r, L, rfl, rfl, hc⟩

end Dictionary

section HProjective

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

variable {k : Type u} [Field k]

/-- The normalization of `P` in a normal integral locally Noetherian scheme `Y`, along a
quasi-compact open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal
and finite over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {Y P : Scheme.{u}}
    {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiSeparated j] [IsNormal Y] [IsLocallyNoetherian Y] :
    IsOpenImmersion (Scheme.Hom.toNormalization j) ∧
      IsNormal (Scheme.Hom.normalization j) ∧ IsFinite (Scheme.Hom.fromNormalization j) := by
  refine ⟨?_, AlgebraicGeometry.isNormal_normalization j fun V hV => ?_,
    isFinite_fromNormalization_of_locallyOfFiniteType j
    (isNagataScheme_of_locallyOfFiniteType_over_field k sP)⟩
  · have : IsOpenImmersion ((Limits.pullback.snd j j).toNormalization ≫ j.normalizationPullback j ≫
        Limits.pullback.fst _ _) := inferInstance
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst j j] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
      (Limits.pullback.fst j j) _).mp this
  · have : IsNoetherian V :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := isCompact_iff_compactSpace.mp hV }
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- **Normal compactification.** A normal variety `X` is an open subscheme of a normal proper
variety: compactify by Nagata's theorem and normalize the compactification in `X`. -/
private theorem exists_isOpenImmersion_isProper {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) :
    ∃ (X' : Scheme.{u}) (sX' : X' ⟶ Spec (.of k)) (t : X ⟶ X'),
      AlgebraicGeometry.IsVariety k sX' ∧ IsNormal X' ∧ IsProper sX' ∧ IsOpenImmersion t ∧
        t ≫ sX' = sX := by
  obtain ⟨hXv, hXn⟩ := hX
  haveI := hXv
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsSeparated sX := hXv.toIsSeparated
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace sX
  set j := c.immersion
  set p := c.toBase
  have hjp : j ≫ p = sX := Over.w c.obj.hom
  haveI : QuasiCompact j := hc
  have : IsSeparated j := by
    have : IsSeparated (j ≫ p) := by rw [hjp]; infer_instance
    exact IsSeparated.of_comp j p
  have : QuasiSeparated j := IsSeparated.instQuasiSeparated j
  haveI : IsNormal (Over.mk sX).left := hXn
  haveI : IsIntegral (Over.mk sX).left := ‹IsIntegral X›
  haveI : IsLocallyNoetherian (Over.mk sX).left := ‹IsLocallyNoetherian X›
  obtain ⟨ht, hnorm, hfin⟩ :=
    isOpenImmersion_toNormalization_and_isNormal_and_isFinite (sP := p) j
  refine ⟨_, j.fromNormalization ≫ p, j.toNormalization,
    (isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hnorm,
    inferInstance, ht, ?_⟩
  simp only [Scheme.Hom.toNormalization_fromNormalization_assoc, hjp]

/-- **A quasi-projective model.** A normal variety `X` is the target of an `H`-projective
birational morphism `q : Z ⟶ X` from a variety carrying an ample invertible sheaf: by Chow's
lemma a normal compactification of `X` is dominated birationally by a projective variety, and
`Z` is the inverse image of `X`. -/
private theorem exists_isProjectiveMorphism_isBirational_isAmple {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ X), AlgebraicGeometry.IsVariety k (q ≫ sX) ∧
      IsProjectiveMorphism q ∧ IsBirational q ∧
      ∃ (L : Z.Modules) (hL : Stacks.Ample.IsInvertibleModule Z L),
        letI := hL; Stacks.Ample.IsAmple Z L := by
  obtain ⟨X', sX', t, hv, hn, hp, ht, hts⟩ := exists_isOpenImmersion_isProper sX hX
  haveI := hv
  haveI := hn
  haveI := hp
  haveI := ht
  haveI : IsIntegral X' := hv.toIsIntegral
  obtain ⟨Z', π, hZv, hZH, hsurj, hbir⟩ :=
    (MMP.Resolution.Bridges.exists_isProjectiveMorphism_isBirational_chowModification k).2 hv hp
  haveI : IsSeparated sX' := hv.toIsSeparated
  have hπH : IsProjectiveMorphism π := IsProjectiveMorphism.of_comp π sX' hZH
  set U := t.opensRange
  set V := π ⁻¹ᵁ U
  let q : V.toScheme ⟶ X := (π ∣_ U) ≫ t.isoOpensRange.inv
  have hqH : IsProjectiveMorphism q :=
    IsProjectiveMorphism.of_iso (Iso.refl _) t.isoOpensRange.symm (by simp [q]) (hπH.restrict U)
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqH
  haveI := hZv
  haveI : IsIntegral Z' := hZv.toIsIntegral
  haveI := hsurj
  haveI : Nonempty V.toScheme := by
    obtain ⟨z, hz⟩ := π.surjective (t (genericPoint X))
    exact ⟨⟨z, show π z ∈ U from hz ▸ ⟨_, rfl⟩⟩⟩
  haveI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  haveI : Nonempty U.toScheme := ⟨⟨t (genericPoint X), ⟨_, rfl⟩⟩⟩
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  have hqv : AlgebraicGeometry.IsVariety k (q ≫ sX) :=
    (isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hqb : IsBirational q :=
    (hbir.morphismRestrict U).comp (isBirational_of_isIso_stalkMap_genericPoint _)
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective (π ≫ sX') M hMa hZH.isQuasiProjective
  haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX')
  haveI : CompactSpace Z' := QuasiCompact.compactSpace_of_compactSpace (π ≫ sX')
  haveI : IsNoetherian Z' := {}
  haveI : CompactSpace V.toScheme := Stacks.AmpleRestrict.compactSpace_opens_toScheme V
  exact ⟨V.toScheme, q, hqv, hqH, hqb, _, inferInstance,
    Stacks.AmpleRestrict.isAmple_pullbackModule_ι V L hLa⟩

open MMP.Fourfold.SNCWeight

/-- A composite `g ≫ q` with `q` proper is an isomorphism over every point `x` over which `q` is
an isomorphism and whose fibre under `q` lies over the biregular locus of `g`. -/
private theorem mem_biregularLocus_comp {X Z Y : Scheme.{u}} (g : Y ⟶ Z) (q : Z ⟶ X) [IsProper q]
    {x : X} (hx : x ∈ biregularLocus q) (hz : ∀ z, q z = x → z ∈ biregularLocus g) :
    x ∈ biregularLocus (g ≫ q) := by
  set A := biregularLocus q
  set B := biregularLocus g
  have hC : IsClosed (q '' (B : Set Z)ᶜ) := q.isClosedMap _ B.isOpen.isClosed_compl
  let V : X.Opens := A ⊓ ⟨_, hC.isOpen_compl⟩
  haveI : IsIso (q ∣_ A) := isBiregular_biregularLocus q
  haveI : IsIso (g ∣_ B) := isBiregular_biregularLocus g
  haveI : IsIso (q ∣_ V) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le q inf_le_left
  haveI : IsIso (g ∣_ q ⁻¹ᵁ V) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le g
    (V := B) (by
      intro z hz'
      by_contra hzB
      exact hz'.2 ⟨z, hzB, rfl⟩)
  refine le_biregularLocus (V := V) (isIso_restrict_comp g q V) ⟨hx, ?_⟩
  rintro ⟨z, hzB, hzx⟩
  exact hzB (hz z hzx)

/-- A closed subset of an snc divisor which is covered by the prime divisors it contains is an
snc divisor. -/
private theorem isSNCSubset_of_le {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} {C T : Closeds Y}
    (hC : IsSNCSubset sY C) (hTC : T ≤ C)
    (hT : ∀ y ∈ T, ∃ E : Mori.PrimeDivisor Y, y ∈ E.support ∧ (E.support : Set Y) ⊆ T) :
    IsSNCSubset sY T := by
  classical
  rcases hC with hC | ⟨s, hs, hsnc⟩
  · left
    rwa [hC, le_bot_iff] at hTC
  · right
    refine ⟨s.filter fun E => (E.support : Set Y) ⊆ T, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · intro y hy
        simp only [Set.mem_iUnion, Finset.mem_filter] at hy
        obtain ⟨E, ⟨-, hET⟩, hyE⟩ := hy
        exact hET hyE
      · intro y hy
        obtain ⟨E, hyE, hET⟩ := hT y hy
        have hEs : E ∈ s := mem_of_support_subset_iUnion (hs ▸ hET.trans hTC)
        exact Set.mem_biUnion (x := E) (Finset.mem_filter.mpr ⟨hEs, hET⟩) hyE
    · refine hsnc.of_support_subset ?_
      rw [support_sum_single, support_sum_single]
      exact Finset.filter_subset _ _

/-- A point of a closed subset of pure codimension one lying in a finite union of prime divisors
lies on one of those prime divisors which is contained in the subset. -/
private theorem exists_primeDivisor_of_isPureCodimOne {Y : Scheme.{u}} {S : Closeds Y}
    (hS : IsPureCodimOne S) {s : Finset (Mori.PrimeDivisor Y)}
    (hSs : (S : Set Y) ⊆ ⋃ E ∈ s, (E.support : Set Y)) {y : Y} (hy : y ∈ S) :
    ∃ E : Mori.PrimeDivisor Y, y ∈ E.support ∧ (E.support : Set Y) ⊆ S := by
  obtain ⟨W, hW, hyW⟩ := MMP.Resolution.exists_mem_componentsOf hy
  let W' : IrreducibleCloseds Y := ⟨W, hW.1.1,
    MMP.Resolution.Aux.isClosed_of_mem_componentsOf S.isClosed hW⟩
  have hcod : codimension W' = 1 :=
    hS W' ⟨hW.1.2, fun V hV hWV => hW.2 ⟨V.isIrreducible, hV⟩ hWV⟩
  obtain ⟨E, -, hWE⟩ := PrimeDivisorUnion.exists_subset_of_isIrreducible
    (fun E _ => PrimeDivisorUnion.isClosed_support E) hW.1.1 (hW.1.2.trans hSs)
  let E' : IrreducibleCloseds Y := ⟨E.support, PrimeDivisorUnion.isIrreducible_support E,
    PrimeDivisorUnion.isClosed_support E⟩
  have hWE' : W' = E' := by
    by_contra hne
    have h1 := Order.coheight_add_one_le (show W' < E' from lt_of_le_of_ne hWE hne)
    rw [← codimension_eq_coheight, ← codimension_eq_coheight, hcod,
      PrimeDivisorUnion.codimension_eq_one_of_eq_support E' E rfl] at h1
    exact absurd h1 (by decide)
  have hEW : (E.support : Set Y) = W := congrArg SetLike.coe hWE'.symm
  exact ⟨E, hEW ▸ hyW, hEW ▸ hW.1.2⟩

/-- Over the biregular locus, a point of the inverse image of a prime divisor `Γ` lies on the
prime divisor lying over `Γ`. -/
private theorem exists_primeDivisor_mem_of_mem_biregularLocus {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] (f : Y ⟶ X)
    [IsProper f] (hf : IsBirationalMorphism f) {y : Y} (hy : f y ∈ biregularLocus f)
    (Γ : Mori.PrimeDivisor X) (hyΓ : f y ∈ Γ.support) :
    ∃ E : Mori.PrimeDivisor Y, y ∈ E.support ∧ f E.genericPoint = Γ.genericPoint := by
  obtain ⟨E, hE, -⟩ := exists_primeDivisor_isIso_stalkMap f hf Γ
  refine ⟨E, ?_, hE⟩
  set A := biregularLocus f
  haveI : IsIso (f ∣_ A) := isBiregular_biregularLocus f
  have hsp : Γ.genericPoint ⤳ f y := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyΓ
    exact specializes_iff_mem_closure.mpr hyΓ
  have hΓA : Γ.genericPoint ∈ A := hsp.mem_open A.isOpen hy
  let a : (f ⁻¹ᵁ A).toScheme := ⟨E.genericPoint, show f E.genericPoint ∈ A from hE ▸ hΓA⟩
  let b : (f ⁻¹ᵁ A).toScheme := ⟨y, hy⟩
  have hab : (f ∣_ A) a ⤳ (f ∣_ A) b := by
    refine Topology.IsInducing.subtypeVal.specializes_iff.mp ?_
    change ((f ∣_ A) a).1 ⤳ ((f ∣_ A) b).1
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
    change f E.genericPoint ⤳ f y
    rwa [hE]
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact specializes_iff_mem_closure.mp
    (((f ∣_ A).isOpenEmbedding.isInducing.specializes_iff.mp hab).map continuous_subtype_val)

/-- **`H`-projective log resolutions.** A normal `ℚ`-factorial variety over a field of
characteristic zero has, for every `ℝ`-divisor `D`, a log resolution `f : Y ⟶ X` which is
`H`-projective, with `Y` carrying an ample invertible sheaf. -/
private theorem exists_isLogResolution_isProjectiveMorphism_isAmple [CharZero k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) (hQ : MMP.Fourfold.IsQFactorial sX) (D : RDivisor X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Mori.IsLogResolution sX D f ∧ IsProjectiveMorphism f ∧
      ∃ (L : Y.Modules) (hL : Stacks.Ample.IsInvertibleModule Y L),
        letI := hL; Stacks.Ample.IsAmple Y L := by
  classical
  obtain ⟨Z, q, hZv, hqH, hqb, L, hL, hLa⟩ := exists_isProjectiveMorphism_isBirational_isAmple sX hX
  haveI := hZv
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqH
  haveI : LocallyOfFiniteType (q ≫ sX) := hZv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  -- `q` is an isomorphism over a neighbourhood of the generic point of `X`
  obtain ⟨hU, hUiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso q hqb).1
    inferInstance
  have hqη : q (genericPoint Z) = genericPoint X := MMP.Mori.map_genericPoint_eq q hqb
  have hηq : genericPoint X ∈ biregularLocus q := by
    refine le_biregularLocus (V := ⟨_, hU⟩) hUiso ?_
    have := MMP.Mori.map_genericPoint_mem_finiteFibreLocus q hqb
    rwa [hqη] at this
  -- the centre `q⁻¹(Supp D ∪ (X ∖ V_q))` of the principalization
  set W : Closeds X := DivisorWithCoeffs.supp D ⊔ (biregularLocus q).compl
  have hηW : genericPoint X ∉ (W : Set X) := by
    rintro (h | h)
    · exact MMP.Fourfold.genericPoint_notMem_supp D h
    · exact h hηq
  set I := Scheme.IdealSheafData.vanishingIdeal (W.preimage q.continuous) with hIdef
  have hIsupp : (I.support : Set Z) = q ⁻¹' W := by
    rw [hIdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hI : I ≠ ⊥ := by
    intro h
    have hξ : genericPoint Z ∈ (I.support : Set Z) := by
      rw [h, Scheme.IdealSheafData.support_bot]; trivial
    rw [hIsupp] at hξ
    exact hηW (hqη ▸ hξ)
  obtain ⟨Y, g, hYv, hgproj, hgbir, hgsm, hgiso, -, hsnc, -⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap (q ≫ sX) hZv I hI
  haveI := hYv
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : IsProper g := hgproj.isProper
  haveI : LocallyOfFiniteType (g ≫ q ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ q ≫ sX)
  set f := g ≫ q with hf
  have hgH : IsProjectiveMorphism g := isProjectiveMorphism_of_isProjective g L hLa hgproj
  have hfH : IsProjectiveMorphism f := hgH.comp hqH
  -- the biregular locus of `g` contains the smooth points outside the centre
  have hgV : smoothLocus (q ≫ sX) ⊓ I.support.compl ≤ biregularLocus g :=
    le_biregularLocus hgiso
  have hηZ : genericPoint Z ∈ biregularLocus g := by
    refine hgV ⟨?_, ?_⟩
    · have hsmne : ((smoothLocus (q ≫ sX) : Z.Opens) : Set Z).Nonempty := by
        rw [smoothLocus_eq_smoothLocus]
        exact (Scheme.Hom.dense_smoothLocus_of_perfectField (q ≫ sX)).nonempty
      exact ((genericPoint_spec Z).mem_open_set_iff (smoothLocus (q ≫ sX)).isOpen).2
        (by simpa using hsmne)
    · change genericPoint Z ∉ (I.support : Set Z)
      rw [hIsupp]
      exact fun h => hηW (hqη ▸ h)
  -- points of `Y` outside the configuration of `g` lie over the biregular locus of `f`
  have hbir : ∀ y : Y, y ∉ (Mori.exceptionalSet g : Set Y) → g y ∉ (I.support : Set Z) →
      f y ∈ biregularLocus f := by
    intro y hy hyI
    have hyW : q (g y) ∉ (W : Set X) := by rwa [hIsupp] at hyI
    have hqV : q (g y) ∈ biregularLocus q := by
      by_contra h
      exact hyW (Or.inr h)
    refine mem_biregularLocus_comp g q hqV fun z hz => ?_
    rw [← eq_of_map_eq_of_mem_biregularLocus q hqV hz.symm]
    exact not_not.mp hy
  have hfb : IsBirationalMorphism f := by
    have hmem : genericPoint X ∈ biregularLocus f := by
      rw [← hqη]
      refine mem_biregularLocus_comp g q (hqη ▸ hηq) fun z hz => ?_
      rw [← eq_of_map_eq_of_mem_biregularLocus q (hqη ▸ hηq) hz.symm]
      exact hηZ
    haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
    exact isBirationalMorphism_of_isIso_restrict f _ ⟨_, hmem⟩
  have hYv' : AlgebraicGeometry.IsVariety k (f ≫ sX) := by
    rwa [hf, Category.assoc]
  have hpure : IsPureCodimOne (Mori.exceptionalSet f) :=
    isPureCodimOne_exceptionalSet_of_isQFactorial sX (f ≫ sX) hQ hYv' f rfl hfH hfb
  set C : Closeds Y := Mori.exceptionalSet g ⊔ (I.comap g).support
  have hsnc' : IsSNCSubset (f ≫ sX) C := by rwa [hf, Category.assoc]
  have hTC : Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous ≤ C := by
    rintro y (hy | hy)
    · by_contra hyC
      have h1 : y ∉ (Mori.exceptionalSet g : Set Y) := fun h => hyC (Or.inl h)
      have h2 : g y ∉ (I.support : Set Z) := by
        intro h
        refine hyC (Or.inr ?_)
        change y ∈ ((I.comap g).support : Set Y)
        rwa [Scheme.IdealSheafData.support_comap]
      exact hy (hbir y h1 h2)
    · right
      change y ∈ ((I.comap g).support : Set Y)
      rw [Scheme.IdealSheafData.support_comap]
      change g y ∈ (I.support : Set Z)
      rw [hIsupp]
      exact Or.inl hy
  have hlogD : Mori.IsLogResolution sX D f := by
    refine ⟨⟨inferInstance, hfb, ?_⟩, hpure, ?_⟩
    · rwa [hf, Category.assoc]
    · refine isSNCSubset_of_le hsnc' hTC fun y hy => ?_
      obtain ⟨s, hs⟩ : ∃ s : Finset (Mori.PrimeDivisor Y),
          (⋃ E ∈ s, (E.support : Set Y)) = C := by
        rcases hsnc' with h | ⟨s, hs, -⟩
        · exact ⟨∅, by rw [h]; simp⟩
        · exact ⟨s, hs⟩
      by_cases hyE : y ∈ (Mori.exceptionalSet f : Set Y)
      · obtain ⟨E, hyE', hE⟩ := exists_primeDivisor_of_isPureCodimOne hpure
          (by rw [hs]; exact fun z hz => hTC (Or.inl hz)) hyE
        exact ⟨E, hyE', hE.trans fun z hz => Or.inl hz⟩
      · have hyD : f y ∈ DivisorWithCoeffs.supp D := hy.resolve_left hyE
        obtain ⟨Γ, hΓ0, hyΓ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyD
        obtain ⟨E, hyE', hEΓ⟩ :=
          exists_primeDivisor_mem_of_mem_biregularLocus f hfb (not_not.mp hyE) Γ hyΓ
        refine ⟨E, hyE', fun z hz => Or.inr ?_⟩
        change f z ∈ DivisorWithCoeffs.supp D
        have hcl : IsClosed (f ⁻¹' (DivisorWithCoeffs.supp D : Set X)) :=
          (DivisorWithCoeffs.supp D).isClosed.preimage f.continuous
        refine (support_subset_iff E hcl).mpr ?_ hz
        change f E.genericPoint ∈ DivisorWithCoeffs.supp D
        rw [hEΓ]
        exact DivisorWithCoeffs.mem_supp_iff.mpr
          ⟨Γ, hΓ0, Positivity.PrimeDivisor.genericPoint_mem_support' Γ⟩
  exact ⟨Y, f, hlogD, hfH, exists_isAmple_of_isQuasiProjective g L hLa hgproj.isQuasiProjective⟩

end HProjective

open TopologicalSpace MMP MMP.Mori MMP.Fourfold.SNCWeight

section Restriction

variable {Y : Scheme.{u}}

/-- The coefficients of the restriction of `∑_{E ∈ s} γ_E E` to a prime divisor `T ∉ s` are
`∑_{E ∈ s} (E · Q) γ_E`. -/
private theorem coeff_restrictPrimeDivisor_finset_sum [IsLocallyNoetherian Y] [CompactSpace Y]
    {R : Type*} [AddCommGroup R] (s : Finset (Mori.PrimeDivisor Y)) {T : Mori.PrimeDivisor Y}
    (hT : T ∉ s) (γ : Mori.PrimeDivisor Y → R)
    (Q : Mori.PrimeDivisor T.idealSheaf.subscheme) :
    (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ s, Finsupp.single E (γ E)) T).coeff Q =
      ∑ E ∈ s, E.intersectionLength T.idealSheaf.subschemeι Q • γ E := by
  classical
  haveI : IsNoetherian Y := ⟨⟩
  have h0 : DivisorWithCoeffs.coeff (∑ E ∈ s, Finsupp.single E (γ E)) T = 0 := by
    rw [DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun E hE => ?_
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hT (h ▸ hE)
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ h0,
    ← Finsupp.sum_finset_sum_index (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
  exact Finset.sum_congr rfl fun E _ => Finsupp.sum_single_index (smul_zero _)

/-- A sum `∑_{j ∈ s} ℓ_j β_j` of natural multiples with `∑_{j ∈ s} ℓ_j = 1` is one of the
`β_j`, with `ℓ_j ≠ 0`. -/
private theorem exists_sum_nsmul_eq_of_sum_eq_one {ι M : Type*} [AddCommMonoid M]
    (s : Finset ι) (ℓ : ι → ℕ) (β : ι → M) (h : ∑ j ∈ s, ℓ j = 1) :
    ∃ j ∈ s, ℓ j ≠ 0 ∧ ∑ i ∈ s, ℓ i • β i = β j := by
  classical
  obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.trans_ne one_ne_zero)
  have hsplit := Finset.add_sum_erase s ℓ hj
  rw [h] at hsplit
  have hrest : ∑ i ∈ s.erase j, ℓ i = 0 := by omega
  have hj1 : ℓ j = 1 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  refine ⟨j, hj, hne, ?_⟩
  rw [Finset.sum_eq_single_of_mem j hj fun i hi hij => by
    rw [hrest i (Finset.mem_erase.mpr ⟨hij, hi⟩), zero_smul], hj1, one_smul]

/-- **The restriction of a combination of snc components.** On a smooth variety over an
algebraically closed field of characteristic zero, let `T ∉ s` be prime divisors with
`T + ∑_{E ∈ s} E` snc. For `A = ∑_{E ∈ s} β_E E`, the restriction `A|_T` is snc, and every
nonzero coefficient of `A|_T` at a prime divisor `Q` of `T` is `β_E` for some `E ∈ s` containing
`Q`. -/
private theorem isSNC_and_coeff_restrictPrimeDivisor_finset_sum {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [Smooth sY] (T : Mori.PrimeDivisor Y) (s : Finset (Mori.PrimeDivisor Y)) (hT : T ∉ s)
    (hsnc : DivisorWithCoeffs.IsSNC sY
      (Finsupp.single T (1 : ℤ) + ∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (β : Mori.PrimeDivisor Y → ℚ) :
    DivisorWithCoeffs.IsSNC (T.idealSheaf.subschemeι ≫ sY)
        (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ s, Finsupp.single E (β E)) T) ∧
      ∀ Q, (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ s, Finsupp.single E (β E)) T).coeff Q
          = 0 ∨
        ∃ E ∈ s, (DivisorWithCoeffs.restrictPrimeDivisor
          (∑ E ∈ s, Finsupp.single E (β E)) T).coeff Q = β E ∧
          T.idealSheaf.subschemeι Q.genericPoint ∈ E.support := by
  classical
  obtain ⟨_, _, _, _⟩ := (isVariety_iff k sY).mp ‹_›
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨hsncT, hone⟩ :=
    DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single sY T s hT hsnc
  set A : QDivisor Y := ∑ E ∈ s, Finsupp.single E (β E)
  set D : Divisor Y := ∑ E ∈ s, Finsupp.single E (1 : ℤ)
  have hAc : ∀ Q, (A.restrictPrimeDivisor T).coeff Q =
      ∑ E ∈ s, E.intersectionLength T.idealSheaf.subschemeι Q • β E :=
    coeff_restrictPrimeDivisor_finset_sum s hT β
  have hDc : ∀ Q, (D.restrictPrimeDivisor T).coeff Q =
      ((∑ E ∈ s, E.intersectionLength T.idealSheaf.subschemeι Q : ℕ) : ℤ) := by
    intro Q
    rw [coeff_restrictPrimeDivisor_finset_sum s hT (fun _ => (1 : ℤ)) Q]
    push_cast
    simp
  have hsupp : (A.restrictPrimeDivisor T).support ⊆ (D.restrictPrimeDivisor T).support := by
    intro Q hQ
    rw [Finsupp.mem_support_iff] at hQ ⊢
    change (A.restrictPrimeDivisor T).coeff Q ≠ 0 at hQ
    change (D.restrictPrimeDivisor T).coeff Q ≠ 0
    rw [hAc] at hQ
    obtain ⟨E, hE, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
    have hl : E.intersectionLength T.idealSheaf.subschemeι Q ≠ 0 := by
      rintro h0
      exact hne (by rw [h0, zero_smul])
    rw [hDc]
    exact_mod_cast (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨E, hE, Nat.pos_of_ne_zero hl⟩).ne'
  refine ⟨hsncT.of_support_subset hsupp, fun Q => or_iff_not_imp_left.mpr fun hQ => ?_⟩
  have hQD := hone Q (hsupp (Finsupp.mem_support_iff.mpr hQ))
  rw [hDc] at hQD
  obtain ⟨E, hE, hlE, heq⟩ := exists_sum_nsmul_eq_of_sum_eq_one s _ β (by exact_mod_cast hQD)
  refine ⟨E, hE, (hAc Q).trans heq, ?_⟩
  by_contra hmem
  exact hlE (MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem _ E hmem)

/-- On a smooth scheme, two prime divisors of a component `T` of an snc divisor which lie on
another component `P` and meet are equal: `P ∩ T` is smooth, so its irreducible components are
disjoint, and a prime divisor of `T` inside `P ∩ T` is a component of `P ∩ T`. -/
private theorem eq_of_mem_support_of_isSNC {k : Type u} [Field k] [PerfectField k]
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] [CompactSpace Y] {D : Divisor Y}
    (hD : DivisorWithCoeffs.IsSNC sY D) {P T : Mori.PrimeDivisor Y} (hP : P ∈ D.support)
    (hT : T ∈ D.support) (hPT : P ≠ T) {Q₁ Q₂ : Mori.PrimeDivisor T.idealSheaf.subscheme}
    (h₁ : T.idealSheaf.subschemeι Q₁.genericPoint ∈ P.support)
    (h₂ : T.idealSheaf.subschemeι Q₂.genericPoint ∈ P.support)
    (hmeet : ((Q₁.support : Set T.idealSheaf.subscheme) ∩ Q₂.support).Nonempty) : Q₁ = Q₂ := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsNoetherian Y := {}
  haveI := T.integral
  set ι := T.idealSheaf.subschemeι with hι
  set I := P.idealSheaf ⊔ T.idealSheaf with hIdef
  have hIsupp : (I.support : Set Y) = (P.support : Set Y) ∩ T.support := by
    rw [hIdef, Scheme.IdealSheafData.support_sup]; rfl
  have hsm : IsSmoothScheme (I.subschemeι ≫ sY) :=
    PrimeDivisorUnion.isSmoothScheme_subscheme_of_isRegularLocalRing_quotient sY I
      (fun y hy => PrimeDivisorUnion.isRegularLocalRing_quotient_inter hD hP hT hPT hy)
  have hιT : ∀ t, ι t ∈ (T.support : Set Y) := fun t => by
    have : ι t ∈ Set.range ι := ⟨t, rfl⟩
    rwa [hι, Scheme.IdealSheafData.range_subschemeι] at this
  have hind : Topology.IsInducing ι := ι.isClosedEmbedding.isInducing
  have hcl : IsClosed (I.support : Set Y) := I.support.isClosed
  obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hcl
  obtain ⟨x, hx₁, hx₂⟩ := hmeet
  -- the component of `P ∩ T` through `ι η_Q` contains `ι x`
  have hcomp : ∀ Q : Mori.PrimeDivisor T.idealSheaf.subscheme, ι Q.genericPoint ∈ P.support →
      x ∈ Q.support → ∃ W ∈ MMP.Resolution.componentsOf (I.support : Set Y),
        ι Q.genericPoint ∈ W ∧ ι x ∈ W := by
    intro Q hQ hxQ
    have hmem : ι Q.genericPoint ∈ (I.support : Set Y) := by
      rw [hIsupp]; exact ⟨hQ, hιT _⟩
    obtain ⟨W, hW, hQW⟩ := hcov hmem
    have hWcl : IsClosed W := MMP.Resolution.Aux.isClosed_of_mem_componentsOf hcl hW
    have hsp : Q.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxQ
      exact specializes_iff_mem_closure.mpr hxQ
    exact ⟨W, hW, hQW, (hsp.map ι.continuous).mem_closed hWcl hQW⟩
  obtain ⟨W₁, hW₁, hQW₁, hxW₁⟩ := hcomp Q₁ h₁ hx₁
  obtain ⟨W₂, hW₂, hQW₂, hxW₂⟩ := hcomp Q₂ h₂ hx₂
  obtain rfl : W₁ = W₂ := MMP.Resolution.Aux.eq_of_mem_componentsOf_of_isSmoothScheme sY I hsm hW₁
    hW₂ hxW₁ hxW₂
  -- the generic point of the component, as a point of `T`
  have hWcl : IsClosed W₁ := MMP.Resolution.Aux.isClosed_of_mem_componentsOf hcl hW₁
  set w := hW₁.1.1.genericPoint
  have hwgen : IsGenericPoint w W₁ := by
    have := hW₁.1.1.isGenericPoint_genericPoint_closure
    rwa [hWcl.closure_eq] at this
  have hwT : w ∈ Set.range ι := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι]
    have := hW₁.1.2 hwgen.mem
    rw [hIsupp] at this
    exact this.2
  obtain ⟨t, ht⟩ := hwT
  have key : ∀ Q : Mori.PrimeDivisor T.idealSheaf.subscheme, ι Q.genericPoint ∈ W₁ →
      Q.genericPoint = t := by
    intro Q hQW
    have hsp : ι t ⤳ ι Q.genericPoint := by
      rw [ht]; exact hwgen.specializes hQW
    have hsp' : t ⤳ Q.genericPoint := hind.specializes_iff.mp hsp
    by_contra hne
    have hlt : Q.genericPoint < t :=
      lt_iff_le_not_ge.mpr ⟨hsp', fun h => hne (Specializes.antisymm h hsp').eq⟩
    have hstep := Order.coheight_add_one_le hlt
    rw [Q.coheight_genericPoint] at hstep
    have h0 : Order.coheight t = 0 := by
      by_contra h0
      have h1 : (1 : ℕ∞) ≤ Order.coheight t := ENat.one_le_iff_ne_zero.mpr h0
      have h2 : (1 : ℕ∞) + 1 ≤ Order.coheight t + 1 := add_le_add_left h1 1
      have : (2 : ℕ∞) ≤ 1 := by rw [← one_add_one_eq_two]; exact h2.trans hstep
      exact absurd this (by decide)
    have hmax : IsMax t := Order.coheight_eq_zero.mp h0
    have htη : t = genericPoint T.idealSheaf.subscheme :=
      (Specializes.antisymm (hmax (genericPoint_specializes t))
        (genericPoint_specializes t)).eq
    have hwη : w = T.genericPoint := by rw [← ht, htη]; rfl
    have hTP : T.genericPoint ∈ (P.support : Set Y) := by
      have := hW₁.1.2 (hwη ▸ hwgen.mem)
      rw [hIsupp] at this
      exact this.1
    exact hPT (eq_of_genericPoint_mem_support hTP).symm
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((key Q₁ hQW₁).trans (key Q₂ hQW₂).symm)

end Restriction

/-- A positive lower bound for the snc discrepancy formula when no two of the components meet:
if `c i < 1` for every `i ∈ S` and the pair condition `P i j ∧ Q i j` never holds, then the
minimum of `1`, of the `1 - c i` and of the `1 - c i - c j` over pairs is positive. -/
private theorem zero_lt_inf_snc_bound {ι : Type*} (S : Finset ι) (c : ι → ℚ)
    (hc : ∀ i ∈ S, c i < 1) (P Q : ι → ι → Prop)
    (hPQ : ∀ i ∈ S, ∀ j ∈ S, P i j → Q i j → False) :
    (0 : EReal) < (⨅ (i ∈ S) (j ∈ S) (_ : P i j) (_ : Q i j),
        (((1 - c i - c j : ℚ) : ℝ) : EReal)) ⊓ (⨅ i ∈ S, (((1 - c i : ℚ) : ℝ) : EReal)) ⊓ 1 := by
  obtain ⟨δ, hδ, hδ1, hδc⟩ : ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i ∈ S, δ ≤ 1 - c i := by
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨1, one_pos, le_rfl, by simp⟩
    · obtain ⟨i₀, hi₀, hmin⟩ := S.exists_min_image (fun i => 1 - c i) hS
      exact ⟨min (1 - c i₀) 1, lt_min (sub_pos.mpr (hc i₀ hi₀)) one_pos, min_le_right _ _,
        fun i hi => (min_le_left _ _).trans (hmin i hi)⟩
  refine lt_of_lt_of_le (b := (((δ : ℚ) : ℝ) : EReal))
    (EReal.coe_lt_coe_iff.mpr (by exact_mod_cast hδ)) (le_inf (le_inf ?_ ?_) ?_)
  · exact le_iInf₂ fun i hi => le_iInf₂ fun j hj => le_iInf₂ fun h1 h2 =>
      (hPQ i hi j hj h1 h2).elim
  · exact le_iInf₂ fun i hi => EReal.coe_le_coe_iff.mpr (by exact_mod_cast hδc i hi)
  · have : (((δ : ℚ) : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (by exact_mod_cast hδ1)
    simpa using this

/-- On a scheme of dimension `≤ 1` no divisor over `X` is exceptional. -/
private theorem not_isExceptional_of_topologicalKrullDim_le_one {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : n ≤ 1)
    (D : DivisorOver k sX) : ¬ D.IsExceptional := by
  intro h
  have hdef : RationalMap.DefinedAt (X := D.Y) D.f.toRationalMap D.E.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp h) hdef
  have hmem : D.f D.E.genericPoint ∈
      (RationalMap.transform (X := D.Y) D.f.toRationalMap D.E.idealSheaf.support : Set X) := by
    refine RationalMap.image_subset_transform D.f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨_, ?_, rfl⟩
    change D.E.genericPoint ∈ D.E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hc := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2) _ hmem
  have hle : (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞) ≤ n := by
    rw [← hdim, ← MMP.Flips.codimension_closureSingleton]
    exact Order.coheight_le_krullDim _
  have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (1 : ℕ) := (WithBot.coe_le_coe.mpr hc).trans
    (hle.trans (by exact_mod_cast hn))
  exact absurd this (by decide)

open Classical in
/-- Sums over the prime divisors of a finite set, written through `Fin`. -/
private theorem sum_equivFin_mul_single {X : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) (Γ : MMP.Mori.PrimeDivisor X) :
    ∑ i : Fin S.card, c (S.equivFin.symm i) *
        (((Finsupp.single (S.equivFin.symm i : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ) =
      if Γ ∈ S then c Γ else 0 := by
  rw [Equiv.sum_comp S.equivFin.symm (fun x : S => c x *
    (((Finsupp.single (x : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ))]
  rw [Finset.sum_coe_sort S (fun x => c x * (((Finsupp.single x (1 : ℤ)) Γ : ℤ) : ℝ))]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single Γ]
    · simp
    · exact fun b _ hb => by simp [hb]
    · exact fun h' => absurd h h'
  · refine Finset.sum_eq_zero fun b hb => ?_
    have : b ≠ Γ := fun h' => h (h' ▸ hb)
    simp [this]

/-- On a smooth scheme `K + B` is `ℝ`-Cartier for every divisor `K` and every `ℝ`-divisor `B`
supported on a finite set `S` of prime divisors. -/
private theorem isRCartier_add_of_isSmoothScheme {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hsm : IsSmoothScheme sX) (K : Divisor X) {B : RDivisor X}
    (S : Finset (MMP.Mori.PrimeDivisor X))
    (hS : B.support ⊆ S) :
    RDivisor.IsRCartier (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + B) := by
  classical
  let e : Fin S.card → MMP.Mori.PrimeDivisor X := fun i => S.equivFin.symm i
  let C : Fin (S.card + 1) → Divisor X :=
    Fin.cons K (fun i => (Finsupp.single (e i) (1 : ℤ) : Divisor X))
  refine ⟨S.card + 1, Fin.cons 1 (fun i => B.coeff (e i)), C,
    fun i => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _, fun Γ => ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [C, e, Fin.cons_zero, Fin.cons_succ, one_mul, DivisorWithCoeffs.coeff_apply]
  rw [sum_equivFin_mul_single S (fun P => B P) Γ]
  change ((K Γ : ℤ) : ℝ) + B Γ = _
  split_ifs with h
  · rfl
  · have : B Γ = 0 := by
      by_contra h0
      exact h (hS (Finsupp.mem_support_iff.mpr h0))
    rw [this]

/-- **The restricted boundary is terminal.** On a smooth variety over an algebraically closed
field of characteristic zero, let `T ∉ s` be prime divisors with `T + ∑_{E ∈ s} E` snc, the `E ∈ s`
pairwise disjoint, and `0 < β_E < 1`. Then `T` is smooth and `Ψ = (∑_{E ∈ s} β_E E)|_T` is an
effective snc divisor with `(T, Ψ)` real terminal: no two components of `Ψ` meet (two components
inside the same `E` are disjoint since `E ∩ T` is smooth), so the snc discrepancy formula gives
`discrep(T, Ψ) > 0`. -/
private theorem isRealTerminalPair_restrictPrimeDivisor {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [Smooth sY] (T : Mori.PrimeDivisor Y) (s : Finset (Mori.PrimeDivisor Y)) (hTs : T ∉ s)
    (hsnc : DivisorWithCoeffs.IsSNC sY
      (Finsupp.single T (1 : ℤ) + ∑ E ∈ s, Finsupp.single E (1 : ℤ)))
    (β : Mori.PrimeDivisor Y → ℚ) (hβ : ∀ E ∈ s, 0 < β E ∧ β E < 1)
    (hdisj : ∀ E ∈ s, ∀ F ∈ s, E ≠ F → ¬ ((E.support : Set Y) ∩ F.support).Nonempty) :
    IsSmoothScheme (T.idealSheaf.subschemeι ≫ sY) ∧
      0 ≤ DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ s, Finsupp.single E (β E)) T ∧
      DivisorWithCoeffs.IsSNC (T.idealSheaf.subschemeι ≫ sY)
        (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ s, Finsupp.single E (β E)) T) ∧
      haveI := T.integral
      ∃ (_ : IsLocallyNoetherian T.idealSheaf.subscheme) (_ : IsNormal T.idealSheaf.subscheme),
        MMP.Fourfold.IsRealTerminalPair (T.idealSheaf.subschemeι ≫ sY)
          (QDivisor.toRDivisor
            (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ s, Finsupp.single E (β E)) T)) := by
  classical
  obtain ⟨_, _, _, _⟩ := (isVariety_iff k sY).mp ‹_›
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := T.integral
  set ι := T.idealSheaf.subschemeι with hι
  set A : QDivisor Y := ∑ E ∈ s, Finsupp.single E (β E)
  set Ψ := A.restrictPrimeDivisor T
  set G : Divisor Y := Finsupp.single T (1 : ℤ) + ∑ E ∈ s, Finsupp.single E (1 : ℤ) with hG
  have hGapp : ∀ E, G E = (if E = T then 1 else 0) + (if E ∈ s then 1 else 0) := by
    intro E
    simp [hG, Finsupp.finset_sum_apply, Finsupp.single_apply, eq_comm]
  have hTG : T ∈ G.support := by
    rw [Finsupp.mem_support_iff, hGapp, if_pos rfl, if_neg hTs]; norm_num
  have hEG : ∀ E ∈ s, E ∈ G.support := by
    intro E hE
    have hET : E ≠ T := fun h => hTs (h ▸ hE)
    rw [Finsupp.mem_support_iff, hGapp, if_neg hET, if_pos hE]; norm_num
  have hTsm : IsSmoothScheme (ι ≫ sY) := hsnc.1 T hTG
  obtain ⟨hΨsnc, hΨc⟩ := isSNC_and_coeff_restrictPrimeDivisor_finset_sum sY T s hTs hsnc β
  have hcoeff : ∀ Q, Ψ.coeff Q ≠ 0 → 0 < Ψ.coeff Q ∧ Ψ.coeff Q < 1 := by
    intro Q hQ
    rcases hΨc Q with h | ⟨E, hE, h, -⟩
    · exact absurd h hQ
    · rw [h]; exact hβ E hE
  have hΨ0 : 0 ≤ Ψ := by
    intro Q
    by_cases hQ : Ψ.coeff Q = 0
    · exact le_of_eq hQ.symm
    · exact (hcoeff Q hQ).1.le
  -- the variety `T`
  haveI : Smooth (ι ≫ sY) := hTsm.smooth
  haveI : IsLocallyNoetherian T.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sY)
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal T.idealSheaf.subscheme := AlgebraicGeometry.isNormal_of_smooth (ι ≫ sY)
  haveI : CompactSpace T.idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (ι ≫ sY)
  have hTv : AlgebraicGeometry.IsVariety k (ι ≫ sY) :=
    (isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  haveI := hTv
  have hTnv : IsNormalVariety k (ι ≫ sY) := ⟨hTv, inferInstance⟩
  obtain ⟨nT, hnT⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety k (ι ≫ sY)
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (ι ≫ sY) hTsm hnT
  -- no two components of `Ψ` meet
  have hnomeet : ∀ Q₁ ∈ Ψ.support, ∀ Q₂ ∈ Ψ.support, Q₁ ≠ Q₂ →
      ¬ ((Q₁.support : Set T.idealSheaf.subscheme) ∩ Q₂.support).Nonempty := by
    intro Q₁ hQ₁ Q₂ hQ₂ hne hmeet
    obtain ⟨E₁, hE₁, -, hι₁⟩ := (hΨc Q₁).resolve_left (Finsupp.mem_support_iff.mp hQ₁)
    obtain ⟨E₂, hE₂, -, hι₂⟩ := (hΨc Q₂).resolve_left (Finsupp.mem_support_iff.mp hQ₂)
    obtain ⟨x, hx₁, hx₂⟩ := hmeet
    have hmap : ∀ (Q : Mori.PrimeDivisor T.idealSheaf.subscheme) (E : Mori.PrimeDivisor Y),
        ι Q.genericPoint ∈ E.support → x ∈ Q.support → ι x ∈ E.support := by
      intro Q E hQE hxQ
      have hsp : Q.genericPoint ⤳ x := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxQ
        exact specializes_iff_mem_closure.mpr hxQ
      exact (hsp.map ι.continuous).mem_closed (PrimeDivisorUnion.isClosed_support E) hQE
    by_cases h12 : E₁ = E₂
    · subst h12
      exact hne (eq_of_mem_support_of_isSNC hsnc (hEG E₁ hE₁) hTG (fun h => hTs (h ▸ hE₁)) hι₁ hι₂
        ⟨x, hx₁, hx₂⟩)
    · exact hdisj E₁ hE₁ E₂ hE₂ h12 ⟨ι x, hmap Q₁ E₁ hι₁ hx₁, hmap Q₂ E₂ hι₂ hx₂⟩
  -- `K_T + Ψ` is `ℝ`-Cartier
  have hRC := isRCartier_add_of_isSmoothScheme hTsm KT (B := QDivisor.toRDivisor Ψ) Ψ.support
    (fun Q hQ => by
      rw [Finsupp.mem_support_iff] at hQ ⊢
      intro h0
      apply hQ
      change ((Ψ Q : ℚ) : ℝ) = 0
      rw [h0, Rat.cast_zero])
  -- the terminal inequality
  have hterm : ∀ (n : ℕ) (E : DivisorOver k (ι ≫ sY)) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy (ι ≫ sY) n (QDivisor.toRDivisor Ψ) E a → 1 < a := by
    intro n E a hE ha
    have hnn : n = nT := by
      have h := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans hnT
      exact_mod_cast h
    subst hnn
    by_cases hdim : n ≤ 1
    · exact absurd hE (not_isExceptional_of_topologicalKrullDim_le_one hnT hdim E)
    have h2 : 2 ≤ n := by omega
    have hPair : Mori.IsPair (ι ≫ sY) Ψ :=
      ⟨hTnv, n, KT, hKT, MMP.Fourfold.isQCartier_of_isSmoothScheme hTsm _⟩
    obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPair hKT E
    have hab := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha' ha
    have hle := discrep_le hE ha'
    have hSsnc : DivisorWithCoeffs.IsSNC (ι ≫ sY) (∑ E ∈ Ψ.support, Finsupp.single E (1 : ℤ)) :=
      (DivisorWithCoeffs.isSNC_iff_of_support_eq (support_sum_single Ψ.support).symm).mp hΨsnc
    have hformula := discrep_eq_of_isSNC (ι ≫ sY) hTnv hTsm h2 hKT Ψ.support subset_rfl hSsnc
      (fun Q hQ => (hcoeff Q (Finsupp.mem_support_iff.mp hQ)).2.le)
    have hpos := zero_lt_inf_snc_bound Ψ.support Ψ.coeff
      (fun Q hQ => (hcoeff Q (Finsupp.mem_support_iff.mp hQ)).2) (fun E F => E ≠ F)
      (fun E F => ((E.support : Set _) ∩ F.support).Nonempty)
      (fun Q₁ hQ₁ Q₂ hQ₂ hne hmeet => hnomeet Q₁ hQ₁ Q₂ hQ₂ hne hmeet)
    rw [← hformula] at hpos
    have h0 : (0 : EReal) < ((a' : ℝ) : EReal) := hpos.trans_le hle
    have : (0 : ℝ) < a' := by exact_mod_cast h0
    rw [hab]
    linarith
  refine ⟨hTsm, hΨ0, hΨsnc, inferInstance, inferInstance,
    ⟨hTnv, fun Q hQ => ?_, ⟨nT, KT, hKT, hRC⟩,
      fun n E a hE ha => (hterm n E a hE ha).le⟩, hterm⟩
  have hQ' : Ψ.coeff Q ≠ 0 := by
    intro h0
    apply hQ
    change ((Ψ Q : ℚ) : ℝ) = 0
    change Ψ Q = 0 at h0
    rw [h0, Rat.cast_zero]
  obtain ⟨h1, h2⟩ := hcoeff Q hQ'
  change (0 : ℝ) < ((Ψ Q : ℚ) : ℝ) ∧ ((Ψ Q : ℚ) : ℝ) < 1
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- If `M = m(K + B)` with `m > 0`, then `K + B = m⁻¹ M` as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_sum {X : Scheme.{u}} {K : Divisor X} {B : QDivisor X} {m : ℕ}
    (hm : 0 < m) {M : Divisor X}
    (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B)) :
    Divisor.toRDivisor K + QDivisor.toRDivisor B =
      ∑ _j : Fin 1, (1 / (m : ℝ)) • Divisor.toRDivisor M := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp at this
  have h' : (M.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by linear_combination this
  have h'' : (M.coeff Γ : ℝ) = m * (K.coeff Γ + B.coeff Γ) := by exact_mod_cast h'
  rw [Flips.coeff_sum_smul_toRDivisor, Fin.sum_univ_one, h'', DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
  field_simp

/-- If `K + B` is `ℚ`-Cartier, it is an `ℝ`-combination of Cartier divisors. -/
private theorem isCartierCombination_toRDivisor_add {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {K : Divisor X} {B : QDivisor X} (h : (Divisor.toQDivisor K + B).IsQCartier) :
    Flips.IsCartierCombination (Divisor.toRDivisor K + QDivisor.toRDivisor B) := by
  obtain ⟨m, hm, M, hM, hMc⟩ := h.exists_pos
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => M, fun _ => hMc, ?_⟩
  rw [toRDivisor_add_eq_sum hm hM]
  simp only [Flips.toRDivisor_eq_mapCoeffs]

/-- The discrepancy of a divisor over `X` which is not exceptional: it is the divisor of a prime
divisor `Γ` of `X`, its centre is the generic point of `Γ`, and its discrepancy is
`-coeff_Γ(Δ)`. -/
private theorem exists_eq_neg_coeff_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : DivisorOver k sX}
    (hD : ¬ D.IsExceptional) {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) :
    ∃ Γ : Mori.PrimeDivisor X, D.f D.E.genericPoint = Γ.genericPoint ∧ a = -Δ.coeff Γ := by
  obtain ⟨Γ, hΓ⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hΓ
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ha.isPair ha.2.1
    (DivisorOver.ofPrimeDivisor k hX Γ)
  have heq := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hΓ hc ha ha'
  exact ⟨Γ, hc, heq.trans (ha'.eq_neg_coeff_of_ofPrimeDivisor hX)⟩

/-- Over a plt pair, the discrepancy of an exceptional divisor exceeds `-1`. -/
private theorem neg_one_lt_of_isPltPair {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hplt : IsPltPair sX n K Δ) {E : DivisorOver k sX}
    (hE : E.IsExceptional) {a : ℚ} (ha : IsDiscrepancy sX n K Δ E a) : -1 < a := by
  have h : ((-1 : ℝ) : EReal) < ((a : ℝ) : EReal) := by
    simpa using hplt.2.trans_le (discrep_le hE ha)
  exact_mod_cast EReal.coe_lt_coe_iff.mp h

/-- **A plt pair is sub-lc.** If `(X, Δ)` is plt and every coefficient of `Δ` is at most one, all
log discrepancies over `(X, Δ)` are nonnegative: exceptional ones exceed `0` by plt, and those of
prime divisors of `X` are `1 - coeff ≥ 0`. -/
private theorem isSubLc_of_isPltPair {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hplt : IsPltPair sX n K Δ) (hΔ1 : ∀ P, Δ.coeff P ≤ 1) :
    IsSubLc sX n K (QDivisor.toRDivisor Δ) := by
  obtain ⟨hX, hK, hQC⟩ := hplt.1
  refine ⟨hX, hK, isCartierCombination_toRDivisor_add hQC, ?_⟩
  rintro F - b ⟨c, hc, rfl⟩
  obtain ⟨-, -, -, E', -, -, -, -, hv, -, -⟩ := id hc
  subst hv
  have hLD := isLogDiscrepancy_of_isDiscrepancy hc
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ⟨hX, n, K, hK, hQC⟩ hK
    E'.toDivisorOver
  have heq := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha' hLD
  rw [heq]
  by_cases hE : E'.toDivisorOver.IsExceptional
  · have : (-1 : ℝ) < a' := by exact_mod_cast neg_one_lt_of_isPltPair hplt hE ha'
    linarith
  · obtain ⟨Γ, -, hΓ⟩ := exists_eq_neg_coeff_of_not_isExceptional hX hE ha'
    have h1 := hΔ1 Γ
    have : (-1 : ℚ) ≤ a' := by rw [hΓ]; linarith
    have : (-1 : ℝ) ≤ a' := by exact_mod_cast this
    linarith

/-- Let `(X, S + B)` be a rational plt pair on a normal `ℚ`-factorial variety, with `S` a prime
divisor, `B ≥ 0`, `S` not a component of `B` and every coefficient of `B` less than one. Then there
is a log resolution `f : Y ⟶ X` and effective `ℚ`-divisors `Γ₀, E` on `Y` with no
common component, `E` exceptional, such that `K_Y + Γ₀ = f^*(K_X + S + B) + E`, the strict
transform `T` of `S` has coefficient one in `Γ₀` and all other coefficients are less than one, `T`
is smooth, and `Ψ₀ = (Γ₀ - T)|_T` is an effective snc divisor with `(T, Ψ₀)` real terminal. -/
@[mmp "lem_fourfold_terminal_restriction_resolution"]
public theorem exists_isLogResolution_isRealTerminalPair_restrictPrimeDivisor
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsQFactorial sX) (n : ℕ) (K : Divisor X) (S : Mori.PrimeDivisor X) (B : QDivisor X)
    (hB : 0 ≤ B) (hBS : B.coeff S = 0) (hB1 : ∀ P, B.coeff P < 1)
    (hplt : IsPltPair sX n K (Finsupp.single S 1 + B)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsLogResolution sX (Finsupp.single S 1 + B) f ∧
      ∃ (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (Γ₀ E : QDivisor Y)
        (T : Mori.PrimeDivisor Y),
        0 ≤ Γ₀ ∧ 0 ≤ E ∧ Γ₀ ⊓ E = 0 ∧
        (∀ P, E.coeff P ≠ 0 → (⟨Y, f, hY, hf, P⟩ : DivisorOver k sX).IsExceptional) ∧
        IsCrepantBoundary sX n K (Finsupp.single S 1 + B) f hY hf (Γ₀ - E) ∧
        f.base T.genericPoint = S.genericPoint ∧ Γ₀.coeff T = 1 ∧
        (∀ P, P ≠ T → Γ₀.coeff P < 1) ∧
        IsSmoothScheme (T.idealSheaf.subschemeι ≫ f ≫ sX) ∧
        0 ≤ (Γ₀ - Finsupp.single T 1).restrictPrimeDivisor T ∧
        ((Γ₀ - Finsupp.single T 1).restrictPrimeDivisor T).IsSNC
          (T.idealSheaf.subschemeι ≫ f ≫ sX) ∧
        haveI := T.integral
        ∃ (_ : IsLocallyNoetherian T.idealSheaf.subscheme) (_ : IsNormal T.idealSheaf.subscheme),
          IsRealTerminalPair (T.idealSheaf.subschemeι ≫ f ≫ sX)
            (QDivisor.toRDivisor ((Γ₀ - Finsupp.single T 1).restrictPrimeDivisor T)) := by
  classical
  set Δ : QDivisor X := Finsupp.single S 1 + B with hΔ
  obtain ⟨⟨hXnv, hK, hQC⟩, -⟩ := id hplt
  haveI : LocallyOfFiniteType sX := hXnv.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXnv.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  -- the coefficients of `Δ = S + B`
  have hΔc : ∀ P, Δ.coeff P = (if P = S then 1 else 0) + B.coeff P := by
    intro P
    simp [hΔ, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, eq_comm]
  have hB0 : ∀ P, 0 ≤ B.coeff P := fun P => hB P
  have hΔ0 : ∀ P, 0 ≤ Δ.coeff P := fun P => by
    rw [hΔc]; split_ifs <;> linarith [hB0 P]
  have hΔ1 : ∀ P, Δ.coeff P ≤ 1 := fun P => by
    rw [hΔc]; split_ifs with h
    · rw [h, hBS]; norm_num
    · linarith [hB1 P]
  have hΔlt : ∀ P, P ≠ S → Δ.coeff P < 1 := fun P hP => by
    rw [hΔc, if_neg hP]; linarith [hB1 P]
  have hΔS : Δ.coeff S = 1 := by rw [hΔc, if_pos rfl, hBS]; norm_num
  have hlc : IsSubLc sX n K (QDivisor.toRDivisor Δ) := isSubLc_of_isPltPair hplt hΔ1
  -- an `H`-projective log resolution with the pair condition
  obtain ⟨Y₀, f₀, hlog₀, hproj₀, hample₀⟩ :=
    exists_isLogResolution_isProjectiveMorphism_isAmple sX hXnv hX (QDivisor.toRDivisor Δ)
  obtain ⟨Y, f, hlog, hproj, hpair⟩ :=
    exists_isLogResolution_pairCondition hlc hlog₀ hproj₀ hample₀
  -- the smooth variety `Y`
  have hfb := hlog.isBirationalMorphism
  haveI : IsProper f := hlog.isProper
  obtain ⟨hY, -, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hXnv
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  haveI : Smooth (f ≫ sX) := hlog.isSmoothScheme.smooth
  haveI : IsDominant f := hfb.isDominant
  have hPair : Mori.IsPair sX Δ := ⟨hXnv, n, K, hK, hQC⟩
  -- the discrepancies `a(P, X, Δ)` of the prime divisors of `Y`
  let toX : Mori.PrimeDivisor Y → DivisorOver k sX := fun P => ⟨Y, f, hY, hfb, P⟩
  choose a ha using fun P => MMP.Positivity.IsPair.exists_isDiscrepancy hPair hK (toX P)
  have hnex : ∀ P, ¬ (toX P).IsExceptional →
      ∃ Γ : Mori.PrimeDivisor X, f P.genericPoint = Γ.genericPoint ∧ a P = -Δ.coeff Γ :=
    fun P hP => exists_eq_neg_coeff_of_not_isExceptional hXnv hP (ha P)
  have hexc : ∀ P, (toX P).IsExceptional ↔ 2 ≤ Order.coheight (f P.genericPoint) :=
    fun P => MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hXnv (toX P)
  -- the configuration of `f`
  obtain ⟨sC, hsC, hsncC⟩ := exists_finset_cfg sX (QDivisor.toRDivisor Δ) hlog
  have hmemsupp : ∀ Γ : Mori.PrimeDivisor X, Δ.coeff Γ ≠ 0 →
      Γ.genericPoint ∈ DivisorWithCoeffs.supp (QDivisor.toRDivisor Δ) := fun Γ hΓ =>
    DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ, by
      rw [QDivisor.coeff_toRDivisor]; exact_mod_cast hΓ,
      Positivity.PrimeDivisor.genericPoint_mem_support' Γ⟩
  have hcfg : ∀ P : Mori.PrimeDivisor Y, P ∈ sC ↔
      P.genericPoint ∈ (Mori.exceptionalSet f : Set Y) ∨
        f P.genericPoint ∈ (DivisorWithCoeffs.supp (QDivisor.toRDivisor Δ) : Set X) := by
    intro P
    rw [← support_subset_iUnion_iff, hsC, support_subset_iff P (cfg _ f).isClosed]
    simp only [cfg, Closeds.coe_sup, Set.mem_union, Closeds.coe_preimage, Set.mem_preimage]
  have ha0 : ∀ P, P ∉ sC → a P = 0 := by
    intro P hP
    rw [hcfg, not_or] at hP
    obtain ⟨hPex, hPD⟩ := hP
    have hb : f P.genericPoint ∈ biregularLocus f := not_not.mp hPex
    have hco : Order.coheight (f P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb, P.coheight_genericPoint]
    have hne : ¬ (toX P).IsExceptional := by
      rw [hexc, hco]; decide
    obtain ⟨Γ, hΓ, haΓ⟩ := hnex P hne
    rw [haΓ]
    have : Δ.coeff Γ = 0 := by
      by_contra h0
      exact hPD (hΓ ▸ hmemsupp Γ h0)
    rw [this, neg_zero]
  -- the strict transform `T` of `S`
  obtain ⟨T, hTS, -⟩ := exists_primeDivisor_isIso_stalkMap f hfb S
  have hTex : ¬ (toX T).IsExceptional := by
    rw [hexc]
    change ¬ 2 ≤ Order.coheight (f T.genericPoint)
    rw [hTS, S.coheight_genericPoint]
    decide
  have haT : a T = -1 := by
    obtain ⟨Γ, hΓ, h⟩ := hnex T hTex
    have hΓS : Γ = S := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hΓ.symm.trans hTS)
    rw [h, hΓS, hΔS]
  have hTuniq : ∀ P : Mori.PrimeDivisor Y, f P.genericPoint = S.genericPoint → P = T := by
    intro P hP
    have hbij := hfb.functionFieldMap_bijective
    have := S.isDiscreteValuationRing_localRing
    haveI : ValuationRing (X.presheaf.stalk (f P.genericPoint)) := by rw [hP]; infer_instance
    haveI : ValuationRing (X.presheaf.stalk (f T.genericPoint)) := by rw [hTS]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij P.genericPoint
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij T.genericPoint
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Positivity.eq_of_isIso_stalkMap f hbij (hTS.trans hP.symm))
  have hagt : ∀ P, P ≠ T → -1 < a P := by
    intro P hPT
    by_cases hPe : (toX P).IsExceptional
    · exact neg_one_lt_of_isPltPair hplt hPe (ha P)
    · obtain ⟨Γ, hΓ, h⟩ := hnex P hPe
      have hΓS : Γ ≠ S := fun h' => hPT (hTuniq P (hΓ.trans (by rw [h'])))
      rw [h]
      linarith [hΔlt Γ hΓS]
  have hTsC : T ∈ sC := (hcfg T).mpr (Or.inr (by
    rw [hTS]; exact hmemsupp S (by rw [hΔS]; norm_num)))
  -- the log discrepancies `1 + a(P, X, Δ)`
  have hLD : ∀ P, IsLD sX n K (QDivisor.toRDivisor Δ) f P (1 + a P) := by
    intro P
    have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (ha P)
      (inferInstance : IsProper f)
    have h2 := isDiscrepancy_of_isLogDiscrepancy hXnv hK hlc.2.2.1
      (E := Flips.ProperDivisorOver.mk (toX P) (inferInstance : IsProper f)) h1
    exact ⟨hY, hfb, inferInstance, _, h2, by ring⟩
  -- `Γ₀` and `E`
  set c : Mori.PrimeDivisor Y → ℚ := fun P => -a P with hcdef
  have hc0 : ∀ P, P ∉ sC → c P = 0 := fun P hP => by simp [hcdef, ha0 P hP]
  let C : QDivisor Y := Finsupp.onFinset sC c fun P hP => by_contra fun h => hP (hc0 P h)
  have hC : ∀ P, C P = c P := fun P => Finsupp.onFinset_apply
  set Γ₀ : QDivisor Y := C⁺ with hΓ₀def
  set E₀ : QDivisor Y := C⁻ with hE₀def
  have hΓ₀ : ∀ P, Γ₀ P = max (c P) 0 := fun P => by
    rw [hΓ₀def, posPart_def, Finsupp.sup_apply, hC]; rfl
  have hE₀ : ∀ P, E₀ P = max (-c P) 0 := fun P => by
    rw [hE₀def, negPart_def, Finsupp.sup_apply, Finsupp.neg_apply, hC]; rfl
  -- the restricted part of `Γ₀`
  set s := sC.filter fun P => P ≠ T ∧ 0 < c P
  have hTs : T ∉ s := fun h => (Finset.mem_filter.mp h).2.1 rfl
  have hrepr : Γ₀ - Finsupp.single T 1 = ∑ P ∈ s, Finsupp.single P (c P) := by
    ext P
    rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, hΓ₀,
      Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    by_cases hPT : P = T
    · subst hPT
      have : c P = 1 := by simp [hcdef, haT]
      rw [if_pos rfl, if_neg hTs, this]
      norm_num
    · rw [if_neg (Ne.symm hPT), sub_zero]
      by_cases hcP : 0 < c P
      · have hPs : P ∈ s := by
          refine Finset.mem_filter.mpr ⟨?_, hPT, hcP⟩
          by_contra h
          rw [hc0 P h] at hcP
          exact lt_irrefl _ hcP
        rw [if_pos hPs, max_eq_left hcP.le]
      · have hPs : P ∉ s := fun h => hcP (Finset.mem_filter.mp h).2.2
        rw [if_neg hPs, max_eq_right (not_lt.mp hcP)]
  have hsnc' : DivisorWithCoeffs.IsSNC (f ≫ sX)
      (Finsupp.single T (1 : ℤ) + ∑ P ∈ s, Finsupp.single P (1 : ℤ)) := by
    refine hsncC.of_support_subset ?_
    rw [support_reducedDivisorOf]
    intro P hP
    rcases Finset.mem_union.mp (Finsupp.support_add hP) with h | h
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; exact hTsC
    · obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum h)
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hPQ)]
      exact (Finset.mem_filter.mp hQ).1
  have hβ : ∀ P ∈ s, 0 < c P ∧ c P < 1 := by
    intro P hP
    obtain ⟨-, hPT, hcP⟩ := Finset.mem_filter.mp hP
    refine ⟨hcP, ?_⟩
    have := hagt P hPT
    simp only [hcdef]
    linarith
  have hdisj : ∀ P ∈ s, ∀ Q ∈ s, P ≠ Q → ¬ ((P.support : Set Y) ∩ Q.support).Nonempty := by
    intro P hP Q hQ hPQ hmeet
    obtain ⟨hPC, hPT, hcP⟩ := Finset.mem_filter.mp hP
    obtain ⟨hQC, hQT, hcQ⟩ := Finset.mem_filter.mp hQ
    have hPc : (P.support : Set Y) ⊆ cfg (QDivisor.toRDivisor Δ) f := by
      rw [← hsC]; exact support_subset_iUnion_iff.mpr hPC
    have hQc : (Q.support : Set Y) ⊆ cfg (QDivisor.toRDivisor Δ) f := by
      rw [← hsC]; exact support_subset_iUnion_iff.mpr hQC
    have h1 : (-1 : ℝ) < a P := by exact_mod_cast hagt P hPT
    have h2 : (-1 : ℝ) < a Q := by exact_mod_cast hagt Q hQT
    have h3 : (a P : ℝ) < 0 := by exact_mod_cast neg_pos.mp hcP
    have h4 : (a Q : ℝ) < 0 := by exact_mod_cast neg_pos.mp hcQ
    linarith [hpair P Q hPQ hPc hQc hmeet _ _ (hLD P) (hLD Q) (by linarith) (by linarith)]
  obtain ⟨hTsm, hΨ0, hΨsnc, hΨterm⟩ :=
    isRealTerminalPair_restrictPrimeDivisor (f ≫ sX) T s hTs hsnc' c hβ hdisj
  refine ⟨Y, f, ⟨hlog, hproj⟩, hY, hfb, Γ₀, E₀, T, posPart_nonneg C, negPart_nonneg C,
    posPart_inf_negPart_eq_zero C, ?_, ?_, hTS, ?_, ?_, hTsm, ?_, ?_, ?_⟩
  · intro P hP
    change E₀ P ≠ 0 at hP
    rw [hE₀] at hP
    have hneg : 0 < -c P := by
      by_contra h
      exact hP (max_eq_right (not_lt.mp h))
    by_contra hPe
    obtain ⟨Γ, -, h⟩ := hnex P hPe
    have : 0 < a P := by simpa [hcdef] using hneg
    rw [h] at this
    linarith [hΔ0 Γ]
  · intro F
    change IsDiscrepancy sX n K Δ (toX F) (-(Γ₀ - E₀).coeff F)
    rw [hΓ₀def, hE₀def, posPart_sub_negPart, DivisorWithCoeffs.coeff_apply, hC]
    simpa [hcdef] using ha F
  · change Γ₀ T = 1
    rw [hΓ₀]
    simp [hcdef, haT]
  · intro P hPT
    change Γ₀ P < 1
    rw [hΓ₀]
    refine max_lt ?_ one_pos
    have := hagt P hPT
    simp only [hcdef]
    linarith
  · rwa [hrepr]
  · rwa [hrepr]
  · rwa [hrepr]

end MMP.Fourfold
